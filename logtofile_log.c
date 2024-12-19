/*-------------------------------------------------------------------------
 *
 * logtofile_log.c
 *      Functions to write audit logs to file
 *
 * Copyright (c) 2020-2024, Francisco Miguel Biete Banon
 *
 * This code is released under the PostgreSQL licence, as given at
 *  http://www.postgresql.org/about/licence/
 *-------------------------------------------------------------------------
 */
#include "logtofile_log.h"

#include "logtofile_autoclose.h"
#include "logtofile_guc.h"
#include "logtofile_shmem.h"
#include "logtofile_vars.h"

#include <access/xact.h>
#include <lib/stringinfo.h>
#include <libpq/libpq-be.h>
#include <miscadmin.h>
#include <pgtime.h>
#include <port/atomics.h>
#include <postmaster/syslogger.h>
#include <storage/fd.h>
#include <storage/ipc.h>
#include <storage/lwlock.h>
#include <storage/pg_shmem.h>
#include <storage/proc.h>
#include <tcop/tcopprot.h>
#include <utils/guc.h>
#include <utils/json.h>
#include <utils/ps_status.h>

#include <pthread.h>
#include <time.h>
#include <sys/stat.h>

/* Defines */
#define PGAUDIT_PREFIX_LINE "AUDIT: "
#define PGAUDIT_PREFIX_LINE_LENGTH sizeof(PGAUDIT_PREFIX_LINE) - 1
#define FORMATTED_TS_LEN 128

/*
 * We really want line-buffered mode for logfile output, but Windows does
 * not have it, and interprets _IOLBF as _IOFBF (bozos).  So use _IONBF
 * instead on Windows.
 */
#ifdef WIN32
#define LBF_MODE _IONBF
#else
#define LBF_MODE _IOLBF
#endif

/* deparsed audit record */
struct audit_record
{
	char *type;	/* OBJECT or SESSION */
	char *statement_id;
	char *substatement_id;
	char *class;
	char *command_tag;
	char *object_type;
	char *object_name;
	char *statement;
	char *parameters;
	char *rows;
};

/* variables to use only in this unit */
static char formatted_log_time[FORMATTED_TS_LEN];
static char formatted_start_time[FORMATTED_TS_LEN];
static char filename_in_use[MAXPGPATH];
static int autoclose_thread_status_debug = 0; // 0: new proc, 1: th running, 2: th running sleep used, 3: th closed

/* forward declaration private functions */
void pgauditlogtofile_close_file(void);
char *pgauditlogtofile_unquote(char *s, char **dest);
void pgauditlogtofile_parse_csv(struct audit_record*, char *);
void pgauditlogtofile_append_csv(StringInfo buf, char * const key, const char *val, bool escape_val, bool first, bool last);
void pgauditlogtofile_append_json(StringInfo buf, char * const key, const char *val, bool escape_val, bool first, bool last);
void pgauditlogtofile_create_audit_line(StringInfo buf, const ErrorData *edata, int exclude_nchars);
void pgauditlogtofile_format_log_time(void);
void pgauditlogtofile_format_start_time(void);
bool pgauditlogtofile_is_enabled(void);
bool pgauditlogtofile_is_open_file(void);
bool pgauditlogtofile_is_prefixed(const char *msg);
bool pgauditlogtofile_open_file(void);
bool pgauditlogtofile_record_audit(const ErrorData *edata, int exclude_nchars);
bool pgauditlogtofile_write_audit(const ErrorData *edata, int exclude_nchars);

/* public methods */

/**
 * @brief Hook to emit_log - write the record to the audit or send it to the default logger
 * @param edata: error data
 * @return void
 */
void PgAuditLogToFile_emit_log(ErrorData *edata)
{
  int exclude_nchars = -1;

  if (pgauditlogtofile_is_enabled())
  {
    // printf("ENABLE PRINTF\n");
    if (pg_strncasecmp(edata->message, PGAUDIT_PREFIX_LINE, PGAUDIT_PREFIX_LINE_LENGTH) == 0)
    {
      exclude_nchars = PGAUDIT_PREFIX_LINE_LENGTH;
      edata->output_to_server = false;
    }
    else if (pgauditlogtofile_is_prefixed(edata->message))
    {
      edata->output_to_server = false;
      exclude_nchars = 0;
    }

    // Scenarios not contemplated above will be ignored
    if (exclude_nchars >= 0)
    {
      if (!pgauditlogtofile_record_audit(edata, exclude_nchars))
      {
        // ERROR: failed to record in audit, record in server log
        edata->output_to_server = true;
      }
    }
  }

  if (pgaudit_ltf_prev_emit_log_hook)
    pgaudit_ltf_prev_emit_log_hook(edata);
}

/**
 * @brief Checks if pgauditlogtofile is completely started and configured
 * @param void
 * @return bool - true if pgauditlogtofile is enabled
 */
bool pgauditlogtofile_is_enabled(void)
{
  if (UsedShmemSegAddr == NULL)
    return false;

  if (!pgaudit_ltf_shm || !pg_atomic_unlocked_test_flag(&pgaudit_ltf_flag_shutdown) ||
      guc_pgaudit_ltf_log_directory == NULL || guc_pgaudit_ltf_log_filename == NULL ||
      strlen(guc_pgaudit_ltf_log_directory) == 0 || strlen(guc_pgaudit_ltf_log_filename) == 0)
    return false;

  return true;
}

/**
 * @brief Records an audit log
 * @param edata: error data
 * @param exclude_nchars: number of characters to exclude from the message
 * @return bool - true if the record was written
 */
bool pgauditlogtofile_record_audit(const ErrorData *edata, int exclude_nchars)
{
  bool rc;

  ereport(DEBUG5, (errmsg("pgauditlogtofile record audit in %s (shm %s)",
                          filename_in_use, pgaudit_ltf_shm->filename)));
  /* do we need to rotate? */
  if (strlen(pgaudit_ltf_shm->filename) > 0 && strcmp(filename_in_use, pgaudit_ltf_shm->filename) != 0)
  {
    ereport(DEBUG3, (
                        errmsg("pgauditlogtofile record audit file handler requires reopening - shm_filename %s filename_in_use %s",
                               pgaudit_ltf_shm->filename, filename_in_use)));
    pgauditlogtofile_close_file();
  }

  if (!pgauditlogtofile_is_open_file() && !pgauditlogtofile_open_file())
    return false;

  rc = pgauditlogtofile_write_audit(edata, exclude_nchars);
  pgaudit_ltf_autoclose_active_ts = GetCurrentTimestamp();

  if (guc_pgaudit_ltf_auto_close_minutes > 0)
  {
    // only 1 auto-close thread
    if (pg_atomic_test_set_flag(&pgaudit_ltf_autoclose_flag_thread))
    {
      ereport(DEBUG3, (errmsg("pgauditlogtofile record_audit - create autoclose thread")));
      autoclose_thread_status_debug = 1;
      pthread_attr_init(&pgaudit_ltf_autoclose_thread_attr);
      pthread_attr_setdetachstate(&pgaudit_ltf_autoclose_thread_attr, PTHREAD_CREATE_DETACHED);
      pthread_create(&pgaudit_ltf_autoclose_thread, &pgaudit_ltf_autoclose_thread_attr, PgAuditLogToFile_autoclose_run, &autoclose_thread_status_debug);
    }
  }

  return rc;
}

/**
 * @brief Close the audit log file
 * @param void
 * @return void
 */
void pgauditlogtofile_close_file(void)
{
  if (pgaudit_ltf_file_handler)
  {
    fclose(pgaudit_ltf_file_handler);
    pgaudit_ltf_file_handler = NULL;
  }
}

/**
 * @brief Checks if the audit log file is open
 * @param void
 * @return bool - true if the file is open
 */
bool pgauditlogtofile_is_open_file(void)
{
  if (pgaudit_ltf_file_handler)
    return true;
  else
    return false;
}

/**
 * @brief Checks if a message starts with one of our intercept prefixes
 * @param msg: message
 * @return bool - true if the message starts with a prefix
 */
bool pgauditlogtofile_is_prefixed(const char *msg)
{
  bool found = false;
  size_t i;

  if (guc_pgaudit_ltf_log_connections)
  {
    for (i = 0; !found && i < pgaudit_ltf_shm->num_prefixes_connection; i++)
    {
      found = pg_strncasecmp(msg, pgaudit_ltf_shm->prefixes_connection[i]->prefix, pgaudit_ltf_shm->prefixes_connection[i]->length) == 0;
    }
  }

  if (!found && guc_pgaudit_ltf_log_disconnections)
  {
    for (i = 0; !found && i < pgaudit_ltf_shm->num_prefixes_disconnection; i++)
    {
      found = pg_strncasecmp(msg, pgaudit_ltf_shm->prefixes_disconnection[i]->prefix, pgaudit_ltf_shm->prefixes_disconnection[i]->length) == 0;
    }
  }

  return found;
}

/**
 * @brief Open the audit log file
 * @param void
 * @return bool - true if the file was opened
 */
bool pgauditlogtofile_open_file(void)
{
  mode_t oumask;
  bool opened = false;

  // if the filename is empty, we short-circuit
  if (strlen(pgaudit_ltf_shm->filename) == 0)
    return opened;

  /* Create spool directory if not present; ignore errors */
  (void)MakePGDirectory(guc_pgaudit_ltf_log_directory);

  /*
   * Note we do not let Log_file_mode disable IWUSR, since we certainly want
   * to be able to write the files ourselves.
   */
  oumask = umask(
      (mode_t)((~(Log_file_mode | S_IWUSR)) & (S_IRWXU | S_IRWXG | S_IRWXO)));
  pgaudit_ltf_file_handler = fopen(pgaudit_ltf_shm->filename, "a");
  umask(oumask);

  if (pgaudit_ltf_file_handler)
  {
    opened = true;
    /* 128K buffer and flush on demand or when full -> attempt to use only 1 IO operation per record */
    setvbuf(pgaudit_ltf_file_handler, NULL, _IOFBF, 131072);
#ifdef WIN32
    /* use CRLF line endings on Windows */
    _setmode(_fileno(file_handler), _O_TEXT);
#endif
    // File open, we update the filename we are using
    strcpy(filename_in_use, pgaudit_ltf_shm->filename);
  }
  else
  {
    int save_errno = errno;
    ereport(ERROR,
            (errcode_for_file_access(),
             errmsg("could not open log file \"%s\": %m", pgaudit_ltf_shm->filename)));
    errno = save_errno;
  }

  return opened;
}

/**
 * @brief Writes an audit record in the audit log file
 * @param edata: error data
 * @param exclude_nchars: number of characters to exclude from the message
 */
bool pgauditlogtofile_write_audit(const ErrorData *edata, int exclude_nchars)
{
  StringInfoData buf;
  int rc = 0;

  initStringInfo(&buf);
  /* create the log line */
  pgauditlogtofile_create_audit_line(&buf, edata, exclude_nchars);

  // auto-close maybe has closed the file
  if (!pgaudit_ltf_file_handler)
    pgauditlogtofile_open_file();

  if (pgaudit_ltf_file_handler)
  {
    fseek(pgaudit_ltf_file_handler, 0L, SEEK_END);
    rc = fwrite(buf.data, 1, buf.len, pgaudit_ltf_file_handler);
    pfree(buf.data);
    fflush(pgaudit_ltf_file_handler);
  }

  if (rc != buf.len)
  {
    int save_errno = errno;
    ereport(ERROR,
            (errcode_for_file_access(),
             errmsg("could not write audit log file \"%s\": %m", filename_in_use)));
    pgauditlogtofile_close_file();
    errno = save_errno;
  }

  return rc == buf.len;
}

/**
 * @brief removes quotes from a possibly quoted CSV entry
 * @param s: the input string (will be overwritten)
 * @param dest: address of the result string
 * @return char* - the position at the end of the parsed string
 */
char *pgauditlogtofile_unquote(char *s, char **dest)
{
	char *p = s;
	bool quoted = false, done = false;

	*dest = s;

	while (!done)
		switch (*s)
		{
			case '"':
				s++;

				if (!quoted)
				{
					quoted = true;
					break;
				}

				if (*s == '"')
					*p++ = *s++;
				else
					quoted = false;

				break;
			case '\0':
				done = true;

				break;
			case ',':
				if (!quoted)
				{
					*p = '\0';
					done = true;
					break;
				}
				/* fallthrough */
			default:
				*p++ = *s++;
		}

	return s;
}

/**
 * @brief parses a CSV audit log entry into its components
 * @param target: the record to fill
 * @param csv: the CSV log line (will be overwritten)
 */
void pgauditlogtofile_parse_csv(struct audit_record* target, char *csv)
{
	/* type */
	target->type = csv;
	for (; *csv != ','; ++csv)
		;
	*csv = '\0';

	/* statement_id */
	target->statement_id = ++csv;
	for (; *csv != ','; ++csv)
		;
	*csv = '\0';

	/* substatement_id */
	target->substatement_id = ++csv;
	for (; *csv != ','; ++csv)
		;
	*csv = '\0';

	/* class */
	target->class = ++csv;
	for (; *csv != ','; ++csv)
		;
	*csv = '\0';

	/* command_tag */
	target->command_tag = ++csv;
	for (; *csv != ','; ++csv)
		;
	*csv = '\0';

	/* object_type */
	target->object_type = ++csv;
	for (; *csv != ','; ++csv)
		;
	*csv = '\0';

	/* object_name */
	csv = pgauditlogtofile_unquote(++csv, &(target->object_name));

	/* statement */
	csv = pgauditlogtofile_unquote(++csv, &(target->statement));

	/* parameters */
	csv = pgauditlogtofile_unquote(++csv, &(target->parameters));

	target->rows = NULL;
	if (*(++csv) != '\0')
		target->rows = csv;
}

/**
 * @brief Appends a value to a CSV log line
 * @param buf: buffer to write the formatted line
 * @param key: name of the column to add (ignored)
 * @param val: a string value
 * @param escape_val: should the value be escaped? (ignored)
 * @param first: is this the first column? (ignored)
 * @param last: is this the last column?
 */
void pgauditlogtofile_append_csv(StringInfo buf, char * const key, const char *val, bool escape_val, bool first, bool last)
{
	appendStringInfoString(buf, val);
	if (last)
		appendStringInfoChar(buf, '\n');
	else
		appendStringInfoChar(buf, ',');
}

/**
 * @brief Appends a value to a JSON log line
 * @param buf: buffer to write the formatted line
 * @param key: name of the column to add
 * @param val: a string value
 * @param escape_val: should the value be escaped?
 * @param first: is this the first column?
 * @param last: is this the last column?
 */
void pgauditlogtofile_append_json(StringInfo buf, char * const key, const char *val, bool escape_val, bool first, bool last)
{
	/* don't write empty values */
	if (val == NULL || val[0] == '\0')
		return;

	if (first)
		appendStringInfoChar(buf, '{');
	escape_json(buf, key);
	appendStringInfoChar(buf, ':');
	if (escape_val)
		escape_json(buf, val);
	else
		appendStringInfoString(buf, val);
	if (last)
		appendStringInfoString(buf, "}\n");
    else
		appendStringInfoChar(buf, ',');
}

/**
 * @brief Formats an audit log line
 * @param buf: buffer to write the formatted line
 * @param edata: error data
 * @param exclude_nchars: number of characters to exclude from the message
 * @return void
 */
void pgauditlogtofile_create_audit_line(StringInfo buf, const ErrorData *edata, int exclude_nchars)
{
  /* static counter for line numbers */
  static long log_line_number = 0;

  /* has counter been reset in current process? */
  static int log_my_pid = 0;

  /* log function */
  void (*write_to_log)(StringInfo, char * const, const char *, bool, bool, bool) =
    guc_pgaudit_ltf_log_json ? &pgauditlogtofile_append_json : pgauditlogtofile_append_csv;

  /* for composing log entries */
  StringInfoData data;

  /*
   * This is one of the few places where we'd rather not inherit a static
   * variable's value from the postmaster.  But since we will, reset it when
   * MyProcPid changes.
   */
  if (log_my_pid != MyProcPid)
  {
    /* new session */
    log_line_number = 0;
    log_my_pid = MyProcPid;
    /* start session timestamp */
    pgauditlogtofile_format_start_time();
  }
  log_line_number++;

  /* timestamp with milliseconds */
  pgauditlogtofile_format_log_time();
  (*write_to_log)(buf, "log time", formatted_log_time, true, true, false);

  /* username */
  if (MyProcPort && MyProcPort->user_name)
    (*write_to_log)(buf, "user", MyProcPort->user_name, true, false, false);
  else
    (*write_to_log)(buf, "user", "", false, false, false);

  /* database name */
  if (MyProcPort && MyProcPort->database_name)
    (*write_to_log)(buf, "database", MyProcPort->database_name, true, false, false);
  else
    (*write_to_log)(buf, "database", "", false, false, false);

  /* Process id  */
  initStringInfo(&data);
  appendStringInfo(&data, "%d", log_my_pid);
  (*write_to_log)(buf, "process ID", data.data, false, false, false);

  /* Remote host and port */
  resetStringInfo(&data);
  if (MyProcPort && MyProcPort->remote_host)
  {
    appendStringInfoString(&data, MyProcPort->remote_host);
    if (MyProcPort->remote_port && MyProcPort->remote_port[0] != '\0')
    {
      appendStringInfoChar(&data, ':');
      appendStringInfoString(&data, MyProcPort->remote_port);
    }
  }
  (*write_to_log)(buf, "host", data.data, ((data.data)[0] != '\0'), false, false);

  /* session id - hex representation of start time . session process id */
  resetStringInfo(&data);
  appendStringInfo(&data, "%lx.%x", (long)MyStartTime, log_my_pid);
  (*write_to_log)(buf, "session id", data.data, true, false, false);

  /* Line number */
  resetStringInfo(&data);
  appendStringInfo(&data, "%ld", log_line_number);
  (*write_to_log)(buf, "line number", data.data, false, false, false);

  /* PS display */
  resetStringInfo(&data);
  if (MyProcPort)
  {
    const char *psdisp;
    int displen;

    psdisp = get_ps_display(&displen);
    appendBinaryStringInfo(&data, psdisp, displen);
  }
  (*write_to_log)(buf, "ps display", data.data, ((data.data)[0] != '\0'), false, false);

  /* session start timestamp */
  (*write_to_log)(buf, "session start timestamp", formatted_start_time, true, false, false);

  /* Virtual transaction id */
  /* keep VXID format in sync with lockfuncs.c */
  resetStringInfo(&data);
#if (PG_VERSION_NUM >= 170000)
  if (MyProc != NULL && MyProc->vxid.procNumber != INVALID_PROC_NUMBER)
    appendStringInfo(&data, "%d/%u", MyProc->vxid.procNumber, MyProc->vxid.lxid);
#else
  if (MyProc != NULL && MyProc->backendId != InvalidBackendId)
    appendStringInfo(&data, "%d/%u", MyProc->backendId, MyProc->lxid);
#endif
  (*write_to_log)(buf, "vxid", data.data, true, false, false);

  /* Transaction id */
  resetStringInfo(&data);
  appendStringInfo(&data, "%u", GetTopTransactionIdIfAny());
  (*write_to_log)(buf, "xid", data.data, false, false, false);

  /* SQL state code */
  (*write_to_log)(buf, "sqlstate", unpack_sql_state(edata->sqlerrcode), true, false, false);

  /* errmessage - PGAUDIT formatted text, +7 exclude "AUDIT: " prefix */
  if (guc_pgaudit_ltf_log_json)
  {
    /* parse the audit log line and write it as JSON */
    struct audit_record rec;

    pgauditlogtofile_parse_csv(&rec, edata->message + exclude_nchars);
    (*write_to_log)(buf, "audit mode", rec.type, true, false, false);
    (*write_to_log)(buf, "statement ID", rec.statement_id, false, false, false);
    (*write_to_log)(buf, "substatement ID", rec.substatement_id, false, false, false);
    (*write_to_log)(buf, "class", rec.class, true, false, false);
    (*write_to_log)(buf, "command tag", rec.command_tag, true, false, false);
    (*write_to_log)(buf, "object type", rec.object_type, true, false, false);
    (*write_to_log)(buf, "object name", rec.object_name, true, false, false);
    (*write_to_log)(buf, "statement", rec.statement, true, false, false);
    (*write_to_log)(buf, "parameters", rec.parameters, true, false, false);
    if (rec.rows != NULL)
      (*write_to_log)(buf, "rows", rec.rows, false, false, false);
  }
  else
    (*write_to_log)(buf, "audit message", edata->message + exclude_nchars, true, false, false);

  /* errdetail or errdetail_log */
  if (edata->detail_log)
    (*write_to_log)(buf, "detail", edata->detail_log, true, false, false);
  else if (edata->detail)
    (*write_to_log)(buf, "detail", edata->detail, true, false, false);
  else
    (*write_to_log)(buf, "detail", "", false, false, false);

  /* errhint */
  if (edata->hint)
    (*write_to_log)(buf, "hint", edata->detail, true, false, false);
  else
    (*write_to_log)(buf, "hint", "", false, false, false);

  /* internal query */
  if (edata->internalquery)
    (*write_to_log)(buf, "internal query", edata->internalquery, true, false, false);
  else
    (*write_to_log)(buf, "internal query", "", false, false, false);

  /* if printed internal query, print internal pos too */
  resetStringInfo(&data);
  if (edata->internalpos > 0 && edata->internalquery != NULL)
    appendStringInfo(&data, "%d", edata->internalpos);
  (*write_to_log)(buf, "internal position", data.data, false, false, false);

  /* errcontext */
  if (edata->context)
    (*write_to_log)(buf, "error context", edata->context, true, false, false);
  else
    (*write_to_log)(buf, "error context", "", false, false, false);

  /* user query --- only reported if not disabled by the caller */
  if (debug_query_string != NULL && !edata->hide_stmt)
  {
    resetStringInfo(&data);
    (*write_to_log)(buf, "query", debug_query_string, true, false, false);
    if (edata->cursorpos > 0)
      appendStringInfo(&data, "%d", edata->cursorpos);
    (*write_to_log)(buf, "cursor position", data.data, false, false, false);
  }
  else
  {
    (*write_to_log)(buf, "query", "", false, false, false);
    (*write_to_log)(buf, "cursor position", "", false, false, false);
  }

  /* file error location */
  if (Log_error_verbosity >= PGERROR_VERBOSE)
  {
    resetStringInfo(&data);
    if (edata->funcname && edata->filename)
      appendStringInfo(&data, "%s, %s:%d", edata->funcname, edata->filename,
                       edata->lineno);
    else if (edata->filename)
      appendStringInfo(&data, "%s:%d", edata->filename, edata->lineno);
    (*write_to_log)(buf, "error location", data.data, true, false, false);
  }
  else
    (*write_to_log)(buf, "error location", "", false, false, false);

  /* application name */
  if (application_name)
    (*write_to_log)(buf, "application name", application_name, true, false, true);
  else
    (*write_to_log)(buf, "application name", "", false, false, true);
}

/**
 * @brief Formats the session start time
 * @param void
 * @return void
 */
void pgauditlogtofile_format_start_time(void)
{
  /*
   * Note: we expect that guc.c will ensure that log_timezone is set up (at
   * least with a minimal GMT value) before Log_line_prefix can become
   * nonempty or CSV mode can be selected.
   */
  pg_strftime(formatted_start_time, FORMATTED_TS_LEN, "%Y-%m-%d %H:%M:%S %Z",
              pg_localtime((pg_time_t *)&MyStartTime, log_timezone));
}

/**
 * @brief Formats the record time
 * @param void
 * @return void
 */
void pgauditlogtofile_format_log_time(void)
{
  struct timeval tv;
  char msbuf[5];

  gettimeofday(&tv, NULL);

  /*
   * Note: we expect that guc.c will ensure that log_timezone is set up (at
   * least with a minimal GMT value) before Log_line_prefix can become
   * nonempty or CSV mode can be selected.
   */
  pg_strftime(formatted_log_time, FORMATTED_TS_LEN,
              /* leave room for milliseconds... */
              "%Y-%m-%d %H:%M:%S     %Z",
              pg_localtime((pg_time_t *)&(tv.tv_sec), log_timezone));

  /* 'paste' milliseconds into place... */
  sprintf(msbuf, ".%03d", (int)(tv.tv_usec / 1000));
  memcpy(formatted_log_time + 19, msbuf, 4);
}
