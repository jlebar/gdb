/* MI Command Set - MI parser.

   Copyright (C) 2000, 2001, 2002, 2007, 2008, 2009, 2010, 2011
   Free Software Foundation, Inc.

   Contributed by Cygnus Solutions (a Red Hat company).

   This file is part of GDB.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#include "defs.h"
#include "mi-cmds.h"
#include "mi-parse.h"
#include "charset.h"

#include <ctype.h>
#include "gdb_string.h"

/* Like parse_escape, but leave the results as a host char, not a
   target char.  */

static int
mi_parse_escape (char **string_ptr)
{
  int c = *(*string_ptr)++;

  switch (c)
    {
      case '\n':
	return -2;
      case 0:
	(*string_ptr)--;
	return 0;

      case '0':
      case '1':
      case '2':
      case '3':
      case '4':
      case '5':
      case '6':
      case '7':
	{
	  int i = host_hex_value (c);
	  int count = 0;

	  while (++count < 3)
	    {
	      c = (**string_ptr);
	      if (isdigit (c) && c != '8' && c != '9')
		{
		  (*string_ptr)++;
		  i *= 8;
		  i += host_hex_value (c);
		}
	      else
		{
		  break;
		}
	    }
	  return i;
	}

    case 'a':
      c = '\a';
      break;
    case 'b':
      c = '\b';
      break;
    case 'f':
      c = '\f';
      break;
    case 'n':
      c = '\n';
      break;
    case 'r':
      c = '\r';
      break;
    case 't':
      c = '\t';
      break;
    case 'v':
      c = '\v';
      break;

    default:
      break;
    }

  return c;
}

static void
mi_parse_argv (char *args, struct mi_parse *parse)
{
  char *chp = args;
  int argc = 0;
  char **argv = xmalloc ((argc + 1) * sizeof (char *));

  argv[argc] = NULL;
  while (1)
    {
      char *arg;

      /* skip leading white space */
      while (isspace (*chp))
	chp++;
      /* Three possibilities: EOF, quoted string, or other text. */
      switch (*chp)
	{
	case '\0':
	  parse->argv = argv;
	  parse->argc = argc;
	  return;
	case '"':
	  {
	    /* A quoted string. */
	    int len;
	    char *start = chp + 1;

	    /* Determine the buffer size. */
	    chp = start;
	    len = 0;
	    while (*chp != '\0' && *chp != '"')
	      {
		if (*chp == '\\')
		  {
		    chp++;
		    if (mi_parse_escape (&chp) <= 0)
		      {
			/* Do not allow split lines or "\000" */
			freeargv (argv);
			return;
		      }
		  }
		else
		  chp++;
		len++;
	      }
	    /* Insist on a closing quote. */
	    if (*chp != '"')
	      {
		freeargv (argv);
		return;
	      }
	    /* Insist on trailing white space. */
	    if (chp[1] != '\0' && !isspace (chp[1]))
	      {
		freeargv (argv);
		return;
	      }
	    /* create the buffer. */
	    arg = xmalloc ((len + 1) * sizeof (char));
	    /* And copy the characters in. */
	    chp = start;
	    len = 0;
	    while (*chp != '\0' && *chp != '"')
	      {
		if (*chp == '\\')
		  {
		    chp++;
		    arg[len] = mi_parse_escape (&chp);
		  }
		else
		  arg[len] = *chp++;
		len++;
	      }
	    arg[len] = '\0';
	    chp++;		/* that closing quote. */
	    break;
	  }
	default:
	  {
	    /* An unquoted string.  Accumulate all non blank
	       characters into a buffer. */
	    int len;
	    char *start = chp;

	    while (*chp != '\0' && !isspace (*chp))
	      {
		chp++;
	      }
	    len = chp - start;
	    arg = xmalloc ((len + 1) * sizeof (char));
	    strncpy (arg, start, len);
	    arg[len] = '\0';
	    break;
	  }
	}
      /* Append arg to argv. */
      argv = xrealloc (argv, (argc + 2) * sizeof (char *));
      argv[argc++] = arg;
      argv[argc] = NULL;
    }
}


void
mi_parse_free (struct mi_parse *parse)
{
  if (parse == NULL)
    return;
  if (parse->command != NULL)
    xfree (parse->command);
  if (parse->token != NULL)
    xfree (parse->token);
  if (parse->args != NULL)
    xfree (parse->args);
  if (parse->argv != NULL)
    freeargv (parse->argv);
  xfree (parse);
}

/* A cleanup that calls mi_parse_free.  */

static void
mi_parse_cleanup (void *arg)
{
  mi_parse_free (arg);
}

struct mi_parse *
mi_parse (char *cmd, char **token)
{
  char *chp;
  struct mi_parse *parse = XMALLOC (struct mi_parse);
  struct cleanup *cleanup;

  memset (parse, 0, sizeof (*parse));
  parse->all = 0;
  parse->thread_group = -1;
  parse->thread = -1;
  parse->frame = -1;

  cleanup = make_cleanup (mi_parse_cleanup, parse);

  /* Before starting, skip leading white space. */
  while (isspace (*cmd))
    cmd++;

  /* Find/skip any token and then extract it. */
  for (chp = cmd; *chp >= '0' && *chp <= '9'; chp++)
    ;
  *token = xmalloc (chp - cmd + 1);
  memcpy (*token, cmd, (chp - cmd));
  (*token)[chp - cmd] = '\0';

  /* This wasn't a real MI command.  Return it as a CLI_COMMAND. */
  if (*chp != '-')
    {
      while (isspace (*chp))
	chp++;
      parse->command = xstrdup (chp);
      parse->op = CLI_COMMAND;

      discard_cleanups (cleanup);

      return parse;
    }

  /* Extract the command. */
  {
    char *tmp = chp + 1;	/* discard ``-'' */

    for (; *chp && !isspace (*chp); chp++)
      ;
    parse->command = xmalloc (chp - tmp + 1);
    memcpy (parse->command, tmp, chp - tmp);
    parse->command[chp - tmp] = '\0';
  }

  /* Find the command in the MI table. */
  parse->cmd = mi_lookup (parse->command);
  if (parse->cmd == NULL)
    error (_("Undefined MI command: %s"), parse->command);

  /* Skip white space following the command. */
  while (isspace (*chp))
    chp++;

  /* Parse the --thread and --frame options, if present.  At present,
     some important commands, like '-break-*' are implemented by forwarding
     to the CLI layer directly.  We want to parse --thread and --frame
     here, so as not to leave those option in the string that will be passed
     to CLI.  */
  for (;;)
    {
      const char *option;
      size_t as = sizeof ("--all ") - 1;
      size_t tgs = sizeof ("--thread-group ") - 1;
      size_t ts = sizeof ("--thread ") - 1;
      size_t fs = sizeof ("--frame ") - 1;

      if (strncmp (chp, "--all ", as) == 0)
	{
	  parse->all = 1;
	  chp += as;
	}
      /* See if --all is the last token in the input.  */
      if (strcmp (chp, "--all") == 0)
	{
          parse->all = 1;
          chp += strlen (chp);
        }
      if (strncmp (chp, "--thread-group ", tgs) == 0)
	{
	  option = "--thread-group";
	  if (parse->thread_group != -1)
	    error (_("Duplicate '--thread-group' option"));
	  chp += tgs;
	  if (*chp != 'i')
	    error (_("Invalid thread group id"));
	  chp += 1;
	  parse->thread_group = strtol (chp, &chp, 10);
	}
      else if (strncmp (chp, "--thread ", ts) == 0)
	{
	  option = "--thread";
	  if (parse->thread != -1)
	    error (_("Duplicate '--thread' option"));
	  chp += ts;
	  parse->thread = strtol (chp, &chp, 10);
	}
      else if (strncmp (chp, "--frame ", fs) == 0)
	{
	  option = "--frame";
	  if (parse->frame != -1)
	    error (_("Duplicate '--frame' option"));
	  chp += fs;
	  parse->frame = strtol (chp, &chp, 10);
	}
      else
	break;

      if (*chp != '\0' && !isspace (*chp))
	error (_("Invalid value for the '%s' option"), option);
      while (isspace (*chp))
	chp++;
    }

  /* For new argv commands, attempt to return the parsed argument
     list. */
  if (parse->cmd->argv_func != NULL)
    {
      mi_parse_argv (chp, parse);
      if (parse->argv == NULL)
	error (_("Problem parsing arguments: %s %s"), parse->command, chp);
    }

  /* FIXME: DELETE THIS */
  /* For CLI commands, also return the remainder of the
     command line as a single string. */
  if (parse->cmd->cli.cmd != NULL)
    parse->args = xstrdup (chp);

  discard_cleanups (cleanup);

  /* Fully parsed. */
  parse->op = MI_COMMAND;
  return parse;
}
