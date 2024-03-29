/* Program and address space management, for GDB, the GNU debugger.

   Copyright (C) 2009, 2010, 2011 Free Software Foundation, Inc.

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
#include "gdbcmd.h"
#include "objfiles.h"
#include "arch-utils.h"
#include "gdbcore.h"
#include "solib.h"
#include "gdbthread.h"

/* The last program space number assigned.  */
int last_program_space_num = 0;

/* The head of the program spaces list.  */
struct program_space *program_spaces;

/* Pointer to the current program space.  */
struct program_space *current_program_space;

/* The last address space number assigned.  */
static int highest_address_space_num;

/* Prototypes for local functions */

static void program_space_alloc_data (struct program_space *);
static void program_space_free_data (struct program_space *);


/* An address space.  Currently this is not used for much other than
   for comparing if pspaces/inferior/threads see the same address
   space.  */

struct address_space
{
  int num;
};

/* Create a new address space object, and add it to the list.  */

struct address_space *
new_address_space (void)
{
  struct address_space *aspace;

  aspace = XZALLOC (struct address_space);
  aspace->num = ++highest_address_space_num;

  return aspace;
}

/* Maybe create a new address space object, and add it to the list, or
   return a pointer to an existing address space, in case inferiors
   share an address space on this target system.  */

struct address_space *
maybe_new_address_space (void)
{
  int shared_aspace = gdbarch_has_shared_address_space (target_gdbarch);

  if (shared_aspace)
    {
      /* Just return the first in the list.  */
      return program_spaces->aspace;
    }

  return new_address_space ();
}

static void
free_address_space (struct address_space *aspace)
{
  xfree (aspace);
}

int
address_space_num (struct address_space *aspace)
{
  return aspace->num;
}

/* Start counting over from scratch.  */

static void
init_address_spaces (void)
{
  highest_address_space_num = 0;
}



/* Adds a new empty program space to the program space list, and binds
   it to ASPACE.  Returns the pointer to the new object.  */

struct program_space *
add_program_space (struct address_space *aspace)
{
  struct program_space *pspace;

  pspace = XZALLOC (struct program_space);

  pspace->num = ++last_program_space_num;
  pspace->aspace = aspace;

  program_space_alloc_data (pspace);

  pspace->next = program_spaces;
  program_spaces = pspace;

  return pspace;
}

/* Releases program space PSPACE, and all its contents (shared
   libraries, objfiles, and any other references to the PSPACE in
   other modules).  It is an internal error to call this when PSPACE
   is the current program space, since there should always be a
   program space.  */

static void
release_program_space (struct program_space *pspace)
{
  struct cleanup *old_chain = save_current_program_space ();

  gdb_assert (pspace != current_program_space);

  set_current_program_space (pspace);

  breakpoint_program_space_exit (pspace);
  no_shared_libraries (NULL, 0);
  exec_close ();
  free_all_objfiles ();
  if (!gdbarch_has_shared_address_space (target_gdbarch))
    free_address_space (pspace->aspace);
  resize_section_table (&pspace->target_sections,
			-resize_section_table (&pspace->target_sections, 0));
    /* Discard any data modules have associated with the PSPACE.  */
  program_space_free_data (pspace);
  xfree (pspace);

  do_cleanups (old_chain);
}

/* Unlinks PSPACE from the pspace list, and releases it.  */

void
remove_program_space (struct program_space *pspace)
{
  struct program_space *ss, **ss_link;

  ss = program_spaces;
  ss_link = &program_spaces;
  while (ss)
    {
      if (ss != pspace)
	{
	  ss_link = &ss->next;
	  ss = *ss_link;
	  continue;
	}

      *ss_link = ss->next;
      release_program_space (ss);
      ss = *ss_link;
    }
}

/* Copies program space SRC to DEST.  Copies the main executable file,
   and the main symbol file.  Returns DEST.  */

struct program_space *
clone_program_space (struct program_space *dest, struct program_space *src)
{
  struct cleanup *old_chain;

  old_chain = save_current_program_space ();

  set_current_program_space (dest);

  if (src->ebfd != NULL)
    exec_file_attach (bfd_get_filename (src->ebfd), 0);

  if (src->symfile_object_file != NULL)
    symbol_file_add_main (src->symfile_object_file->name, 0);

  do_cleanups (old_chain);
  return dest;
}

/* Sets PSPACE as the current program space.  It is the caller's
   responsibility to make sure that the currently selected
   inferior/thread matches the selected program space.  */

void
set_current_program_space (struct program_space *pspace)
{
  if (current_program_space == pspace)
    return;

  gdb_assert (pspace != NULL);

  current_program_space = pspace;

  /* Different symbols change our view of the frame chain.  */
  reinit_frame_cache ();
}

/* A cleanups callback, helper for save_current_program_space
   below.  */

static void
restore_program_space (void *arg)
{
  struct program_space *saved_pspace = arg;

  set_current_program_space (saved_pspace);
}

/* Save the current program space so that it may be restored by a later
   call to do_cleanups.  Returns the struct cleanup pointer needed for
   later doing the cleanup.  */

struct cleanup *
save_current_program_space (void)
{
  struct cleanup *old_chain = make_cleanup (restore_program_space,
					    current_program_space);

  return old_chain;
}

/* Returns true iff there's no inferior bound to PSPACE.  */

static int
pspace_empty_p (struct program_space *pspace)
{
  if (find_inferior_for_program_space (pspace) != NULL)
      return 0;

  return 1;
}

/* Prune away automatically added program spaces that aren't required
   anymore.  */

void
prune_program_spaces (void)
{
  struct program_space *ss, **ss_link;
  struct program_space *current = current_program_space;

  ss = program_spaces;
  ss_link = &program_spaces;
  while (ss)
    {
      if (ss == current || !pspace_empty_p (ss))
	{
	  ss_link = &ss->next;
	  ss = *ss_link;
	  continue;
	}

      *ss_link = ss->next;
      release_program_space (ss);
      ss = *ss_link;
    }
}

/* Prints the list of program spaces and their details on UIOUT.  If
   REQUESTED is not -1, it's the ID of the pspace that should be
   printed.  Otherwise, all spaces are printed.  */

static void
print_program_space (struct ui_out *uiout, int requested)
{
  struct program_space *pspace;
  int count = 0;
  struct cleanup *old_chain;

  /* Might as well prune away unneeded ones, so the user doesn't even
     seem them.  */
  prune_program_spaces ();

  /* Compute number of pspaces we will print.  */
  ALL_PSPACES (pspace)
    {
      if (requested != -1 && pspace->num != requested)
	continue;

      ++count;
    }

  /* There should always be at least one.  */
  gdb_assert (count > 0);

  old_chain = make_cleanup_ui_out_table_begin_end (uiout, 3, count, "pspaces");
  ui_out_table_header (uiout, 1, ui_left, "current", "");
  ui_out_table_header (uiout, 4, ui_left, "id", "Id");
  ui_out_table_header (uiout, 17, ui_left, "exec", "Executable");
  ui_out_table_body (uiout);

  ALL_PSPACES (pspace)
    {
      struct cleanup *chain2;
      struct inferior *inf;
      int printed_header;

      if (requested != -1 && requested != pspace->num)
	continue;

      chain2 = make_cleanup_ui_out_tuple_begin_end (uiout, NULL);

      if (pspace == current_program_space)
	ui_out_field_string (uiout, "current", "*");
      else
	ui_out_field_skip (uiout, "current");

      ui_out_field_int (uiout, "id", pspace->num);

      if (pspace->ebfd)
	ui_out_field_string (uiout, "exec",
			     bfd_get_filename (pspace->ebfd));
      else
	ui_out_field_skip (uiout, "exec");

      /* Print extra info that doesn't really fit in tabular form.
	 Currently, we print the list of inferiors bound to a pspace.
	 There can be more than one inferior bound to the same pspace,
	 e.g., both parent/child inferiors in a vfork, or, on targets
	 that share pspaces between inferiors.  */
      printed_header = 0;
      for (inf = inferior_list; inf; inf = inf->next)
	if (inf->pspace == pspace)
	  {
	    if (!printed_header)
	      {
		printed_header = 1;
		printf_filtered ("\n\tBound inferiors: ID %d (%s)",
				 inf->num,
				 target_pid_to_str (pid_to_ptid (inf->pid)));
	      }
	    else
	      printf_filtered (", ID %d (%s)",
			       inf->num,
			       target_pid_to_str (pid_to_ptid (inf->pid)));
	  }

      ui_out_text (uiout, "\n");
      do_cleanups (chain2);
    }

  do_cleanups (old_chain);
}

/* Boolean test for an already-known program space id.  */

static int
valid_program_space_id (int num)
{
  struct program_space *pspace;

  ALL_PSPACES (pspace)
    if (pspace->num == num)
      return 1;

  return 0;
}

/* If ARGS is NULL or empty, print information about all program
   spaces.  Otherwise, ARGS is a text representation of a LONG
   indicating which the program space to print information about.  */

static void
maintenance_info_program_spaces_command (char *args, int from_tty)
{
  int requested = -1;

  if (args && *args)
    {
      requested = parse_and_eval_long (args);
      if (!valid_program_space_id (requested))
	error (_("program space ID %d not known."), requested);
    }

  print_program_space (current_uiout, requested);
}

/* Simply returns the count of program spaces.  */

int
number_of_program_spaces (void)
{
  struct program_space *pspace;
  int count = 0;

  ALL_PSPACES (pspace)
    count++;

  return count;
}

/* Update all program spaces matching to address spaces.  The user may
   have created several program spaces, and loaded executables into
   them before connecting to the target interface that will create the
   inferiors.  All that happens before GDB has a chance to know if the
   inferiors will share an address space or not.  Call this after
   having connected to the target interface and having fetched the
   target description, to fixup the program/address spaces mappings.

   It is assumed that there are no bound inferiors yet, otherwise,
   they'd be left with stale referenced to released aspaces.  */

void
update_address_spaces (void)
{
  int shared_aspace = gdbarch_has_shared_address_space (target_gdbarch);
  struct program_space *pspace;
  struct inferior *inf;

  init_address_spaces ();

  if (shared_aspace)
    {
      struct address_space *aspace = new_address_space ();

      free_address_space (current_program_space->aspace);
      ALL_PSPACES (pspace)
	pspace->aspace = aspace;
    }
  else
    ALL_PSPACES (pspace)
      {
	free_address_space (pspace->aspace);
	pspace->aspace = new_address_space ();
      }

  for (inf = inferior_list; inf; inf = inf->next)
    if (gdbarch_has_global_solist (target_gdbarch))
      inf->aspace = maybe_new_address_space ();
    else
      inf->aspace = inf->pspace->aspace;
}

/* Save the current program space so that it may be restored by a later
   call to do_cleanups.  Returns the struct cleanup pointer needed for
   later doing the cleanup.  */

struct cleanup *
save_current_space_and_thread (void)
{
  struct cleanup *old_chain;

  /* If restoring to null thread, we need to restore the pspace as
     well, hence, we need to save the current program space first.  */
  old_chain = save_current_program_space ();
  save_current_inferior ();
  make_cleanup_restore_current_thread ();

  return old_chain;
}

/* Switches full context to program space PSPACE.  Switches to the
   first thread found bound to PSPACE.  */

void
switch_to_program_space_and_thread (struct program_space *pspace)
{
  struct inferior *inf;

  inf = find_inferior_for_program_space (pspace);
  if (inf != NULL)
    {
      struct thread_info *tp;

      tp = any_live_thread_of_process (inf->pid);
      if (tp != NULL)
	{
	  switch_to_thread (tp->ptid);
	  /* Switching thread switches pspace implicitly.  We're
	     done.  */
	  return;
	}
    }

  switch_to_thread (null_ptid);
  set_current_program_space (pspace);
}



/* Keep a registry of per-program_space data-pointers required by other GDB
   modules.  */

struct program_space_data
{
  unsigned index;
  void (*cleanup) (struct program_space *, void *);
};

struct program_space_data_registration
{
  struct program_space_data *data;
  struct program_space_data_registration *next;
};

struct program_space_data_registry
{
  struct program_space_data_registration *registrations;
  unsigned num_registrations;
};

static struct program_space_data_registry program_space_data_registry
  = { NULL, 0 };

const struct program_space_data *
register_program_space_data_with_cleanup
  (void (*cleanup) (struct program_space *, void *))
{
  struct program_space_data_registration **curr;

  /* Append new registration.  */
  for (curr = &program_space_data_registry.registrations;
       *curr != NULL; curr = &(*curr)->next);

  *curr = XMALLOC (struct program_space_data_registration);
  (*curr)->next = NULL;
  (*curr)->data = XMALLOC (struct program_space_data);
  (*curr)->data->index = program_space_data_registry.num_registrations++;
  (*curr)->data->cleanup = cleanup;

  return (*curr)->data;
}

const struct program_space_data *
register_program_space_data (void)
{
  return register_program_space_data_with_cleanup (NULL);
}

static void
program_space_alloc_data (struct program_space *pspace)
{
  gdb_assert (pspace->data == NULL);
  pspace->num_data = program_space_data_registry.num_registrations;
  pspace->data = XCALLOC (pspace->num_data, void *);
}

static void
program_space_free_data (struct program_space *pspace)
{
  gdb_assert (pspace->data != NULL);
  clear_program_space_data (pspace);
  xfree (pspace->data);
  pspace->data = NULL;
}

void
clear_program_space_data (struct program_space *pspace)
{
  struct program_space_data_registration *registration;
  int i;

  gdb_assert (pspace->data != NULL);

  for (registration = program_space_data_registry.registrations, i = 0;
       i < pspace->num_data;
       registration = registration->next, i++)
    if (pspace->data[i] != NULL && registration->data->cleanup)
      registration->data->cleanup (pspace, pspace->data[i]);

  memset (pspace->data, 0, pspace->num_data * sizeof (void *));
}

void
set_program_space_data (struct program_space *pspace,
		       const struct program_space_data *data,
		       void *value)
{
  gdb_assert (data->index < pspace->num_data);
  pspace->data[data->index] = value;
}

void *
program_space_data (struct program_space *pspace,
		    const struct program_space_data *data)
{
  gdb_assert (data->index < pspace->num_data);
  return pspace->data[data->index];
}



void
initialize_progspace (void)
{
  add_cmd ("program-spaces", class_maintenance,
	   maintenance_info_program_spaces_command,
	   _("Info about currently known program spaces."),
	   &maintenanceinfolist);

  /* There's always one program space.  Note that this function isn't
     an automatic _initialize_foo function, since other
     _initialize_foo routines may need to install their per-pspace
     data keys.  We can only allocate a progspace when all those
     modules have done that.  Do this before
     initialize_current_architecture, because that accesses exec_bfd,
     which in turn dereferences current_program_space.  */
  current_program_space = add_program_space (new_address_space ());
}
