/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Mod
public import Lang.CoCSL.Sequential
public import Examples.CSL.Allocator.Layout

/-!
# The link-first allocator source program

Link-first remote frees and owner collection, scoped from mimalloc v2.5.2 (`src/free.c`,
`src/page.c`); the model omits delayed-free flags and abandoned-page recovery
(← `examples/CSL/Allocator/Program.v`).
-/

@[expose] public section
namespace Examples.CSL.Allocator.Program
open CoCSL Tisl.Heap Examples.CSL.Allocator.Layout

def init_links (first count : Nat) : CProg Unit :=
  write_list (link_updates first count)

def init_page (base capacity : Nat) : CProg Unit :=
  .bind (.write (remote_head base) 0) fun _ =>
  .bind (.write (drain_head base) 0) fun _ =>
  .bind (.write (mailbox base false) 0) fun _ =>
  .bind (.write (mailbox base true) 0) fun _ =>
  .bind (.write (local_head base) (match capacity with | 0 => 0 | _ + 1 => base + 5)) fun _ =>
  init_links (base + 5) capacity

def new_page (capacity : Nat) : CProg Nat :=
  .bind (.alloc (page_size capacity)) fun base =>
  .bind (init_page base capacity) fun _ => .ret base

def remote_attempt (base block : Nat) : CProg (Option Unit) :=
  .bind (.read (remote_head base)) fun old =>
  .bind .yield fun _ =>
  .bind (.write block old) fun _ =>
  .bind .yield fun _ =>
  .bind (.cas (.lit (remote_head base)) (.lit old) (.lit block)) fun success =>
    if success then
      .bind (.emit tag_retire block) fun _ => .ret none
    else
      .bind (.emit tag_retry block) fun _ =>
      .bind .yield fun _ => .ret (some ())

def remote_free (base block : Nat) : CProg Unit :=
  .untilNone (remote_attempt base block)

def detach_attempt (base : Nat) : CProg (Option Unit) :=
  .bind (.read (remote_head base)) fun old =>
  .bind .yield fun _ =>
  .bind (.cas (.lit (remote_head base)) (.lit old) (.lit 0)) fun success =>
    if success then
      .bind (.write (drain_head base) old) fun _ =>
      .bind .yield fun _ => .ret none
    else
      .bind .yield fun _ => .ret (some ())

def detach_remote (base : Nat) : CProg Unit :=
  .untilNone (detach_attempt base)

def reclaim_step (base : Nat) : CProg (Option Unit) :=
  .bind (.read (drain_head base)) fun block =>
    if block == 0 then
      .bind .yield fun _ => .ret none
    else
      .bind (.read block) fun next =>
      .bind (.read (local_head base)) fun lcl =>
      .bind (.write block lcl) fun _ =>
      .bind (.write (local_head base) block) fun _ =>
      .bind (.write (drain_head base) next) fun _ =>
      .bind (.emit tag_reclaim block) fun _ =>
      .bind .yield fun _ => .ret (some ())

def collect_remote (base : Nat) : CProg Unit :=
  .bind (detach_remote base) fun _ =>
  .untilNone (reclaim_step base)

def offer_block (base : Nat) (client : Bool) : CProg Unit :=
  .bind (.read (mailbox base client)) fun offered =>
    if offered == 0 then
      .bind (.read (local_head base)) fun block =>
        if block == 0 then
          .bind .yield fun _ => .ret ()
        else
          .bind (.read block) fun next =>
          .bind (.write (local_head base) next) fun _ =>
          .bind (.write (mailbox base client) block) fun _ =>
          .bind (.emit tag_alloc block) fun _ =>
          .bind .yield fun _ => .ret ()
    else
      .bind .yield fun _ => .ret ()

def client_round (base : Nat) (client : Bool) : CProg (Option Unit) :=
  .bind (.read (mailbox base client)) fun block =>
    if block == 0 then
      .bind .yield fun _ => .ret (some ())
    else
      .bind (.write (mailbox base client) 0) fun _ =>
      .bind (.write (block + 1) (if client then 2 else 1)) fun _ =>
      .bind .yield fun _ =>
      .bind (remote_free base block) fun _ =>
      -- Publication has returned; the client no longer accesses `block`.
      .bind .yield fun _ =>
      .ret (some ())

def remote_client (base : Nat) (client : Bool) : CProg Unit :=
  .untilNone (client_round base client)

def owner_round (base : Nat) : CProg (Option Unit) :=
  .bind (collect_remote base) fun _ =>
  .bind (offer_block base false) fun _ =>
  .bind (offer_block base true) fun _ =>
  .ret (some ())

def owner (base : Nat) : CProg Unit :=
  .bind .yield fun _ => .untilNone (owner_round base)

def allocator_program (capacity : Nat) : CProg Unit :=
  .bind (new_page capacity) fun base =>
  .bind (.fork (remote_client base false)) fun _ =>
  .bind (.fork (remote_client base true)) fun _ =>
  owner base

end Examples.CSL.Allocator.Program
