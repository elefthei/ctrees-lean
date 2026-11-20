/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Allocator.LivenessRanks
public import Examples.CSL.Allocator.Execution
public import Examples.CSL.Allocator.Replay
public import Logic.Yield.Fair
public import Logic.CTree.TraceRules
public import Logic.Setoid

/-!
# Allocator liveness under every fair scheduler, and ABA robustness

Every observation kind of the link-first allocator (allocation, retirement, reclamation) recurs
under every fair scheduling policy, from the real source program, via the fairness inversion rule
`agaf_pool_simulation_fair` on a ghost-ranked turn model; a concrete ABA script shows a stale
remote CAS loses no block (<- `examples/CSL/Allocator/Liveness.v`, from `mboxh` on; the model
budgets precede it in `Examples.CSL.Allocator.LivenessRanks`).
-/

@[expose] public section
namespace Examples.CSL.Allocator.Liveness
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Notation CoCSL
open Examples.CSL.Allocator.Layout Examples.CSL.Allocator.Program Examples.CSL.Allocator.Model
open Examples.CSL.Allocator.Execution Examples.CSL.Allocator.Replay
open Actor owner_pc remote_pc

/-! ## Recurrence of every observation kind under any fair scheduler

The fairness inversion rule `agaf_pool_simulation_fair` wants an invariant, a well-founded rank
and a helpful slot on ghost data projecting to model states. The ghost is the model state with
the ownership lists of `allocator_view`; the rank is (occurrence bound left, block-position
potential, helpful distance) under `rank3`. Every block move that is not itself a `kind` event
drops the potential; the helpful actor is the one that can move a block next, and each of its
silent turns drops its distance to that move by one. -/

def mboxh (h : Heap) (client : Bool) : Nat :=
  match h (mailbox 1 client) with | some m => m | none => 0

def mbox (s : AState) (client : Bool) : Nat := mboxh s.aheap client

def nH (s : AState) : Nat := (held s.remote0_state).length + (held s.remote1_state).length

def is_poll : remote_pc → Bool
  | RPoll => true
  | RRead _ | RLink _ _ | RCAS _ _ => false

theorem mailbox_nodes_length (m : Nat) : (mailbox_nodes m).length = if m = 0 then 0 else 1 := by
  by_cases h : m = 0 <;> simp [mailbox_nodes, h]

theorem held_length (pc : remote_pc) : (held pc).length = if is_poll pc then 0 else 1 := by
  cases pc <;> rfl

/-- Block-position potential. Moves: alloc L→mailbox, pickup mailbox→held, retire held→R,
detach R→D, reclaim D→L; the coefficients make every move that is not a `kind` event strictly
decreasing. -/
def phi (kind : Nat) (s : AState) (L R D : List Nat) : Nat :=
  let mailboxes := (mailbox_nodes (mbox s false)).length + (mailbox_nodes (mbox s true)).length
  if kind = tag_alloc then 4 * mailboxes + 3 * nH s + 2 * R.length + D.length
  else if kind = tag_retire then mailboxes + 2 * L.length + 3 * D.length + 4 * R.length
  else R.length + 2 * nH s + 3 * mailboxes + 4 * L.length

/-- Owner block moves enabled at the points of its cycle: 1 = `OCAS` (detach), 2 = `ODrain`
(reclaim), 3 = `OOffer false`, 4 = `OOffer true`. Stated on the heap so that a silent turn
leaves them syntactically alone. -/
def en1 (R : List Nat) : Bool := decide (0 < R.length)
def en2 (D : List Nat) : Bool := decide (0 < D.length)
def en3 (h : Heap) (L : List Nat) : Bool := decide (0 < L.length) && mboxh h false == 0
def en4 (h : Heap) (L : List Nat) : Bool := decide (0 < L.length) && mboxh h true == 0

def owner_work (h : Heap) (L R D : List Nat) : Bool :=
  en1 R || en2 D || en3 h L || en4 h L

def remote_has_block (s : AState) (client : Bool) : Bool :=
  !(mbox s client == 0) || !is_poll (if client then s.remote1_state else s.remote0_state)

def helpful (s : AState) (L R D : List Nat) : Actor :=
  if owner_work s.aheap L R D then Owner
  else if remote_has_block s false then Remote0 else Remote1

/-- Owner turns until its next block move, from each cycle point. -/
def from1 (h : Heap) (L R D : List Nat) : Nat :=
  if en1 R then 1 else if en2 D then 2 else if en3 h L then 3 else if en4 h L then 4 else 0

def odist (s : AState) (L R D : List Nat) : Nat :=
  match s.owner_state with
  | ORead => 1 + from1 s.aheap L R D
  | OCAS old => if R.headD 0 = old then from1 s.aheap L R D else 2 + from1 s.aheap L R D
  | ODrain =>
    if en2 D then 1 else if en3 s.aheap L then 2 else if en4 s.aheap L then 3
    else if en1 R then 5 else 0
  | OOffer false =>
    if en3 s.aheap L then 1 else if en4 s.aheap L then 2 else if en1 R then 4
    else if en2 D then 5 else 0
  | OOffer true =>
    if en4 s.aheap L then 1 else if en1 R then 3 else if en2 D then 4
    else if en3 s.aheap L then 5 else 0

/-- Remote distance: the contention cost (phase + staleness). -/
def rdist (s : AState) (who : Actor) : Nat :=
  match who with
  | Owner => 0
  | Remote0 => contention_cost (contention_head s) s.remote0_state
  | Remote1 => contention_cost (contention_head s) s.remote1_state

def hdist (s : AState) (L R D : List Nat) : Nat :=
  match helpful s L R D with
  | Owner => odist s L R D
  | who => rdist s who

def fresh_kind (kind kb : Nat) : CSLObs (Nat × Nat) → Prop :=
  csl_indexed fun o => o.value.1 = kind ∧ kb ≤ o.index

def AG_ghost : Type := AState × (List Nat × (List Nat × List Nat))

def InvG (capacity : Nat) (g : AG_ghost) : Prop :=
  match g with | (s, (L, (R, D))) => allocator_view 1 capacity s L R D

def rankG (kind kb : Nat) (g : AG_ghost) : Nat × (Nat × Nat) :=
  match g with | (s, (L, (R, D))) => (kb - s.acount, (phi kind s L R D, hdist s L R D))

def targetG (g : AG_ghost) : Fin 3 :=
  match g with | (s, (L, (R, D))) => slot_of_actor (helpful s L R D)

/-- The three-way obligation of `agaf_pool_simulation_fair`. -/
def progress (kind kb : Nat) (who : Actor) (event : List (CSLObs (Nat × Nat)))
    (g g' : AG_ghost) : Prop :=
  (∃ o ∈ event, fresh_kind kind kb o) ∨
  rank3 (rankG kind kb g') (rankG kind kb g) ∨
  (slot_of_actor who ≠ targetG g ∧ rankG kind kb g' = rankG kind kb g ∧ targetG g' = targetG g)

theorem rank3_step (a a' b b' c c' : Nat) :
    a' ≤ a → (a' = a → b' < b ∨ (b' = b ∧ c' < c)) → rank3 (a', (b', c')) (a, (b, c)) := by
  intro hle hcase
  by_cases hlt : a' < a
  · exact rank3_bound _ _ _ _ _ _ hlt
  · obtain rfl : a' = a := by omega
    rcases hcase rfl with hb | ⟨rfl, hc⟩
    · exact rank3_pos _ _ _ _ _ hb
    · exact rank3_phase _ _ _ _ hc

theorem helpful_owner (s : AState) (L R D : List Nat) :
    helpful s L R D = Owner → owner_work s.aheap L R D = true := by
  unfold helpful; split
  · intro; assumption
  · split <;> intro h <;> cases h

theorem helpful_remote0 (s : AState) (L R D : List Nat) :
    helpful s L R D = Remote0 → remote_has_block s false = true := by
  unfold helpful; split
  · intro h; cases h
  · split
    · intro; assumption
    · intro h; cases h

/-- The default helpful remote holds or owns a block: the pool is non-empty and nothing else
does. -/
theorem helpful_remote1 (capacity : Nat) (s : AState) (L R D : List Nat) :
    0 < capacity → allocator_view 1 capacity s L R D →
    helpful s L R D = Remote1 → remote_has_block s true = true := by
  rintro hcap ⟨-, -, m0, m1, -, -, -, -, -, -, hm0, hm1, hp, -⟩ hh
  have hlen := hp.length_eq
  simp only [List.length_append, page_blocks_length, mailbox_nodes_length, held_length] at hlen
  simp only [helpful, owner_work, en1, en2, en3, en4, remote_has_block, mbox, mboxh, hm0,
    hm1] at hh ⊢
  revert hh hlen
  generalize L.length = a; generalize R.length = b; generalize D.length = c
  cases s.remote0_state <;> cases s.remote1_state <;>
    simp only [is_poll] <;> by_cases h0 : m0 = 0 <;> by_cases h1 : m1 = 0 <;>
    simp [h0, h1] <;> (repeat' split) <;> (try simp) <;> omega

/-! ### The three progress shapes -/

theorem progress_kind_event (kind kb : Nat) (who : Actor) (s s' : AState)
    (ls ls' : List Nat × (List Nat × List Nat)) (b count : Nat)
    (event : List (CSLObs (Nat × Nat))) :
    s.acount = count → s'.acount = count + 1 →
    stamp (kind, b) count ∈ csl_emissions event →
    progress kind kb who event (s, ls) (s', ls') := by
  rintro rfl hc hin
  obtain ⟨L, R, D⟩ := ls
  obtain ⟨L', R', D'⟩ := ls'
  by_cases hle : kb ≤ s.acount
  · exact .inl ⟨_, (csl_emissions_in _ _).1 hin, rfl, hle⟩
  · refine .inr (.inl ?_)
    simp only [rankG, hc]
    exact rank3_bound _ _ _ _ _ _ (by omega)

theorem progress_move (kind kb : Nat) (who : Actor) (event : List (CSLObs (Nat × Nat)))
    (s s' : AState) (L R D L' R' D' : List Nat) :
    s.acount ≤ s'.acount → s'.acount ≤ s.acount + 1 →
    phi kind s' L' R' D' < phi kind s L R D →
    progress kind kb who event (s, (L, (R, D))) (s', (L', (R', D'))) := by
  intro hlo _ hphi
  exact .inr (.inl (rank3_step _ _ _ _ _ _ (by omega) fun _ => .inl hphi))

theorem progress_idle (kind kb : Nat) (who : Actor) (event : List (CSLObs (Nat × Nat)))
    (s s' : AState) (L R D : List Nat) :
    mbox s' false = mbox s false → mbox s' true = mbox s true →
    contention_head s' = contention_head s →
    s.acount ≤ s'.acount → s'.acount ≤ s.acount + 1 →
    (match who with
     | Owner =>
       s'.remote0_state = s.remote0_state ∧ s'.remote1_state = s.remote1_state ∧
       (owner_work s.aheap L R D = true → odist s' L R D + 1 = odist s L R D)
     | Remote0 =>
       s'.owner_state = s.owner_state ∧ s'.remote1_state = s.remote1_state ∧
       is_poll s'.remote0_state = is_poll s.remote0_state ∧
       (helpful s L R D = Remote0 → rdist s' Remote0 + 1 = rdist s Remote0)
     | Remote1 =>
       s'.owner_state = s.owner_state ∧ s'.remote0_state = s.remote0_state ∧
       is_poll s'.remote1_state = is_poll s.remote1_state ∧
       (helpful s L R D = Remote1 → rdist s' Remote1 + 1 = rdist s Remote1)) →
    progress kind kb who event (s, (L, (R, D))) (s', (L, (R, D))) := by
  intro em0 em1 ehead hlo hhi hwho
  have emh0 : mboxh s'.aheap false = mboxh s.aheap false := em0
  have emh1 : mboxh s'.aheap true = mboxh s.aheap true := em1
  have hrem : remote_has_block s' false = remote_has_block s false ∧
      remote_has_block s' true = remote_has_block s true := by
    simp only [remote_has_block, em0, em1, ↓reduceIte, Bool.false_eq_true]
    cases who <;> obtain ⟨e1, e2, e3⟩ := hwho <;> simp only [e1, e2] <;>
      (try obtain ⟨e3, -⟩ := e3) <;> simp [e3]
  have hhelp : helpful s' L R D = helpful s L R D := by
    unfold helpful owner_work en3 en4; rw [emh0, emh1, hrem.1]
  have hphi : phi kind s' L R D = phi kind s L R D := by
    simp only [phi, nH, em0, em1, held_length]
    cases who <;> obtain ⟨e1, e2, e3⟩ := hwho <;> simp only [e1, e2] <;>
      (try obtain ⟨e3, -⟩ := e3) <;> simp only [e3]
  have hodist : s'.owner_state = s.owner_state → odist s' L R D = odist s L R D := by
    intro eop
    unfold odist from1 en3 en4; rw [eop, emh0, emh1]
  have hsame : who = helpful s L R D → hdist s' L R D + 1 = hdist s L R D := by
    intro hw
    simp only [hdist, hhelp, ← hw]
    cases who with
    | Owner => exact hwho.2.2 (helpful_owner s L R D hw.symm)
    | Remote0 => exact hwho.2.2.2 hw.symm
    | Remote1 => exact hwho.2.2.2 hw.symm
  have hother : who ≠ helpful s L R D → hdist s' L R D = hdist s L R D := by
    intro hw
    simp only [hdist, hhelp]
    cases hh : helpful s L R D with
    | Owner =>
      cases who
      · exact absurd hh.symm hw
      all_goals exact hodist hwho.1
    | Remote0 =>
      cases who
      · simp only [rdist, ehead, hwho.1]
      · exact absurd hh.symm hw
      · simp only [rdist, ehead, hwho.2.1]
    | Remote1 =>
      cases who
      · simp only [rdist, ehead, hwho.2.1]
      · simp only [rdist, ehead, hwho.2.1]
      · exact absurd hh.symm hw
  by_cases hslot : slot_of_actor who = slot_of_actor (helpful s L R D)
  · have heq : who = helpful s L R D := by
      simpa only [actor_of_slot_of_actor] using congrArg actor_of_slot hslot
    refine .inr (.inl ?_)
    simp only [rankG, hphi]
    exact rank3_step _ _ _ _ _ _ (by omega) fun _ => .inr ⟨rfl, by have := hsame heq; omega⟩
  · have hne : who ≠ helpful s L R D := fun h => hslot (h ▸ rfl)
    by_cases hlt : kb - s'.acount < kb - s.acount
    · exact .inr (.inl (rank3_bound _ _ _ _ _ _ hlt))
    · refine .inr (.inr ⟨hslot, ?_, ?_⟩)
      · simp only [rankG, hphi, hother hne, show kb - s'.acount = kb - s.acount by omega]
      · simp only [targetG, hhelp]


/-! ### One turn makes progress -/

/-- Inversion of an ownership step that neither emits a block move nor detaches: the ownership
lists are unchanged. -/
theorem transition_silent {who : Actor} {o o' : owner_pc} {event : List (CSLObs (Nat × Nat))}
    {L R D L' R' D' : List Nat} :
    ownership_transition who o o' event L R D L' R' D' →
    (csl_emissions event = [] ∨ ∃ b idx, csl_emissions event = [stamp (tag_retry, b) idx]) →
    (who = Owner → o' ≠ ODrain) → L' = L ∧ R' = R ∧ D' = D := by
  intro h hev hdrain
  cases h with
  | ownership_detach => exact absurd rfl (hdrain rfl)
  | ownership_drain | ownership_offer | ownership_publish =>
    simp [csl_emissions_heap_prefix, csl_emissions, tag_retry, tag_reclaim, tag_alloc,
      tag_retire] at hev
  | _ => exact ⟨rfl, rfl, rfl⟩

/-- Inversion of a detach: the remote list becomes the drain list. -/
theorem transition_detach {who : Actor} {o o' : owner_pc} {event : List (CSLObs (Nat × Nat))}
    {L R D L' R' D' : List Nat} :
    ownership_transition who o o' event L R D L' R' D' → csl_emissions event = [] →
    who = Owner → o' = ODrain → L' = L ∧ R' = [] ∧ D' = R := by
  intro h hev hwho ho
  cases h with
  | ownership_detach => exact ⟨rfl, rfl, rfl⟩
  | ownership_drain => simp [csl_emissions_heap_prefix, csl_emissions] at hev
  | ownership_remote _ _ _ _ _ _ hne | ownership_publish _ _ _ _ _ _ _ _ hne =>
    exact absurd hwho hne
  | _ => first | cases ho | (unfold owner_after_offer at ho; split at ho <;> cases ho)

/-- Inversion of an ownership step with a non-retry emission: the emitted block moved. -/
theorem transition_emit {who : Actor} {o o' : owner_pc} {event : List (CSLObs (Nat × Nat))}
    {L R D L' R' D' : List Nat} {tag b idx : Nat} :
    ownership_transition who o o' event L R D L' R' D' →
    csl_emissions event = [stamp (tag, b) idx] → tag ≠ tag_retry →
    (tag = tag_reclaim ∧ D = b :: D' ∧ L' = b :: L ∧ R' = R) ∨
    (tag = tag_alloc ∧ L = b :: L' ∧ R' = R ∧ D' = D) ∨
    (tag = tag_retire ∧ L' = L ∧ R' = b :: R ∧ D' = D) := by
  intro h hev htag
  cases h with
  | ownership_drain =>
    simp [csl_emissions_heap_prefix, csl_emissions] at hev
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hev
    exact .inl ⟨rfl, rfl, rfl, rfl⟩
  | ownership_offer =>
    simp [csl_emissions_heap_prefix, csl_emissions] at hev
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hev
    exact .inr (.inl ⟨rfl, rfl, rfl, rfl⟩)
  | ownership_publish =>
    simp [csl_emissions_heap_prefix, csl_emissions] at hev
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hev
    exact .inr (.inr ⟨rfl, rfl, rfl, rfl⟩)
  | ownership_remote _ _ _ _ _ _ _ hne =>
    rcases hne with hne | ⟨b', idx', hne⟩ <;> rw [hne] at hev <;> simp at hev
    exact absurd hev.1.1.symm htag
  | _ => simp [csl_emissions, csl_emissions_heaps] at hev

/-- Evaluate the selected turn on the view's cell values (Rocq `cbn [turn]; rewrite H…`). -/
macro "fair_eval " hturn:ident hr:ident hl:ident hd:ident hm0:ident hm1:ident : tactic =>
  `(tactic| simp (disch := omega) only [turn, remote_head, local_head, drain_head, mailbox,
    upd_eq, upd_neq, $hr:ident, $hl:ident, $hd:ident, $hm0:ident, $hm1:ident,
    Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd, beq_iff_eq, eq_self_iff_true,
    List.headD_nil, List.headD_cons, Option.some.injEq, Prod.mk.injEq] at $hturn:ident)

/-- Normalize heap reads, mailboxes and the contention head after a turn (Rocq `fair_cells`). -/
macro "fair_cells " hr:ident hm0:ident hm1:ident : tactic => `(tactic|
  simp (disch := omega) only [mbox, mboxh, contention_head, remote_head, mailbox, upd_eq,
    upd_neq, $hr:ident, $hm0:ident, $hm1:ident, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd,
    List.headD_nil, List.headD_cons, Option.getD_some, is_poll])

/-- A helpful owner's silent turn: both distances are the same `if`-chain on the same mailbox
reads, one step apart (Rocq `fair_odist`). -/
macro "fair_odist " hw:ident hm0:ident hm1:ident : tactic => `(tactic| (
  simp (disch := omega) only [odist, owner_work, from1, en1, en2, en3, en4, mboxh, mailbox,
    upd_eq, upd_neq, $hm0:ident, $hm1:ident, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd,
    List.length_cons, List.length_nil] at $hw:ident ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at $hw:ident ⊢
  (repeat' split) <;> omega))

/-- A remote's silent turn: its contention cost drops by one (Rocq `fair_rdist`). -/
macro "fair_rdist " hr:ident : tactic => `(tactic| (
  simp (disch := omega) only [rdist, contention_cost, contention_phase, contention_stale,
    contention_head, remote_head, upd_eq, upd_neq, $hr:ident, List.headD_nil, List.headD_cons,
    Option.getD_some, reduceIte, ↓reduceIte]
  all_goals ((repeat' split) <;> omega)))

/-- Block-position potential after a move (Rocq `fair_phi`); `hk` excludes the measured kind. -/
macro "fair_phi " hkind:ident hm0:ident hm1:ident hk:(ident)? : tactic => do
  let unfold_hk ← match hk with
    | some hk => `(tactic| try simp only [tag_alloc, tag_retire, tag_reclaim] at $hk:ident)
    | none => `(tactic| skip)
  `(tactic| (
    simp (disch := omega) only [phi, nH, mbox, mboxh, mailbox, upd_eq, upd_neq, $hm0:ident,
      $hm1:ident, Bool.false_eq_true, ↓reduceIte, reduceIte, eq_self_iff_true, Nat.reduceAdd,
      mailbox_nodes_length, held_length, is_poll, List.length_cons, List.length_nil, tag_alloc,
      tag_retire, tag_reclaim]
    simp only [List.mem_cons, List.mem_nil_iff, or_false, tag_alloc, tag_retire,
      tag_reclaim] at $hkind:ident
    $unfold_hk:tactic
    (repeat' split) <;> omega))

theorem allocator_fair_turn (capacity kind kb : Nat) :
    0 < capacity → kind ∈ [tag_alloc, tag_retire, tag_reclaim] →
    ∀ (g : AG_ghost) who s' event,
      InvG capacity g → turn 1 who g.1 = some (s', event) →
      ∃ g', g'.1 = s' ∧ InvG capacity g' ∧ progress kind kb who event g g' := by
  rintro hcap hkind ⟨s, L, R, D⟩ who t event hview hturn
  obtain ⟨L', R', D', hview', hstep⟩ := turn_view_step 1 capacity who s t event L R D hview hturn
  refine ⟨(t, (L', (R', D'))), rfl, hview', ?_⟩
  have hview_s := hview
  obtain ⟨h, allocs, count, op, p0, p1⟩ := s
  obtain ⟨-, hback, m0, m1, hr, hl, hd, CL, -, CD, hm0, hm1, hp, hop, -, hc0, hc1⟩ := hview
  dsimp only at hback hr hl hd CL CD hm0 hm1 hp hop hc0 hc1 hturn hstep
  have hge : ∀ x, x ∈ L ++ R ++ D ++ mailbox_nodes m0 ++ mailbox_nodes m1 ++ held p0 ++
      held p1 → 6 ≤ x ∧ x + 1 < 1 + page_size capacity :=
    fun x hx => page_blocks_bounds 1 capacity x (hp.subset hx)
  simp only [remote_head, local_head, drain_head, mailbox, Bool.false_eq_true, ↓reduceIte,
    Nat.reduceAdd] at hr hl hd hm0 hm1
  cases who with
  | Owner =>
    cases op with
    | ORead =>
      fair_eval hturn hr hl hd hm0 hm1
      obtain ⟨rfl, rfl⟩ := hturn
      obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl rfl) (fun _ => nofun)
      exact progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
        ⟨rfl, rfl, fun hw => by fair_odist hw hm0 hm1⟩
    | OCAS old =>
      obtain rfl : D = [] := hop
      by_cases hc : R.headD 0 = old
      · subst hc
        fair_eval hturn hr hl hd hm0 hm1
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨rfl, rfl, hD⟩ := transition_detach hstep (by simp [csl_emissions]) rfl rfl
        subst D'
        cases R with
        | nil =>
          exact progress_idle _ _ _ _ _ _ _ _ _ (by fair_cells hr hm0 hm1)
            (by fair_cells hr hm0 hm1) (by fair_cells hr hm0 hm1)
            (by simp) (by simp) ⟨rfl, rfl, fun hw => by fair_odist hw hm0 hm1⟩
        | cons b R =>
          exact progress_move _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp)
            (by fair_phi hkind hm0 hm1)
      · fair_eval hturn hr hl hd hm0 hm1
        simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hturn
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl rfl) (fun _ => nofun)
        exact progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
          ⟨rfl, rfl, fun hw => by fair_odist hw hm0 hm1⟩
    | ODrain =>
      cases D with
      | nil =>
        fair_eval hturn hr hl hd hm0 hm1
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl rfl) (fun _ => nofun)
        exact progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
          ⟨rfl, rfl, fun hw => by fair_odist hw hm0 hm1⟩
      | cons b D =>
        obtain ⟨hnext, -⟩ := CD
        have hb := hge b (by simp)
        have hb0 : b ≠ 0 := by omega
        fair_eval hturn hr hl hd hm0 hm1
        simp only [hb0, hnext, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hturn
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨-, hD, rfl, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ :=
          transition_emit (tag := tag_reclaim) (b := b) (idx := count) hstep
            (by simp [csl_emissions]) (by decide)
        · cases hD
          by_cases hk : kind = tag_reclaim
          · subst hk
            exact progress_kind_event _ _ _ _ _ _ _ b count _ rfl rfl (by simp [csl_emissions])
          · exact progress_move _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp)
              (by fair_phi hkind hm0 hm1 hk)
        all_goals exact absurd h1 (by decide)
    | OOffer client =>
      obtain rfl : D = [] := hop
      cases client with
      | false =>
        by_cases hm : m0 = 0
        · subst hm
          cases L with
          | nil =>
            fair_eval hturn hr hl hd hm0 hm1
            obtain ⟨rfl, rfl⟩ := hturn
            obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl rfl) (fun _ => nofun)
            exact progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
              ⟨rfl, rfl, fun hw => by fair_odist hw hm0 hm1⟩
          | cons b L =>
            obtain ⟨hnext, -⟩ := CL
            have hb := hge b (by simp)
            have hb0 : b ≠ 0 := by omega
            fair_eval hturn hr hl hd hm0 hm1
            simp only [hb0, hnext, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hturn
            obtain ⟨rfl, rfl⟩ := hturn
            obtain ⟨h1, -⟩ | ⟨-, hL, rfl, rfl⟩ | ⟨h1, -⟩ :=
              transition_emit (tag := tag_alloc) (b := b) (idx := count) hstep
                (by simp [csl_emissions]) (by decide)
            · exact absurd h1 (by decide)
            · cases hL
              by_cases hk : kind = tag_alloc
              · subst hk
                exact progress_kind_event _ _ _ _ _ _ _ b count _ rfl rfl
                  (by simp [csl_emissions])
              · exact progress_move _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp)
                  (by fair_phi hkind hm0 hm1 hk)
            · exact absurd h1 (by decide)
        · fair_eval hturn hr hl hd hm0 hm1
          simp only [hm, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hturn
          obtain ⟨rfl, rfl⟩ := hturn
          obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl rfl) (fun _ => nofun)
          exact progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
            ⟨rfl, rfl, fun hw => by fair_odist hw hm0 hm1⟩
      | true =>
        by_cases hm : m1 = 0
        · subst hm
          cases L with
          | nil =>
            fair_eval hturn hr hl hd hm0 hm1
            obtain ⟨rfl, rfl⟩ := hturn
            obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl rfl) (fun _ => nofun)
            exact progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
              ⟨rfl, rfl, fun hw => by fair_odist hw hm0 hm1⟩
          | cons b L =>
            obtain ⟨hnext, -⟩ := CL
            have hb := hge b (by simp)
            have hb0 : b ≠ 0 := by omega
            fair_eval hturn hr hl hd hm0 hm1
            simp only [hb0, hnext, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hturn
            obtain ⟨rfl, rfl⟩ := hturn
            obtain ⟨h1, -⟩ | ⟨-, hL, rfl, rfl⟩ | ⟨h1, -⟩ :=
              transition_emit (tag := tag_alloc) (b := b) (idx := count) hstep
                (by simp [csl_emissions]) (by decide)
            · exact absurd h1 (by decide)
            · cases hL
              by_cases hk : kind = tag_alloc
              · subst hk
                exact progress_kind_event _ _ _ _ _ _ _ b count _ rfl rfl
                  (by simp [csl_emissions])
              · exact progress_move _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp)
                  (by fair_phi hkind hm0 hm1 hk)
            · exact absurd h1 (by decide)
        · fair_eval hturn hr hl hd hm0 hm1
          simp only [hm, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hturn
          obtain ⟨rfl, rfl⟩ := hturn
          obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl rfl) (fun _ => nofun)
          exact progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
            ⟨rfl, rfl, fun hw => by fair_odist hw hm0 hm1⟩
  | Remote0 =>
    cases p0 with
    | RPoll =>
      by_cases hm : m0 = 0
      · subst hm
        fair_eval hturn hr hl hd hm0 hm1
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl rfl) nofun
        refine progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
          ⟨rfl, rfl, rfl, fun hh => ?_⟩
        have := helpful_remote0 _ _ _ _ hh
        simp [remote_has_block, mbox, mboxh, mailbox, hm0, is_poll] at this
      · have hb := hge m0 (by simp [mailbox_nodes, hm])
        obtain ⟨v, hv⟩ := ai_backing_present 1 capacity h (m0 + 1) hback ⟨by omega, by omega⟩
        fair_eval hturn hr hl hd hm0 hm1
        simp only [hm, hv, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hturn
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl (by simp [csl_emissions])) nofun
        exact progress_move _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp)
          (by fair_phi hkind hm0 hm1)
    | RRead b =>
      fair_eval hturn hr hl hd hm0 hm1
      obtain ⟨rfl, rfl⟩ := hturn
      obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl rfl) nofun
      exact progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
        ⟨rfl, rfl, rfl, fun _ => by fair_rdist hr⟩
    | RLink b old =>
      have hb := hge b (by simp [held])
      obtain ⟨v, hv⟩ := ai_backing_present 1 capacity h b hback ⟨by omega, by omega⟩
      fair_eval hturn hr hl hd hm0 hm1
      simp only [hv, Option.some.injEq, Prod.mk.injEq] at hturn
      obtain ⟨rfl, rfl⟩ := hturn
      obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl (by simp [csl_emissions])) nofun
      exact progress_idle _ _ _ _ _ _ _ _ _ (by fair_cells hr hm0 hm1)
        (by fair_cells hr hm0 hm1) (by fair_cells hr hm0 hm1)
        (by simp) (by simp) ⟨rfl, rfl, rfl, fun _ => by fair_rdist hr⟩
    | RCAS b old =>
      by_cases hc : R.headD 0 = old
      · subst hc
        fair_eval hturn hr hl hd hm0 hm1
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, hR, rfl⟩ :=
          transition_emit (tag := tag_retire) (b := b) (idx := count) hstep
            (by simp [csl_emissions]) (by decide)
        · exact absurd h1 (by decide)
        · exact absurd h1 (by decide)
        · subst R'
          by_cases hk : kind = tag_retire
          · subst hk
            exact progress_kind_event _ _ _ _ _ _ _ b count _ rfl rfl (by simp [csl_emissions])
          · exact progress_move _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp)
              (by fair_phi hkind hm0 hm1 hk)
      · fair_eval hturn hr hl hd hm0 hm1
        simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hturn
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨rfl, rfl, rfl⟩ :=
          transition_silent hstep (.inr ⟨b, count, by simp [csl_emissions]⟩) nofun
        exact progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
          ⟨rfl, rfl, rfl, fun _ => by fair_rdist hr⟩
  | Remote1 =>
    cases p1 with
    | RPoll =>
      by_cases hm : m1 = 0
      · subst hm
        fair_eval hturn hr hl hd hm0 hm1
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl rfl) nofun
        refine progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
          ⟨rfl, rfl, rfl, fun hh => ?_⟩
        have := helpful_remote1 capacity _ _ _ _ hcap hview_s hh
        simp [remote_has_block, mbox, mboxh, mailbox, hm1, is_poll] at this
      · have hb := hge m1 (by simp [mailbox_nodes, hm])
        obtain ⟨v, hv⟩ := ai_backing_present 1 capacity h (m1 + 1) hback ⟨by omega, by omega⟩
        fair_eval hturn hr hl hd hm0 hm1
        simp only [hm, hv, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hturn
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl (by simp [csl_emissions])) nofun
        exact progress_move _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp)
          (by fair_phi hkind hm0 hm1)
    | RRead b =>
      fair_eval hturn hr hl hd hm0 hm1
      obtain ⟨rfl, rfl⟩ := hturn
      obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl rfl) nofun
      exact progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
        ⟨rfl, rfl, rfl, fun _ => by fair_rdist hr⟩
    | RLink b old =>
      have hb := hge b (by simp [held])
      obtain ⟨v, hv⟩ := ai_backing_present 1 capacity h b hback ⟨by omega, by omega⟩
      fair_eval hturn hr hl hd hm0 hm1
      simp only [hv, Option.some.injEq, Prod.mk.injEq] at hturn
      obtain ⟨rfl, rfl⟩ := hturn
      obtain ⟨rfl, rfl, rfl⟩ := transition_silent hstep (.inl (by simp [csl_emissions])) nofun
      exact progress_idle _ _ _ _ _ _ _ _ _ (by fair_cells hr hm0 hm1)
        (by fair_cells hr hm0 hm1) (by fair_cells hr hm0 hm1)
        (by simp) (by simp) ⟨rfl, rfl, rfl, fun _ => by fair_rdist hr⟩
    | RCAS b old =>
      by_cases hc : R.headD 0 = old
      · subst hc
        fair_eval hturn hr hl hd hm0 hm1
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, hR, rfl⟩ :=
          transition_emit (tag := tag_retire) (b := b) (idx := count) hstep
            (by simp [csl_emissions]) (by decide)
        · exact absurd h1 (by decide)
        · exact absurd h1 (by decide)
        · subst R'
          by_cases hk : kind = tag_retire
          · subst hk
            exact progress_kind_event _ _ _ _ _ _ _ b count _ rfl rfl (by simp [csl_emissions])
          · exact progress_move _ _ _ _ _ _ _ _ _ _ _ _ (by simp) (by simp)
              (by fair_phi hkind hm0 hm1 hk)
      · fair_eval hturn hr hl hd hm0 hm1
        simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hturn
        obtain ⟨rfl, rfl⟩ := hturn
        obtain ⟨rfl, rfl, rfl⟩ :=
          transition_silent hstep (.inr ⟨b, count, by simp [csl_emissions]⟩) nofun
        exact progress_idle _ _ _ _ _ _ _ _ _ rfl rfl rfl (by simp) (by simp)
          ⟨rfl, rfl, rfl, fun _ => by fair_rdist hr⟩



/-- Every observation kind of the allocator recurs under every fair policy, for every page
capacity, from the real source program. -/
theorem allocator_agaf_fair (sch : Scheduler) [FairScheduler sch] (capacity : Nat) (ctx : Ctx)
    (c kind kb : Nat) (st : sch.sched_state) :
    0 < capacity → kind ∈ [tag_alloc, tag_retire, tag_reclaim] →
    entails (AG (AF (visWₜ (fair_obs (fresh_kind kind kb)))))
      (run_fair sch (allocator_program capacity) st (managed_empty, (ctx, c))) .pure := by
  intro hcap hkind
  rw [proper_entails_meq _ (run_fair_allocator_initialized sch capacity st ctx c)]
  refine agaf_emit_list _ _ _ _ .pure ?_
  obtain ⟨L0, R0, D0, hview0⟩ := initial_state_inv capacity c
  exact agaf_pool_simulation_fair sh sch actor_of_slot slot_of_actor slot_of_actor_of_slot
    (turn 1) (allocator_pool 1) state_agrees (allocator_inv 1 capacity)
    (allocator_simulation 1 capacity) (Prod.fst : AG_ghost → AState) (InvG capacity)
    (rankG kind kb) rank3 targetG (fresh_kind kind kb) rank3_wf
    (fun ⟨_, L, R, D⟩ hg => ⟨L, R, D, hg⟩) (allocator_fair_turn capacity kind kb hcap hkind)
    (initial_state capacity c, (L0, (R0, D0))) (source_pool0 1) _ none st _ hview0
    ⟨heq_refl _, heq_refl _, rfl⟩ (pool_equ_guard _ _ (source_pool0_initial capacity c))
    (after_logs_not_done _ .pure)

/-! ## ABA robustness

Remote 1 snapshots head 6 and prepares to publish block 8 with link 6; before its CAS commits,
block 6 is reclaimed, reallocated and retired again, so the head is once more 6. The stale
snapshot still matches, and the successful CAS loses nothing: the remote list is exactly
`[8, 6]`. -/

def aba_logs : List (CSLObs (Nat × Nat)) :=
  ((List.range aba_script.length).map fun k =>
    (allocator_execution 2 0 (fun j => aba_script.getD j Owner)).emitted k).flatten

/-- The ABA logs are the replay table's observations. -/
private theorem aba_logs_table : aba_logs = ((List.range' 0 23).map (aba_event 0)).flatten := by
  let e := allocator_execution 2 0 (fun j => aba_script.getD j Owner)
  have hv : allocator_valid 2 0 e := allocator_execution_valid 2 0 _
  have h0 : e.states 0 = initial_state 2 0 := hv.1
  have he := execution_run_turns (turn 1) (fun xs => xs) _ e 0 23 hv
  have hs : (List.range' 0 23).map e.selected = aba_script.take 23 := rfl
  rw [hs, h0, aba_run 0 23 (Nat.le_refl _), Option.some.injEq, Prod.mk.injEq] at he
  rw [aba_logs, List.range_eq_range']
  exact he.2.symm

theorem aba_user_emissions : csl_emissions aba_logs =
    [stamp (0, 6) 0, stamp (0, 8) 1, stamp (1, 6) 2, stamp (2, 6) 3,
     stamp (0, 6) 4, stamp (1, 6) 5, stamp (1, 8) 6] := by
  rw [aba_logs_table]; rfl

theorem aba_snapshot_survives_reuse :
    (run_turns (turn 1) (fun xs => xs) aba_before_reuse (initial_state 2 0)).map
        (fun result => (result.1.owner_state, result.1.remote0_state, result.1.remote1_state)) =
      some (ORead, RPoll, RCAS 8 6) ∧
    (run_turns (turn 1) (fun xs => xs) aba_before_commit (initial_state 2 0)).map
        (fun result => (result.1.owner_state, result.1.remote0_state, result.1.remote1_state)) =
      some (ORead, RPoll, RCAS 8 6) ∧
    (run_turns (turn 1) (fun xs => xs) aba_before_reuse (initial_state 2 0)).map
        (fun result => [result.1.aheap 1]) = some [some 6] ∧
    (run_turns (turn 1) (fun xs => xs) aba_before_commit (initial_state 2 0)).map
        (fun result => [result.1.aheap 1]) = some [some 6] := by
  rw [show aba_before_reuse = aba_script.take 12 from rfl,
    show aba_before_commit = aba_script.take 22 from rfl, aba_run 0 12 (by decide),
    aba_run 0 22 (by decide)]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem aba_run_no_loss : ∃ last,
    run_turns (turn 1) (fun xs => xs) aba_script (initial_state 2 0) = some (last, aba_logs) ∧
    allocator_inv 1 2 last ∧
    last.aheap (remote_head 1) = some 8 ∧ linked (fun a next => last.aheap a = some next) [8, 6] 0 ∧
    [8, 6].Nodup ∧ [8, 6].Perm (page_blocks 1 2) := by
  have hrun : run_turns (turn 1) (fun xs => xs) aba_script (initial_state 2 0) =
      some (aba_state 0 23, aba_logs) := by
    rw [aba_logs_table]; exact aba_run 0 23 (Nat.le_refl _)
  refine ⟨aba_state 0 23, hrun, run_turns_preserves_inv (turn 1) (fun xs => xs)
    (allocator_inv 1 2) (turn_preserves_inv 1 2) aba_script _ _ _ (initial_state_inv 2 0) hrun,
    by decide, ⟨by decide, by decide, trivial⟩, by decide, by decide⟩


theorem aba_actual_source_no_loss : ∃ last labels residual,
    run_turns (turn 1) (fun xs => xs) aba_script (initial_state 2 0) = some (last, aba_logs) ∧
    allocator_inv 1 2 last ∧
    last.aheap (remote_head 1) = some 8 ∧ linked (fun a next => last.aheap a = some next) [8, 6] 0 ∧
    label_logs labels = new_page_logs 1 2 managed_empty ++ aba_logs ∧ label_taus labels = 23 ∧
    FiniteSteps (run_nd (allocator_program 2) (managed_empty, (([] : Ctx), 0))) labels residual ∧
    residual ~ (model_nd 2 actor_of_slot (turn 1) last :
      ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  obtain ⟨last, hrun, hinv, hhead, hchain, -, -⟩ := aba_run_no_loss
  obtain ⟨labels, residual, -, hlogs, htaus, hsteps, htail⟩ :=
    run_turns_realizes_source 2 [] 0 aba_script last aba_logs hrun
  exact ⟨last, labels, residual, hrun, hinv, hhead, hchain, hlogs, htaus, hsteps, htail⟩

-- Not ported: the `Local Ltac`s `fair_heap`, `fair_cells`, `fair_idle_owner`,
-- `fair_idle_remote`, `fair_inv`, `fair_odist`, `fair_rdist`, `fair_phi` (replaced by the macros
-- `fair_eval`, `fair_cells`, `fair_odist`, `fair_rdist`, `fair_phi` and the ownership inversion
-- lemmas `transition_silent`, `transition_detach`, `transition_emit`); the `Section ABASafety`
-- `Let`s are the public defs `aba_before_reuse`, `aba_before_commit`, `aba_script` (in
-- `Examples.CSL.Allocator.Replay`) and `aba_logs` (their statements mention them), the
-- `vm_compute` witness is the replay state `Replay.aba_state 0 23`.

end Examples.CSL.Allocator.Liveness
