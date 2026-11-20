/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.Asep
public import Lang.CoCSL.Owned
public import Examples.CSL.Frame.Shared

/-!
# Transient active-separation regression

Parent emits `(2,1)` and `(2,0)` and returns; the unfocused Child is then selected and emits
`(1,1)`. Each lineage eventually reaches its own endpoint, but the two endpoints never hold at the
same separated state, so no global path reaches them jointly
(← `examples/CSL/Frame/Active.v`, module `TransientActiveRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Active.TransientActiveRegression
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm Tisl.Notation CoCSL
open Examples.CSL.Frame.Shared

def child : CProg Unit := .emit 1 1

def parent : CProg Unit :=
  .bind (.emit 2 1) fun _ => .bind (.emit 2 0) fun _ => .ret ()

def cfg : OwnedCfg := init_owned child parent (region 1 3) (region 2 5) [] 0

def initial : AsepState := { cfg := cfg, global := .pure, loc := fun _ => .pure }

def emit_head (payload : Nat × Nat) (k : Thread sE Bn) : Thread sE Bn :=
  .vis (E := CEff) (.inr (.inr (.inr (.inr payload)))) fun _ => k

def tc : Thread sE Bn := emit_head (1, 1) (pure ⟨⟩)
def tp1 : Thread sE Bn := emit_head (2, 0) (pure ⟨⟩)
def tp0 : Thread sE Bn := emit_head (2, 1) tp1

theorem child_head : denote child = tc := source_raw_emit_head 1 1 _

theorem parent_head : denote parent = tp0 := by
  simp only [denote, parent, source_raw_bind, source_raw_emit_head, source_raw_ret]; rfl

theorem initial_ok : asep_state_ok initial :=
  ⟨admissible_active_erasable _ _ _ _ _ _ (admissible_regions _ _ _ _ _ _ _ _ (by decide)
      trivial ⟨trivial, fun _ => ⟨trivial, fun _ => trivial⟩⟩
      (by simp [addr_ok, child]) (by simp [addr_ok, parent])),
    .pure, fun _ => .pure⟩

/-- The seven finite phases record existing owned actions, not a scheduler. In particular, `P3`
is the sole unfocused selection frontier. -/
inductive phase
  | P0 | P1 | P2 | P3 | P4 | P5 | P6
  deriving DecidableEq

def c0 : OwnedCfg := init_owned_threads tc tp0 (region 1 3) (region 2 5) [] 0
def c1 : OwnedCfg := set_pool (emit_cfg c0 .parent (2, 1))
  (mk_pool 2 #v[tc, tp1] #v[.child, .parent] (some 1))
def c2 : OwnedCfg := set_pool (emit_cfg c1 .parent (2, 0))
  (mk_pool 2 #v[tc, pure ⟨⟩] #v[.child, .parent] (some 1))
def c3 : OwnedCfg := set_pool c2 (mk_pool 1 #v[tc] #v[.child] none)
def c4 : OwnedCfg := set_pool c3 (mk_pool 1 #v[tc] #v[.child] (some 0))
def c5 : OwnedCfg := set_pool (emit_cfg c4 .child (1, 1))
  (mk_pool 1 #v[pure ⟨⟩] #v[.child] (some 0))
def c6 : OwnedCfg := set_pool c5 (mk_pool 0 #v[] #v[] none)

def phase_cfg : phase → OwnedCfg
  | .P0 => c0 | .P1 => c1 | .P2 => c2 | .P3 => c3 | .P4 => c4 | .P5 => c5 | .P6 => c6

def next : phase → phase
  | .P0 => .P1 | .P1 => .P2 | .P2 => .P3 | .P3 => .P4 | .P4 => .P5 | .P5 => .P6 | .P6 => .P6

def phase_action : phase → OwnedAction
  | .P0 => act .parent (.emit (2, 1) 0)
  | .P1 => act .parent (.emit (2, 0) 1)
  | .P2 => act .parent .ret
  | .P3 => act .child .select
  | .P4 => act .child (.emit (1, 1) 2)
  | .P5 | .P6 => act .child .ret

def emission (p : Nat × Nat) (n : Nat) : World (writerE (CSLObs (Nat × Nat))) :=
  .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.emit (stamp p n)) ⟨⟩

def local_child : phase → World (writerE (CSLObs (Nat × Nat)))
  | .P5 | .P6 => emission (1, 1) 0
  | _ => .pure

def local_parent : phase → World (writerE (CSLObs (Nat × Nat)))
  | .P0 => .pure
  | .P1 => emission (2, 1) 0
  | _ => emission (2, 0) 1

def global_world : phase → World (writerE (CSLObs (Nat × Nat)))
  | .P0 => .pure
  | .P1 => emission (2, 1) 0
  | .P5 | .P6 => emission (1, 1) 2
  | _ => emission (2, 0) 1

def phase_view (ph : phase) : AsepState where
  cfg := phase_cfg ph
  global := global_world ph
  loc := fun | .child => local_child ph | .parent => local_parent ph

theorem cfg_equ_c0 : owned_equ cfg c0 := by
  rw [cfg, init_owned, child_head, parent_head]; exact owned_equ_Equivalence.refl _

theorem replace_equ (c : OwnedCfg) (n : Nat) (v : Pool sE Bn n) (g : Vector Side n)
    (f : Option (Fin n)) (j : Fin n) (t u : Thread sE Bn) :
    t = u →
    owned_equ (set_pool c (mk_pool n (v.set j t) g f)) (set_pool c (mk_pool n (v.set j u) g f)) :=
  fun H => H ▸ owned_equ_Equivalence.refl _

theorem finite_step (ph : phase) (a : OwnedAction) (c' : OwnedCfg) :
    owned_step (phase_cfg ph) a c' →
    ph ≠ .P6 ∧ a = phase_action ph ∧ owned_equ c' (phase_cfg (next ph)) := by
  intro H
  cases ph
  · obtain ⟨k, kind, y, d, Hk, Hp, rfl, rfl⟩ :=
      (focus_step_head_prim c0 1 _ _ 1 _ (fun _ => tp1) 0 a c' rfl).1
        ((owned_step_focus c0 1 #v[tc, tp0] #v[.child, .parent] 1 a c' rfl).1 H)
    cases Hp
    exact ⟨nofun, rfl, replace_equ _ _ _ _ _ _ _ _ (Hk _)⟩
  · obtain ⟨k, kind, y, d, Hk, Hp, rfl, rfl⟩ :=
      (focus_step_head_prim c1 1 _ _ 1 _ (fun _ => pure ⟨⟩) 0 a c' rfl).1
        ((owned_step_focus c1 1 #v[tc, tp1] #v[.child, .parent] 1 a c' rfl).1 H)
    cases Hp
    exact ⟨nofun, rfl, replace_equ _ _ _ _ _ _ _ _ (Hk _)⟩
  · obtain ⟨rfl, rfl⟩ := (focus_step_head_ret c2 1 #v[tc, pure ⟨⟩] _ 1 0 a c' rfl).1
      ((owned_step_focus c2 1 #v[tc, pure ⟨⟩] #v[.child, .parent] 1 a c' rfl).1 H)
    refine ⟨nofun, rfl, ?_⟩
    rw [vector_remove_pair, vector_remove_pair]; exact owned_equ_Equivalence.refl _
  · obtain ⟨j, rfl, rfl⟩ := (owned_step_sel c3 0 #v[tc] #v[.child] a c' rfl).1 H
    obtain rfl := fin1_eq j
    exact ⟨nofun, rfl, owned_equ_Equivalence.refl _⟩
  · obtain ⟨k, kind, y, d, Hk, Hp, rfl, rfl⟩ :=
      (focus_step_head_prim c4 0 _ _ 0 _ (fun _ => pure ⟨⟩) 0 a c' rfl).1
        ((owned_step_focus c4 0 #v[tc] #v[.child] 0 a c' rfl).1 H)
    cases Hp
    exact ⟨nofun, rfl, replace_equ _ _ _ _ _ _ _ _ (Hk _)⟩
  · obtain ⟨rfl, rfl⟩ := (focus_step_head_ret c5 0 #v[pure ⟨⟩] _ 0 0 a c' rfl).1
      ((owned_step_focus c5 0 #v[pure ⟨⟩] #v[.child] 0 a c' rfl).1 H)
    refine ⟨nofun, rfl, ?_⟩
    rw [vector_remove_single, vector_remove_single]; exact owned_equ_Equivalence.refl _
  · exact H.elim

theorem finite_step_exists (ph : phase) : ph ≠ .P6 →
    owned_step (phase_cfg ph) (phase_action ph) (phase_cfg (next ph)) := by
  intro Hlast
  cases ph
  · exact (owned_step_focus c0 1 #v[tc, tp0] #v[.child, .parent] 1 _ _ rfl).2
      ((focus_step_head_prim c0 1 _ _ 1 _ (fun _ => tp1) 0 _ _ rfl).2
        ⟨fun _ => tp1, _, _, emit_cfg c0 .parent (2, 1), fun _ => rfl, rfl, rfl, rfl⟩)
  · exact (owned_step_focus c1 1 #v[tc, tp1] #v[.child, .parent] 1 _ _ rfl).2
      ((focus_step_head_prim c1 1 _ _ 1 _ (fun _ => pure ⟨⟩) 0 _ _ rfl).2
        ⟨fun _ => pure ⟨⟩, _, _, emit_cfg c1 .parent (2, 0), fun _ => rfl, rfl, rfl, rfl⟩)
  · exact (owned_step_focus c2 1 #v[tc, pure ⟨⟩] #v[.child, .parent] 1 _ _ rfl).2
      ((focus_step_head_ret c2 1 _ _ 1 0 _ _ rfl).2
        ⟨rfl, by rw [vector_remove_pair, vector_remove_pair]; rfl⟩)
  · exact (owned_step_sel c3 0 #v[tc] #v[.child] _ _ rfl).2 ⟨0, rfl, rfl⟩
  · exact (owned_step_focus c4 0 #v[tc] #v[.child] 0 _ _ rfl).2
      ((focus_step_head_prim c4 0 _ _ 0 _ (fun _ => pure ⟨⟩) 0 _ _ rfl).2
        ⟨fun _ => pure ⟨⟩, _, _, emit_cfg c4 .child (1, 1), fun _ => rfl, rfl, rfl, rfl⟩)
  · exact (owned_step_focus c5 0 #v[pure ⟨⟩] #v[.child] 0 _ _ rfl).2
      ((focus_step_head_ret c5 0 _ _ 0 0 _ _ rfl).2
        ⟨rfl, by rw [vector_remove_single, vector_remove_single]; rfl⟩)
  · exact absurd rfl Hlast

private theorem phase_view_advance (ph : phase) : ph ≠ .P6 →
    phase_view (next ph) =
      asep_advance (phase_view ph) (phase_action ph) (phase_cfg (next ph)) := by
  intro Hlast
  cases ph <;> first
    | exact absurd rfl Hlast
    | (simp only [phase_view, asep_advance]
       congr 1
       funext i
       cases i <;> rfl)

theorem phase_view_step (ph : phase) : ph ≠ .P6 →
    asep_step (phase_view ph) (phase_action ph) (phase_view (next ph)) :=
  fun Hlast => ⟨finite_step_exists ph Hlast, phase_view_advance ph Hlast⟩

theorem phase_advance (c : OwnedCfg) (ph : phase) : owned_equ c (phase_cfg ph) → ph ≠ .P6 →
    ∃ c', owned_step c (phase_action ph) c' ∧ owned_equ c' (phase_cfg (next ph)) := by
  intro E Hlast
  obtain rfl := owned_equ_eq E
  exact ⟨_, finite_step_exists ph Hlast, owned_equ_Equivalence.refl _⟩

theorem concrete_action_order : ∃ d1 d2 d3 d4 d5 d6,
    owned_step cfg (act .parent (.emit (2, 1) 0)) d1 ∧
    owned_step d1 (act .parent (.emit (2, 0) 1)) d2 ∧
    owned_step d2 (act .parent .ret) d3 ∧
    owned_step d3 (act .child .select) d4 ∧
    owned_step d4 (act .child (.emit (1, 1) 2)) d5 ∧
    owned_step d5 (act .child .ret) d6 := by
  obtain ⟨d1, H1, E1⟩ := phase_advance cfg .P0 cfg_equ_c0 nofun
  obtain ⟨d2, H2, E2⟩ := phase_advance d1 .P1 E1 nofun
  obtain ⟨d3, H3, E3⟩ := phase_advance d2 .P2 E2 nofun
  obtain ⟨d4, H4, E4⟩ := phase_advance d3 .P3 E3 nofun
  obtain ⟨d5, H5, E5⟩ := phase_advance d4 .P4 E4 nofun
  obtain ⟨d6, H6, -⟩ := phase_advance d5 .P5 E5 nofun
  exact ⟨d1, d2, d3, d4, d5, d6, H1, H2, H3, H4, H5, H6⟩

def phase_inv (s : AsepState) : Prop := ∃ ph,
  owned_equ s.cfg (phase_cfg ph) ∧
  s.loc .child = local_child ph ∧
  s.loc .parent = local_parent ph ∧
  s.global = global_world ph

theorem phase_inv_init : phase_inv initial :=
  ⟨.P0, cfg_equ_c0, rfl, rfl, rfl⟩

/-- `phase_inv` pins the whole state (`owned_equ` is equality). -/
private theorem phase_inv_view (s : AsepState) (ph : phase) :
    owned_equ s.cfg (phase_cfg ph) → s.loc .child = local_child ph →
    s.loc .parent = local_parent ph → s.global = global_world ph → s = phase_view ph := by
  obtain ⟨c, g, l⟩ := s
  intro E EC EP EW
  obtain rfl := owned_equ_eq E
  simp only [phase_view]
  congr 1
  funext i
  cases i
  · exact EC
  · exact EP

theorem phase_inv_closed : asep_closed phase_inv := by
  rintro s a s' - ⟨ph, E, EC, EP, EW⟩ ⟨Hs, Eu⟩
  obtain rfl := phase_inv_view s ph E EC EP EW
  obtain ⟨Hlast, rfl, En⟩ := finite_step ph a _ Hs
  rw [owned_equ_eq En, ← phase_view_advance ph Hlast] at Eu
  subst Eu
  exact ⟨next ph, owned_equ_Equivalence.refl _, rfl, rfl, rfl⟩

def seen (payload : Nat × Nat) (w : World (writerE (CSLObs (Nat × Nat)))) : Prop :=
  match w with
  | .obs (CSLObs.emit e) _ => e.value = payload
  | _ => False

def endpoint (payload : Nat × Nat) :
    ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig) → World (writerE (CSLObs (Nat × Nat))) →
      Prop :=
  entails (.now (seen payload) : TiclL (writerE (CSLObs (Nat × Nat))))

theorem phase_inv_inv (s : AsepState) : phase_inv s → ∃ ph,
    owned_equ s.cfg (phase_cfg ph) ∧
    s.loc .child = local_child ph ∧
    s.loc .parent = local_parent ph ∧
    s.global = global_world ph ∧
    (endpoint (1, 1) (owned_interp (project .child s.cfg)) (s.loc .child) ↔
      ph = .P5 ∨ ph = .P6) ∧
    (endpoint (2, 1) (owned_interp (project .parent s.cfg)) (s.loc .parent) ↔ ph = .P1) := by
  rintro ⟨ph, E, EC, EP, EW⟩
  refine ⟨ph, E, EC, EP, EW, ?_, ?_⟩
  · simp only [endpoint, ticl_now, EC]
    cases ph <;> simp [local_child, seen, emission, stamp] <;> exact .obs _ _
  · simp only [endpoint, ticl_now, EP]
    cases ph <;> simp [local_parent, seen, emission, stamp] <;> exact .obs _ _

theorem parent_progress_remembered (s : AsepState) :
    phase_inv s →
    endpoint (1, 1) (owned_interp (project .child s.cfg)) (s.loc .child) →
    s.cfg.count .parent = 2 ∧
    entails (.now fun w => w = emission (2, 0) 1 : TiclL (writerE (CSLObs (Nat × Nat))))
      (owned_interp (project .parent s.cfg)) (s.loc .parent) ∧
    ¬ endpoint (2, 1) (owned_interp (project .parent s.cfg)) (s.loc .parent) := by
  intro Hinv Hchild
  obtain ⟨ph, E, -, EP, -, HC, HP⟩ := phase_inv_inv s Hinv
  have Hph := HC.1 Hchild
  refine ⟨?_, ?_, fun Hparent => ?_⟩
  · rw [owned_equ_eq E]; rcases Hph with rfl | rfl <;> rfl
  · rw [ticl_now, EP]
    rcases Hph with rfl | rfl <;> exact ⟨rfl, .obs _ _⟩
  · rcases Hph with rfl | rfl <;> cases HP.1 Hparent

theorem initial_local_state (i : Side) (t : Thread sE Bn) (h : ManagedHeap) (ctx : Ctx)
    (base : Nat) (focused : Bool) :
    joined_state (init_local_thread i t h ctx base focused) = (h, (ctx, base)) := by
  cases i <;> simp only [joined_state, joined_heap, global_count, init_local_thread, side_only,
    side_eqb, ite_true, ite_false, Bool.false_eq_true, Nat.add_zero]
  · exact congrArg (·, _) (managed_heap_ext _ _ (pop_emp_r _ (pdef_emp_r _)))
  · exact congrArg (·, _) (managed_heap_ext _ _ (peq_trans _ _ _ (pop_comm _ _ (pdef_emp _))
      (pop_emp_r _ (pdef_emp_r _))))

theorem child_local_af :
    entails (AF (.now (seen (1, 1))) : TiclL (writerE (CSLObs (Nat × Nat))))
      (owned_interp (project .child cfg)) .pure := by
  refine (proper_entails_meq _ (owned_interp_equ _ _
    (project_init_child child parent (region 1 3) (region 2 5) [] 0))).2 ?_
  show entails _ (interp_schedule_nd sh 1 #v[denote child] none
    (joined_state (init_local_thread .child (denote child) (region 1 3) [] 0 false))) _
  rw [initial_local_state]
  refine (au_csl_nd_select 0 (region 1 3) [] 0 #v[denote child] .pure _ _).2
    (.inr ⟨⟨trivial, .pure⟩, fun j => ?_⟩)
  obtain rfl := fin1_eq j
  show entails _ (interp_schedule_nd sh 1 ((#v[pure ⟨⟩] : Pool sE Bn 1).set 0
    (denote_flow (.emit 1 1) >>= fun _ => pure ⟨⟩)) (some 0) (own 1 3 [] 0)) _
  refine (proper_entails_meq _ (interp_nd_source_emit_log 0 #v[pure ⟨⟩] 0 1 1
    (fun _ => pure ⟨⟩) (region 1 3) [] 0)).2 ?_
  exact af_log .pure (.matchA ⟨rfl, .obs _ _⟩)

theorem parent_local_af :
    entails (AF (.now (seen (2, 1))) : TiclL (writerE (CSLObs (Nat × Nat))))
      (owned_interp (project .parent cfg)) .pure := by
  refine (proper_entails_meq _ (owned_interp_equ _ _
    (project_init_parent child parent (region 1 3) (region 2 5) [] 0))).2 ?_
  show entails _ (interp_schedule_nd sh 1 ((#v[pure ⟨⟩] : Pool sE Bn 1).set 0
    (denote_flow parent >>= fun _ => pure ⟨⟩)) (some 0)
    (joined_state (init_local_thread .parent (denote parent) (region 2 5) [] 0 true))) _
  rw [initial_local_state]
  refine (congrArg (fun t => entails _ t _) (interp_nd_source_bind 0 #v[pure ⟨⟩] 0 (.emit 2 1)
    (fun _ => .bind (.emit 2 0) fun _ => .ret ()) (fun _ => pure ⟨⟩) (region 2 5, ([], 0)))).mpr ?_
  refine (proper_entails_meq _ (interp_nd_source_emit_log 0 #v[pure ⟨⟩] 0 2 1 _
    (region 2 5) [] 0)).2 ?_
  exact af_log .pure (.matchA ⟨rfl, .obs _ _⟩)

theorem no_current_pair (s : AsepState) :
    ¬ asep_at phase_inv (endpoint (1, 1)) (endpoint (2, 1)) s := by
  intro Hinv
  obtain ⟨-, -, Hphase, HC, HP⟩ := asep_at_inv _ _ _ s Hinv
  obtain ⟨ph, -, -, -, -, HCphase, HPphase⟩ := phase_inv_inv s Hphase
  obtain rfl := HPphase.1 HP
  rcases HCphase.1 HC with h | h <;> cases h

theorem separated_endpoint_impossible (t : AsepTree) (w : AsepWorld) :
    ¬ asep_sat phase_inv (endpoint (1, 1)) (endpoint (2, 1)) t w := by
  intro Hsat
  obtain ⟨s, -, -, Hok, -, HI, HC, HP⟩ := asep_sat_inv _ _ _ t w Hsat
  exact no_current_pair s (asep_at_intro _ _ _ s Hok HI HC HP)

theorem no_global_ef_separated_transient_endpoints :
    ¬ Euc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (asep_sat phase_inv (endpoint (1, 1)) (endpoint (2, 1)))
      (owned_interp cfg) .pure := by
  intro H
  obtain ⟨t, w, HE⟩ := euc_endpoint_exists H
  exact separated_endpoint_impossible t w HE

end Examples.CSL.Frame.Active.TransientActiveRegression
