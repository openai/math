import OAI.Geometry.Hirsch.Leaves

noncomputable section

open Set Filter

namespace OAI.Geometry.Hirsch.Layer

variable {I : Type} {N B L V C h : ℕ} {code : Bundles L V} {ep : Episodes N}
  (times : Times ep B)

structure Level (I : Type) (code : Bundles L V) (C h k : ℕ) where
  par : Parameters code
  size : ℝ
  positive : 0 < size
  sizeEq : size = if k = 0 then 1/2 else par.allow
  shift : Shift times.time (Times.group L k) size
  bend : k < h → 0 < shift.bend
  top : k = h → shift.bend = 0
  panel : ∀ i : I, Panel I B V i
  count : ∀ i, Fintype.card (panel i).Row ≤ Plate.budget code C * N * B^2
  leaf : k = 0 → ∀ i t, (panel i).Leaf (times.time t) (shift.val t) t.2
  child : Probe N B → ℝ
  data : 0 < k → Probe N B → SampleData par
  childEq : ∀ hk t, (data hk t).child = child t
  internal : ∀ hk i t, (panel i).Internal (times.time t) (shift.val t) t.2 (data hk t)

namespace Level

variable [NeZero N] [NeZero B] [NeZero L] {k : ℕ}

omit [NeZero N] [NeZero B] [NeZero L] in
theorem default_par (code : Bundles L V) : Nonempty (Parameters code) := by
  let atlas : Atlas code (fun _ : Empty => 0) (fun _ => 0) Empty.elim 0 :=
    ⟨Empty.elim,fun t => t.elim,fun t => t.elim,fun t => t.elim,fun t => t.elim⟩
  let cfg : Setup atlas :=
    ⟨Empty.elim,Empty.elim,4,1,Empty.elim,one_pos,by norm_num,fun t => t.elim,fun t => t.elim⟩
  exact ⟨(Classical.choice cfg.result).par⟩

omit [NeZero L] in
theorem bottom (hh : 0 < h) : Nonempty (Level times I code C h 0) := by
  obtain ⟨A,hA,high⟩ := times.penalty_high
  obtain ⟨a,ha,hs⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (eventually_all.mpr (times.penalty_patch L (R := 1/400) (by norm_num) hA.le))).exists
  let sh : Shift times.time (Times.group L 0) (1/2) :=
    ⟨times.carrier L 0,a,1/400,ha,by norm_num,by norm_num⟩
  refine ⟨{
    par := Classical.choice (default_par code), size := 1/2, positive := by norm_num, sizeEq := by simp,
    shift := sh, bend := fun _ => by norm_num [sh], top := fun he => by omega,
    panel := fun i => leafPanel hs i, count := ?_, leaf := ?_, child := 0,
    data := fun hk => (by omega), childEq := fun hk => (by omega), internal := fun hk => (by omega) }⟩
  · intro i
    change Fintype.card (Probe N B × Index B V) ≤ _
    simp only [Probe,Index,Forest.Position,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_option]
    calc
      _ ≤ N*B*((2*B)*(2*V)) := by gcongr; have := NeZero.pos B; omega
      _ = 4*V*N*B^2 := by ring
      _ ≤ _ := by gcongr; unfold Plate.budget; omega
  · intro _ i t
    apply leaf_panel
    · change times.penalty A t.2 t + sh.val t < _
      simp [Times.penalty]
    · intro d hd
      exact add_lt_add_left (high d t hd) _

variable {times}

def Follows (prev : Level times I code C h k) (next : Level times I code C h (k+1)) :=
  next.child = prev.shift.val ∧ 10*next.par.delta < prev.size

theorem advance (prev : Level times I code C h k) (hk : k < h)
    (atlas : Atlas code times.time (Times.group L (k+1)) (Times.site L k) C) :
    ∃ next, prev.Follows next := by
  obtain ⟨cfg,hg,hc,hm⟩ := compatible atlas times.injective times.unit (Times.link L k)
    prev.positive prev.shift (prev.bend hk)
  obtain ⟨res⟩ := cfg.result
  let R := if k+1 = h then 0 else res.par.allow/200
  have hp := res.par.allow_pos
  have hr : 0 ≤ R := by unfold R; split <;> positivity
  obtain ⟨a,ha,plate⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (res.plate (times.carrier L (k+1)) hg hr)).exists
  let sh : Shift times.time (Times.group L (k+1)) res.par.allow :=
    ⟨times.carrier L (k+1),a,R,ha,hr,by unfold R; split <;> linarith⟩
  let next : Level times I code C h (k+1) := {
    par := res.par, size := res.par.allow, positive := hp, sizeEq := by simp,
    shift := sh, bend := fun hh => by simp [sh,R,hh.ne,hp], top := fun hh => by simp [sh,R,hh],
    panel := plate.panel, count := plate.rows, leaf := fun he => by omega,
    child := cfg.child, data := fun _ => res.data, childEq := fun _ => res.child,
    internal := fun _ => plate.internal }
  exact ⟨next,hc,by change 10*res.par.delta < _; rwa [res.delta]⟩

variable (hh : 0 < h) (supply : ∀ k < h,
  Nonempty (Atlas code times.time (Times.group L (k+1)) (Times.site L k) C))

def tower : (k : ℕ) → k ≤ h → Level times I code C h k
  | 0, _ => Classical.choice (bottom times hh)
  | k+1, hk => ((tower k (by omega)).advance hk (Classical.choice (supply k hk))).choose

theorem follows (hk : k < h) :
    (tower (I := I) hh supply k hk.le).Follows (tower hh supply (k+1) hk) :=
  ((tower hh supply k hk.le).advance hk (Classical.choice (supply k hk))).choose_spec

end Level
end OAI.Geometry.Hirsch.Layer
