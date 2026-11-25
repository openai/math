import OAI.Geometry.Hirsch.Levels

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {I : Type} {L V h B C : ℕ} {code : Bundles L V}

def Interpolates (code : Bundles L V) (C : ℕ) : Prop :=
  ∀ (T : Type) [Fintype T] (time : T → ℝ) (block : T → ℕ) (site : T → Fin L),
    Function.Injective time → (∀ s t, block s = block t → site s < site t → time s < time t) →
    Nonempty (Atlas code time block site C)

theorem Interpolates.plan [NeZero L] [NeZero B] (input : Interpolates code C)
    (hh : 0 < h) (tree : Forest I (Fin V) h) (ep : Episodes (L^h)) :
    Nonempty (Plan tree code ep B (Plate.budget code C)) := by
  obtain ⟨times⟩ := Times.exists_times ep B
  have supply : ∀ k < h, Nonempty (Atlas code times.time (Times.group L (k+1)) (Times.site L k) C) := by
    intro k _
    apply input _ _ _ _ times.injective
    intro s t he hl
    apply times.group_ordered L k
    rw [← Times.link L k s,← Times.link L k t,he]
    exact Nat.add_lt_add_left hl _
  let level := fun k (hk : k ≤ h) => Level.tower (I := I) hh supply k hk
  let rank := fun i => h - tree.depth i
  have bound : ∀ i, rank i ≤ h := fun _ => Nat.sub_le ..
  let lev := fun i => level (rank i) (bound i)
  have pos : ∀ i, tree.depth i < h → 0 < rank i := fun _ hi => Nat.sub_pos_of_lt hi
  have next : ∀ i j l, tree.path i = (j,l) :: tree.path j → rank j = rank i + 1 := by
    intro i j l he
    have hi := tree.bounded i
    simp only [rank,Forest.depth,he,List.length_cons] at hi ⊢
    omega
  have adj : ∀ i j l, tree.path i = (j,l) :: tree.path j →
      (lev j).child = (lev i).shift.val ∧ 10*(lev j).par.delta < (lev i).size := by
    intro i j l he
    have ht := next _ _ _ he
    have hj := bound j
    have hi : rank i < h := by omega
    have hf := Level.follows (I := I) hh supply hi
    change (level (rank i + 1) hi).child = (lev i).shift.val ∧
      10*(level (rank i + 1) hi).par.delta < (lev i).size at hf
    have eqn : ∀ k (hk : k ≤ h), k = rank i + 1 →
        (level k hk).child = (lev i).shift.val ∧ 10*(level k hk).par.delta < (lev i).size := by
      rintro k hk rfl; exact hf
    exact eqn _ hj ht
  refine ⟨{
    time := times.time, interior := times.interior,
    panel := fun i => (lev i).panel i, rows := fun i => (lev i).count i,
    par := fun i => (lev i).par, shift := fun i => (lev i).shift.val,
    tangent := fun i => (lev i).shift.supported.line, touches := fun i => (lev i).shift.supported.touch,
    below := fun i => (lev i).shift.supported.below, root := ?_, margin := ?_,
    data := fun i hi => (lev i).data (pos i hi), child := ?_,
    leaf := fun i hi => (lev i).leaf (Nat.sub_eq_zero_of_le (le_of_not_gt hi)) i,
    internal := fun i hi => (lev i).internal (pos i hi) i }⟩
  · intro i hi t
    have ht : rank i = h := by simp [rank,hi]
    apply (lev i).shift.zero ((lev i).top ht)
    unfold Times.group
    rw [ht]
    exact Nat.div_eq_of_lt t.1.isLt
  · intro i j l he
    have hm := (adj _ _ _ he).2
    rw [(lev i).sizeEq] at hm
    by_cases hi : tree.depth i < h
    · simpa [hi,(pos i hi).ne'] using hm
    · have hz : rank i = 0 := Nat.sub_eq_zero_of_le (le_of_not_gt hi)
      simpa [hi,hz] using hm
  · intro i j l he t
    rw [(lev j).childEq,(adj _ _ _ he).1]

def LayerTheorem : Prop :=
  ∀ rate : ℕ, ∃ L V C : ℕ, 2 ≤ L ∧ 0 < V ∧ (2*V)^rate ≤ L ∧
    ∃ code : Bundles L V, Interpolates code C

theorem plan_of_layers (input : LayerTheorem) : PlanTheorem := by
  intro rate
  obtain ⟨L,V,C,hL,hV,hr,code,hi⟩ := input rate
  let : NeZero L := ⟨by omega⟩
  refine ⟨L,V,Plate.budget code C,hL,hV,hr,code,fun h hh I tree B hb ep => ?_⟩
  let : NeZero B := ⟨hb.ne'⟩
  exact hi.plan hh tree ep

theorem scheduler_of_layers (input : LayerTheorem) : SchedulerTheorem :=
  Forest.scheduler_of_modules (modules_of_plan (plan_of_layers input))

end OAI.Geometry.Hirsch.Layer
