import OAI.Hierarchy.FormulaPartitionMarkedRun

namespace OAI
/-! # The fixed-slot, fixed-gate summand is a pure partition tensor -/

namespace Hierarchy.FormulaPartition

open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {τ : V→Type} {F : Type*} [Field F]
local notation "h" => Nat.log 2 (Fintype.card V)

theorem markedWeight_factors (ks : List (Kernel V τ F)) (tip : Leaf V τ F)
    (π : FormulaPartitionRank.Partition V (h+1)) (pos : Positions h ks.length) :
    ∃ fac : Fin (h+1) → (∀v,τ v) → F, (∀ j, FormulaPartitionRank.Depends π j (fac j)) ∧
      ∀ a, markedWeight ks tip π pos a = ∏ j, fac j a := by
  classical
  let p (j : Fin (h+1)) := (pos.val j).val
  let Q (j : Fin (h+1)) := Finset.univ.filter (fun v => j ≤ π.val v)
  let gates := routeSteps ks pos
  let pin := routePin π pos
  let mid (j : Fin h) (a : ∀v,τ v) : F :=
    segmentValue (intervalSteps gates (p j.castSucc) (p j.succ-p j.castSucc)) a
      (Q j.castSucc) (Q j.succ)
  let tail (a : ∀v,τ v) : F :=
    walk (intervalSteps (applyPin gates pin) (p (Fin.last h)) (ks.length-p (Fin.last h))) a
      (Q (Fin.last h)) (tip.value a)
  let fac : Fin (h+1) → (∀v,τ v) → F := Fin.lastCases tail mid
  have ordered : StrictMono p := fun _ _ hij => pos.property.1 hij
  have start : p 0=0 := congrArg Fin.val pos.property.2
  have stop : p (Fin.last h)≤ks.length := Nat.le_of_lt_succ (pos.val _).isLt
  have full : Q 0 = Finset.univ := by simp [Q]
  refine ⟨fac,?_,?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun j=>?_) j
    · simp only [fac,Fin.lastCases_last]
      intro a b agree
      apply walk_leaf_locality
      intro v hv
      exact agree v (le_antisymm (Fin.le_last _) (Finset.mem_filter.mp hv).2)
    · simp only [fac,Fin.lastCases_castSucc]
      intro a b agree
      apply segmentValue_locality
      intro v hv
      obtain ⟨before,after⟩ := Finset.mem_sdiff.mp hv
      have lo : j.val ≤ (π.val v).val := (Finset.mem_filter.mp before).2
      have hi : ¬ j.val+1 ≤ (π.val v).val := fun he => after (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
      exact agree v (Fin.ext (by change (π.val v).val=j.val;omega))
  · intro a
    have clear (j : Fin h) (i : ℕ) (lo : p j.castSucc < i) (hi : i < p j.succ) (T : Finset V) :
        pin i T := by
      intro m eqn
      change i=p m at eqn
      by_cases below : m ≤ j.castSucc
      · have := ordered.monotone below
        omega
      · have above : j.succ ≤ m := by
          change ¬ m.val ≤ j.val at below
          change j.val+1 ≤ m.val
          omega
        have := ordered.monotone above
        omega
    have endPin (j : Fin h) (T : Finset V) : pin (p j.succ) T ↔ T=Q j.succ := by
      constructor
      · intro hp
        exact hp j.succ rfl
      · intro he m eqn
        change p j.succ=p m at eqn
        exact ordered.injective eqn ▸ he
    have hh := full_walk_position_prod (len:=ks.length) gates pin p ordered Q start stop clear endPin a (tip.value a)
    rw [markedWeight_eq_walk, Fin.prod_univ_castSucc]
    simpa only [fac,Fin.lastCases_last,Fin.lastCases_castSucc,mid,tail,full] using hh

end
end Hierarchy.FormulaPartition

end OAI
