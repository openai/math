import OAI.Hierarchy.DescentGLFiber
import Mathlib.LinearAlgebra.Prod
import Mathlib.Basic.Real.Basic

namespace OAI
/-! # Binary linear layouts conditioned on previously fixed output rows

A completion fixes its headRows as an entire linear map. Composing on the output
with an invertible transformation of the remaining rows acts transitively on
the possible tails of each surviving nonzero difference.
-/

namespace Hierarchy.DescentGL
open scoped Classical
noncomputable section

def splitRows (h r : ℕ) : Bits (h+r) ≃ₗ[ZMod 2] Bits h × Bits r where
  toFun v := (fun i => v (Fin.castAdd r i), fun i => v (Fin.natAdd h i))
  invFun v := Fin.append v.1 v.2
  left_inv v := by
    funext i
    refine Fin.addCases (fun l => ?_) (fun u => ?_) i
    · exact Fin.append_left (fun i => v (Fin.castAdd r i)) (fun i => v (Fin.natAdd h i)) l
    · exact Fin.append_right (fun i => v (Fin.castAdd r i)) (fun i => v (Fin.natAdd h i)) u
  right_inv v := by
    apply Prod.ext
    · funext i; exact Fin.append_left v.1 v.2 i
    · funext i; exact Fin.append_right v.1 v.2 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- All layouts whose first `h` rows agree with those already selected. -/
abbrev Completions (h r : ℕ) (base : Layout (h+r)) :=
  {L : Layout (h+r) // ∀ v, (splitRows h r (L v)).1 = (splitRows h r (base v)).1}

private def twist (h : ℕ) {r : ℕ} (T : Layout r) : Layout (h+r) :=
  ((splitRows h r).trans ((LinearEquiv.refl _ _).prodCongr T)).trans (splitRows h r).symm

private theorem split_twist (h : ℕ) {r : ℕ} (T : Layout r) (v : Bits (h+r)) :
    splitRows h r (twist h T v) = ((splitRows h r v).1, T (splitRows h r v).2) := by
  apply (splitRows h r).apply_symm_apply

private def modify {h r : ℕ} {base : Layout (h+r)} (T : Layout r)
    (L : Completions h r base) : Completions h r base :=
  ⟨L.val.trans (twist h T), fun v => by
    change (splitRows h r (twist h T (L.val v))).1 = _
    rw [split_twist]
    exact L.property v⟩

private def modifyEquiv {h r : ℕ} {base : Layout (h+r)} (T : Layout r) :
    Completions h r base ≃ Completions h r base where
  toFun := modify T
  invFun := modify T.symm
  left_inv L := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply (splitRows h r).injective
    change splitRows h r (twist h T.symm (twist h T (L.val v))) = _
    rw [split_twist, split_twist, T.symm_apply_apply]
  right_inv L := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply (splitRows h r).injective
    change splitRows h r (twist h T (twist h T.symm (L.val v))) = _
    rw [split_twist, split_twist, T.apply_symm_apply]

private def tailImage {h r : ℕ} {base : Layout (h+r)} (d : Nonzero (h+r))
    (survives : (splitRows h r (base d.val)).1 = 0) (L : Completions h r base) : Nonzero r :=
  ⟨(splitRows h r (L.val d.val)).2, by
    intro hz
    have hz' : splitRows h r (L.val d.val) = 0 := Prod.ext ((L.property d.val).trans survives) hz
    exact d.property (L.val.injective (((splitRows h r).injective (hz'.trans
      (splitRows h r).map_zero.symm)).trans L.val.map_zero.symm))⟩

/-- When all rows have been fixed there is no surviving nonzero difference. -/
theorem no_survivor_after_last_row (h : ℕ) (base : Layout (h+0)) (d : Nonzero (h+0)) :
    (splitRows h 0 (base d.val)).1 ≠ 0 := by
  intro hz
  let u := tailImage d hz (⟨base,fun _ => rfl⟩ : Completions h 0 base)
  exact u.property (Subsingleton.elim _ _)

private theorem equal_conditional_fibers {h r : ℕ} (base : Layout (h+r)) (d : Nonzero (h+r))
    (survives : (splitRows h r (base d.val)).1 = 0) (a b : Nonzero r) :
    Fintype.card {L : Completions h r base // tailImage d survives L = a} =
      Fintype.card {L : Completions h r base // tailImage d survives L = b} := by
  obtain ⟨T, hT⟩ := exists_map a.property b.property
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (modifyEquiv T)
  intro L
  simp only [Subtype.ext_iff]
  change (splitRows h r (L.val d.val)).2 = a.val ↔
    (splitRows h r (twist h T (L.val d.val))).2 = b.val
  rw [split_twist, ← hT, T.injective.eq_iff]

private theorem prefix_after_head {h r j : ℕ} (hj : j≤r) (v : Bits (h+r))
    (head : (splitRows h r v).1 = 0) :
    headRows (Nat.add_le_add_left hj h) v = 0 ↔ headRows hj (splitRows h r v).2 = 0 := by
  constructor
  · intro hz
    funext i
    exact congrFun hz (Fin.natAdd h i)
  · intro hz
    funext i
    refine Fin.addCases (fun l => ?_) (fun u => ?_) i
    · exact congrFun head l
    · exact congrFun hz u

/-- Among completions of `h` fixed rows, a surviving nonzero difference
collides through the next `j` rows with proportion
`(2^(r-j)-1)/(2^r-1)`, where `r` is the number of remaining rows. -/
theorem conditional_collision_count {h r j : ℕ} (hj : j≤r) (base : Layout (h+r))
    (d : Nonzero (h+r)) (survives : (splitRows h r (base d.val)).1 = 0) :
    (Finset.univ.filter (fun L : Completions h r base =>
        headRows (Nat.add_le_add_left hj h) (L.val d.val)=0)).card * (2^r-1) =
      (2^(r-j)-1) * Fintype.card (Completions h r base) := by
  let a := tailImage d survives (⟨base, fun _ => rfl⟩ : Completions h r base)
  have eqn := uniform_multiplicity (tailImage d survives) a (fun v => headRows hj v.val=0)
    (fun L => headRows (Nat.add_le_add_left hj h) (L.val d.val)=0)
    (fun L => prefix_after_head hj (L.val d.val) ((L.property d.val).trans survives))
    (fun t => equal_conditional_fibers base d survives t a)
  rw [zero_prefix_card, card_nonzero] at eqn
  simpa only [Fintype.card_subtype] using eqn

/-- Conditional probability of keeping equality at depth `h+j` after the first
`h` rows have annihilated the difference. -/
theorem conditional_collision_probability {h r j : ℕ} (hj : j≤r) (base : Layout (h+r))
    (d : Nonzero (h+r)) (survives : (splitRows h r (base d.val)).1 = 0) :
    ((Finset.univ.filter (fun L : Completions h r base =>
        headRows (Nat.add_le_add_left hj h) (L.val d.val)=0)).card : ℝ) /
        Fintype.card (Completions h r base) =
      ((2^(r-j)-1 : ℕ) : ℝ) / ((2^r-1 : ℕ) : ℝ) := by
  let L : Completions h r base := ⟨base,fun _ => rfl⟩
  let : Nonempty (Completions h r base) := ⟨L⟩
  let : Nonempty (Nonzero r) := ⟨tailImage d survives L⟩
  have hden : 0 < 2^r-1 := by rw [← card_nonzero]; exact Fintype.card_pos
  apply (div_eq_div_iff (by exact_mod_cast (Fintype.card_pos (α := Completions h r base)).ne')
    (by exact_mod_cast hden.ne')).mpr
  exact_mod_cast conditional_collision_count hj base d survives


end
end Hierarchy.DescentGL

end OAI
