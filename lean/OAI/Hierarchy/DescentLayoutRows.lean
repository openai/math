import OAI.Hierarchy.DescentRecordedBranch
import OAI.Hierarchy.DescentEdgeTapePrefix

namespace OAI
/-! # The exact two integer sums compared by the common layout controller -/

namespace Hierarchy.DescentSixParty
open scoped Classical BigOperators
noncomputable section
variable {F I : Type} [Field F] [Fintype I]
def layoutUnits {C : ℕ} (extra : ℕ) (side : Bool) (p : Profile C) : ℕ :=
  ∑ e,if retained side e then (p.val e).val+extra else 0

theorem layout_units_bound {C : ℕ} (k : ℕ) (p : Profile C) (side : Bool) : layoutUnits k side p≤C+8+8*k := by
  calc
    layoutUnits k side p ≤ ∑ e : Fin 8, ((p.val e).val+k) := by
      unfold layoutUnits
      apply Finset.sum_le_sum
      intro e _
      split <;> omega
    _ = (∑ e : Fin 8, (p.val e).val)+8*k := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ _ := Nat.add_le_add_right p.property _

theorem surviving_units (G : PoweredGadget F) (z : ℕ) (p : I→Profile G.C) (side : Bool) :
    surviving (branchWidth G (fun _=>z) p) side=z*∑i,layoutUnits G.k side (p i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [layoutUnits,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : retained side e <;> simp [h,branchWidth]

theorem best_units (G : PoweredGadget F) (z : ℕ) (positive : 0<z) (p : I→Profile G.C) :
    bestLayout (branchWidth G (fun _=>z) p)=
      decide ((∑i,layoutUnits G.k true (p i))<(∑i,layoutUnits G.k false (p i))) := by
  simp [bestLayout,surviving_units,Nat.mul_lt_mul_left positive]

/-- A common immutable array contains the one-side contribution of every
valid static profile. Its last extra code serves padded or missing matches. -/
def layoutROM {C c : ℕ} (code : Profile C↪Fin c) (k : ℕ) (s : Bool) (i : ℕ) :=
  if h : ∃p,(code p).val=i then layoutUnits k s h.choose else 0

theorem layoutROM_read {C c : ℕ} (code : Profile C↪Fin c) (k : ℕ) (s : Bool) (p : Profile C) :
    layoutROM code k s (code p).val=layoutUnits k s p := by
  have h : ∃q,(code q).val=(code p).val := ⟨p,rfl⟩
  exact (dite_eq_left h).trans (congrArg (layoutUnits k s) (code.injective (Fin.ext h.choose_spec)))

theorem layoutROM_hole {C c : ℕ} (code : Profile C↪Fin c) (k : ℕ) (s : Bool) :
    layoutROM code k s c=0 := by
  apply dite_eq_right
  rintro ⟨p,h⟩;have := (code p).isLt;omega

end
end Hierarchy.DescentSixParty

end OAI
