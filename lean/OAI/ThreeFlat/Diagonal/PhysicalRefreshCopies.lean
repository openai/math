import OAI.ThreeFlat.Diagonal.RefreshTableStep
import OAI.ThreeFlat.Diagonal.PhysicalStateWidth
import OAI.ThreeFlat.Diagonal.BlockEnergyPotential
import OAI.ThreeFlat.Diagonal.FixedMotifMaxWidth

namespace OAI
/-! # Total and individual copy counts of the physical refresh table -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Expander Computability.VPVNP.Compression CompressorPacking RefreshTies
open scoped BigOperators Classical
noncomputable section

variable {F : Type} [Field F] {m lanes hbits rem h pad : ℕ}
    {c : Fin m → Fin m → ℕ} {H : ℝ} (T : RefreshMotif.Table F c (1+h+pad) H)
    (A : State m lanes) (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)

/-- The count used in the histogram at this actual base and residual lane. -/
abbrev refreshCopies (v : A.Base × BitWord rem) : ℕ :=
  T.repeats (changeLanes A.graph u) port (A.width ∘ (StageAddress.refreshEdge u port).symm) v

/-- Each old edge width is read once at its source and once at its target.
The constant part of the demand score costs at most one per old position. -/
theorem refreshCopies_sum_le :
    (∑ v, refreshCopies T A u port v) ≤ A.positions+2*A.widthSum := by
  let G := changeLanes A.graph u
  let w := A.width ∘ (StageAddress.refreshEdge u port).symm
  have old : (∑ a, w a) = A.widthSum :=
    (StageAddress.refreshEdge (V := A.Base) u port).symm.sum_comp A.width
  have dense : (∑ v, ∑ e, profile G port w v e) = 2*∑ a, w a := by
    exact_mod_cast (dense_charge (arrival G port) (fun a => (w a : ℝ)))
  have hm : 0 < m := by have ht := (port.symm 0).isLt; omega
  have groups : Fintype.card (A.Base × BitWord rem) ≤ A.positions := by
    apply (Nat.le_mul_of_pos_right _ hm).trans
    apply Nat.le_of_eq
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      (Fintype.card_congr ((StageAddress.refreshSite u port).symm.trans A.chart))
  calc
    _ ≤ ∑ v, (1 + ∑ e, profile G port w v e) :=
      Finset.sum_le_sum (fun v _ => FixedMotifMaxWidth.score_le_sentinel (profile G port w v) T.base _)
    _ = Fintype.card (A.Base × BitWord rem)+2*A.widthSum := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,Nat.cast_id, Nat.mul_one, dense, old]
    _ ≤ _ := Nat.add_le_add_right groups _

/-- A single refresh block has two square arrays of demand entries, each
bounded by the old maximum edge width. -/
theorem refreshCopies_le (v : A.Base × BitWord rem) :
    refreshCopies T A u port v ≤ (1+2*m*m)*(1+A.maxWidth) := by
  let G := changeLanes A.graph u
  let w := A.width ∘ (StageAddress.refreshEdge u port).symm
  have entry (e) : profile G port w v e ≤ A.maxWidth :=
    A.width_le_maxWidth ((StageAddress.refreshEdge u port).symm (addr (arrival G port) v e))
  have row : (∑ e, profile G port w v e) ≤ (2*m*m)*A.maxWidth := calc
    _ ≤ ∑ _e : Bool × Fin m × Fin m, A.maxWidth := Finset.sum_le_sum (fun e _ => entry e)
    _ = _ := by simp [Nat.mul_assoc]
  calc
    _ ≤ 1+∑ e, profile G port w v e := FixedMotifMaxWidth.score_le_sentinel _ T.base _
    _ ≤ 1+(2*m*m)*A.maxWidth := Nat.add_le_add_left row _
    _ ≤ _ := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]; omega

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
