import OAI.Computability.BorderVNP.DiagonalPhysicalGeometryComponents
import OAI.Computability.BorderVNP.GeometryTableReservation

/-! # A length-only gate ceiling for self-addressed geometry output

The seed compiler's measured Boolean bound determines the ceiling before
any absolute pointer is embedded. The four-way lowering and the physical
interpreter use this same ceiling for every choice of pins and emitter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales Cover Packing PackedHistoryCircuit VPVNP.VerifierNetwork GeometryAdviceRate
open PackedHistoryCircuit.Normalized.SelectedSchedule

/-- Public pre-lowering gate allowance depending only on the selected batch,
input length and fixed polynomial of the emitter. -/
noncomputable def geometryGateBudget (U degree r n : ℕ) : ℕ :=
  ⌊((U:ℝ)+8)*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^degree⌋₊

/-- Actual reserved number of AND/NOT gate records in the physical packet. -/
noncomputable def geometryGateCeiling (U degree r n : ℕ) := 4*geometryGateBudget U degree r n

variable {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]

/-- Every admissible concrete frame fits one common gate allocation. The
output references and reserved profile also fit the numerical charge of that
same allocation. This estimate permits the frames to contain addresses
computed from the common ceiling itself. -/
theorem geometry_reserve_components {active o field mult rows degree U n r : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r)
    (history : Frame (X ⊕ Y) (V ⊕ Unit)) (order : Y ≃ Fin active) (fit : active ≤ SeedPlan.profileReserve r n)
    (emit : Frame ((X ⊕ Fin (SeedPlan.profileReserve r n)) ⊕ V) (Fin o × Fin field)) (x : X → Bool)
    (paid : ((mult*history.size+active:ℕ):ℝ) ≤ r*(n:ℝ)^(92/100:ℝ))
    (rowFit : (rows:ℝ) ≤ r*(n:ℝ)^(92/100:ℝ))
    (cost : history.size+emit.size+o*field ≤ mult*history.size+U*rows*(logWidth r n)^degree) :
    let reserve := SeedPlan.profileReserve r n
    let ceiling := geometryGateCeiling U degree r n
    let t := geometryTable history order fit emit x
    t.size ≤ ceiling ∧ (t.reserve ceiling).size = ceiling ∧
      ((geometryGateBudget U degree r n+reserve+o*field:ℕ):ℝ) ≤
        (2*((U:ℝ)+8))*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^degree := by
  intro reserve ceiling t
  let mass := ((U:ℝ)+8)*r*(n:ℝ)^(92/100:ℝ)*(logWidth r n:ℝ)^degree
  have charge := geometry_size_of_components hn hr paid rowFit cost
  have natCharge := Nat.le_floor charge
  change history.size+emit.size+3*(reserve-active)+3+reserve+o*field ≤ geometryGateBudget U degree r n at natCharge
  have gates : history.size+emit.size+3*(reserve-active)+3 ≤ geometryGateBudget U degree r n := by omega
  have admitted := (exportRows_size history order fit emit x).trans (Nat.mul_le_mul_left 4 gates)
  have aux : reserve+o*field ≤ geometryGateBudget U degree r n := by omega
  have cap : (geometryGateBudget U degree r n:ℝ) ≤ mass := Nat.floor_le (by positivity)
  refine ⟨admitted,t.reserve_size ceiling admitted,?_⟩
  have bound : ((geometryGateBudget U degree r n+reserve+o*field:ℕ):ℝ) ≤ mass+mass := by
    rw [Nat.add_assoc,Nat.cast_add]
    exact add_le_add cap (((Nat.cast_le (α := ℝ)).mpr aux).trans cap)
  apply bound.trans_eq
  dsimp only [mass]
  ring

end Diagonal

end BorderVNP
end Computability
end OAI
