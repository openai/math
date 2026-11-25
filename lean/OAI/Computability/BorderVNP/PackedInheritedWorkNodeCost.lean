import OAI.Computability.BorderVNP.PackedInheritedWorkSchedule
import OAI.Computability.BorderVNP.PackedInheritedWorkPrepCost

/-! # Gate charge of one work-augmented crossing node in its actual sparse rectangles -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening.StaticRows CellAddressCircuit VPVNP.VerifierNetwork
open private physical from OAI.Computability.BorderVNP.PackedInheritedWorkStep
open scoped Classical

variable {D m k V V' E n np w : ℕ} [NeZero D] {K : Type} [Field K] (e : PaidIdentity K D m)
variable {A B σ : Type} [Fintype A] [Fintype σ] (seed : A ↪ Fin n)
variable (a : NodeFields (A := A) (k := k) (V := V) (E := E) (n := n) (np := np) (w := w) e B σ)
local notation "N" => siteCapacity e (k*V) n

/-- A sparse incidence scan plus one fixed arithmetic template per physical seed. -/
theorem node_cubic {R W : ℕ} (rows : 1+count N E np N ≤ R) (seeds : Fintype.card A ≤ R)
    (width : w ≤ W) (depth : Nat.clog 2 R ≤ W) :
    (node e seed a).size ≤ (4100+100*(2*e.count+1+birthNodes e))*R*(W+1)^3 := by
  let term := 2*e.count+1+birthNodes e
  let unit := R*(W+1)^3
  have hr : 0<R := by omega
  have pos : 0<unit := Nat.mul_pos hr (by positivity)
  have sq : (w+1)^2 ≤ (W+1)^3 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by positivity) (by decide : 2≤3))
  have birth : Fintype.card A*term*(100*(w+1)^2) ≤ 100*term*unit :=
    (Nat.mul_le_mul (Nat.mul_le_mul_right term seeds) (Nat.mul_le_mul_left 100 sq)).trans_eq
      (by dsimp only [unit]; ring)
  have shape := Views.frame_size (physical e a)
  have hs := node_size e seed a
  have cost := Prep.charge_cubic rows width depth
  unfold Prep.charge at cost
  change _ ≤ 4000*R*(W+1)^3 at cost
  change (node e seed a).size ≤ 7+Fintype.card A*term*(100*(w+1)^2)+_+_ at hs
  change (node e seed a).size ≤ (4100+100*term)*R*(W+1)^3
  rw [show (4100+100*term)*R*(W+1)^3 = 4100*unit+100*term*unit by dsimp only [unit]; ring]
  rw [show 4000*R*(W+1)^3 = 4000*unit by dsimp only [unit]; ring] at cost
  omega

variable {Old : Type} [Fintype Old] [Fintype B] (p : Ports np) (rect : V' = siteCapacity e (k*V) n) (fit : V' ≤ 2^w)
variable (geom : Frame ((Fin k × Old) ⊕ (A × Fin e.count × Fin w)) (SavedPins B V' E w ⊕ Unit))

/-- Cost of the common geometry and width frame on the scheduled successor rectangle. -/
theorem jointAt_cubic {R W : ℕ} (rows : 1+count V' E (k*np) V' ≤ R) (seeds : Fintype.card A ≤ R)
    (width : w ≤ W) (depth : Nat.clog 2 R ≤ W) :
    (jointAt (k := k) (V := V) (E := E) (w := w) (Old := Old) (B := B) e seed p rect fit geom).size ≤ geom.size + (4100+100*(2*e.count+1+birthNodes e))*R*(W+1)^3 := by
  subst V'
  rw [jointAt,jointNode_size]
  exact Nat.add_le_add_left (node_cubic e seed _ rows seeds width depth) _

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
