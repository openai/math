import OAI.Computability.BorderVNP.FiniteScalarBurst

/-! # Reconstructing a checked cell weight at a fetched private opcode

The actual scalar-returning private call receives the same binary reports that
the sparse cell directory checked. For each physical assignment this recovers
the product of its field entries. Summing the joint reports gives each repeated
box its true contraction factor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldScalar

open Crossing CellSparse FieldDirectory.Copies
open scoped BigOperators Classical
open private bank_claim from OAI.Computability.BorderVNP.FiniteCellCopiesScan

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {F : Type*} [Field F] [Fintype F] {copies w d : ℕ}

/-- The exact field multiplier of the validated count bits of a repeated cell. -/
theorem checked_product (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) (c : Index F → Fin d → Bool) :
    let B := directory N sites table copies d
    let z := bank N a x (claimBits d c)
    (B.weight z : F) * (∏ i, (Fintype.equivFin F).symm i ^ FieldPowers.digits (List.ofFn (c i))) =
      scan N sites table d a x c := by
  intro B z
  rw [scan,FieldPowers.evaluate]
  apply congrArg ((B.weight z : F) * ·)
  let eqn : Index F ≃ Fin B.reportedCounts.length := finCongr (by simp [B,directory])
  rw [← eqn.prod_comp (fun i => scalar N sites table copies d i ^ FieldPowers.digits (B.reportedCounts[i].map z))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hv : scalar N sites table copies d (eqn i) = (Fintype.equivFin F).symm i := by
    unfold scalar
    exact congrArg (Fintype.equivFin F).symm (Fin.ext rfl)
  rw [hv]
  have he : (B.reportedCounts[eqn i]).map z = List.ofFn (c i) := by
    change ((List.ofFn fun v : Index F => List.ofFn (claimAddress N copies d v))[eqn i]).map z = _
    simp only [Fin.getElem_fin,List.getElem_ofFn,List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    change bank N a x (claimBits d c) (claimAddress N copies d i j) = c i j
    exact bank_claim ..
  rw [he]

/-- At any setting of the count bits, evaluating the concrete field return
on the actual RAM words gives the same multiplier as the cell's power scanner. -/
theorem event_cell (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits)
    (c : Index F → Fin d → Bool) (hw : 0<w) (e : TeamRAM.Event w) (fuel : ℕ)
    (words : e.old = burst F w (fun i => List.ofFn (c i))) (choices : e.choices = [])
    (fits : Fintype.card F*(2*d+1)+Fintype.card F < fuel) :
    let B := directory N sites table copies d
    let z := bank N a x (claimBits d c)
    (B.weight z : F) * (FieldProcessor.returned (routine F) (output F) fuel e).getD 0 =
      scan N sites table d a x c := by
  intro B z
  let counts := fun i : Index F => List.ofFn (c i)
  have hl := packet_length F counts d (by simp [counts]) (Fintype.card F) le_rfl
  rw [event_value F hw counts fuel e words (hl ▸ fits), choices]
  change (B.weight z : F) * (∏ i, (Fintype.equivFin F).symm i ^ FieldPowers.digits (counts i)) = _
  exact checked_product N sites table a x c

/-- The two actual callback factors, the signed directory acceptance and the
field-valued private return, recover all repeated local site entries once. -/
theorem sum_events (sites : List N.Site) (table : N.Tables F) (hw : 0<w)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) (fuel : ℕ) :
    let d := Nat.clog 2 (copies*sites.length+1)
    ∀ e : (Index F → Fin d → Bool) → TeamRAM.Event w,
      (∀ c, (e c).old = burst F w (fun i => List.ofFn (c i)) ∧ (e c).choices = []) →
      Fintype.card F*(2*d+1)+Fintype.card F < fuel →
      (∑ c, ((directory N sites table copies d).weight (bank N a x (claimBits d c)) : F) *
        (FieldProcessor.returned (routine F) (output F) fuel (e c)).getD 0) =
      ∏ i, (sites.map (N.read table (a i) (x i))).prod := by
  intro d e he hf
  have each c := event_cell N sites table a x c hw (e c) fuel (he c).1 (he c).2 hf
  exact (Finset.sum_congr rfl fun c _ => each c).trans (sum_scan N sites table a x)

end FieldScalar

end BorderVNP
end Computability
end OAI
