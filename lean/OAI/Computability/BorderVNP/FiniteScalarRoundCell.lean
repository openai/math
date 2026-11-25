import OAI.Computability.BorderVNP.FiniteScalarRounds

/-! # Finite-field cell return from the checked compact input writer

The suffix of the actual external assignment contains one Boolean word per
subtotal digit. The already installed compact word writer reads that entire
suffix once. Its field-valued private call supplies precisely the coefficient
needed by the original local bit network.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteScalarRounds

open Crossing FieldDirectory.Copies VPVNP.BurstRAM RoutingISA
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] {w d : ℕ}

omit [Field F] in
/-- The physical subtotal array is exactly the bit-major word supplied to the
existing compact writer, at every index of the source interval. -/
theorem stream_eq_ofFn (c : Index F → Fin d → Bool) :
    stream F c = List.ofFn fun i : Fin (d*Fintype.card F) => claimBits d c i.val := by
  rw [List.ofFn_mul]
  unfold stream
  congr 2
  funext j
  apply congrArg List.ofFn
  funext v
  have he : j.val*Fintype.card F+v.val = (finProdFinEquiv (j,v)).val := by
    change _ = v.val+Fintype.card F*j.val
    ring
  change c v j = claimBits d c (j.val*Fintype.card F+v.val)
  rw [he]
  simp only [claimBits,(finProdFinEquiv (j,v)).isLt,dite_true,Fin.eta,Equiv.symm_apply_apply]

omit [Field F] in
/-- An exact source directory suffices for the existing physical word writer. -/
theorem source (m : Memory w) (start : ℕ) (c : Index F → Fin d → Bool)
    (read : ∀ j : Fin (d*Fintype.card F), (m (start+j.val)).val = (claimBits d c j.val).toNat) :
    CompactWrite.Source m start (stream F c) := by
  rw [stream_eq_ofFn]
  intro i hi
  have h := read ⟨i,by simpa using hi⟩
  simpa only [List.getElem_ofFn] using h

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits) {copies : ℕ}

/-- After the true subtotal suffix has been packed by the native writer, the
one private callback contributes the entire field multiplier for this cell. -/
theorem returned_cell (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) (c : Index F → Fin d → Bool)
    (hw : 0<w) (e : TeamRAM.Event w) (fuel : ℕ)
    (words : e.old = CompactFrame.pack w (stream F c)) (choices : e.choices = [])
    (fits : 2*d*Fintype.card F < fuel) :
    let B := directory N sites table copies d
    let z := bank N a x (claimBits d c)
    (B.weight z : F) * (FieldProcessor.returned (routine F) (result F) fuel e).getD 0 =
      scan N sites table d a x c := by
  intro B z
  rw [event_value F hw c e fuel words fits,choices]
  exact FieldScalar.checked_product N sites table a x c

/-- Summing the joint reports in the actual field callback recovers precisely
the repeated local tensor product, with no factor for rejected reports. -/
theorem sum_returns (sites : List N.Site) (table : N.Tables F) (hw : 0<w)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) (fuel : ℕ) :
    let d := Nat.clog 2 (copies*sites.length+1)
    ∀ e : (Index F → Fin d → Bool) → TeamRAM.Event w,
      (∀ c, (e c).old = CompactFrame.pack w (stream F c) ∧ (e c).choices = []) →
      2*d*Fintype.card F < fuel →
      (∑ c, ((directory N sites table copies d).weight (bank N a x (claimBits d c)) : F) *
        (FieldProcessor.returned (routine F) (result F) fuel (e c)).getD 0) =
      ∏ i, (sites.map (N.read table (a i) (x i))).prod := by
  intro d e he hf
  exact (Finset.sum_congr rfl fun c _ => returned_cell N sites table a x c hw (e c) fuel (he c).1 (he c).2 hf).trans
    (sum_scan N sites table a x)

end FiniteScalarRounds

end BorderVNP
end Computability
end OAI
