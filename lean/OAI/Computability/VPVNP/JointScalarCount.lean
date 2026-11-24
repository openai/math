import OAI.Computability.VPVNP.JointScalarCircuit

/-!
# Counting the witnesses of the signed joint row checker

Fixing the row address selects one witness bank. The other two banks must be
all zero, so summing the physical bit witnesses gives precisely the active
count. Both signs of each motif coefficient use the same comparison table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar

open VerifierNetwork JointLabelSystem.FixedRows

variable {n high t W flags clock motif g m q : ℕ}
variable (prod : Fin g → Fin t) (localMap : Fin m → Fin t) (tables : Fin q → Motif.Table m)
variable (parse : Frame (ParseOracle.Input n t W flags) Unit) (path : Frame (Fin n ⊕ Fin clock) Unit)

private theorem assignment_eq (neg : Bool) (row : ℕ) (a : Fin t → ℕ) (f : Fin flags → Bool)
    (u : Fin clock → Bool) (b : Fin motif → Bool) :
    Sum.elim (query (n := n) (high := high) (W := W) neg row a) (witnesses f u b) = assignment neg row a f u b := rfl

private theorem bool_count_and (b : Bool) (p : Prop) [Decidable p] :
    (b && decide p).toNat = if p then b.toNat else 0 := by
  by_cases hp : p <;> simp [hp]

theorem count_grammar (negative : Bool) (row : ℕ) (hr : row < 2^n)
    (a : Fin t → ℕ) (ha : ∀ j, a j < 2^W) :
    (∑ w, (((frame (high := high) (motif := motif) prod localMap tables parse path).circuit ()).eval
      (Sum.elim (query negative row a) w)).toNat) =
      if negative then
        (if ∀ j, a j = 0 then
          ∑ u, (path.eval (Sum.elim (fun j => row.testBit j.val) u) ()).toNat else 0)
      else
        (if ∀ j, a (localMap j) = 0 then
          ∑ f, (parse.eval (Sum.elim (ParseOracle.query (fun j => row.testBit j.val) a W) f) ()).toNat else 0) := by
  classical
  rw [sum_witnesses]
  simp only [Frame.circuit_eval, assignment_eq, eval_grammar prod localMap tables parse path negative row hr a ha]
  cases negative with
  | false =>
    simp only [Bool.false_eq_true, ite_false, bool_count_and]
    by_cases hm : ∀ j, a (localMap j) = 0
    · simp [hm, ite_and]
    · simp [hm]
  | true =>
    simp only [ite_true, bool_count_and]
    by_cases hm : ∀ j, a j = 0
    · simp [hm, ite_and]
    · simp [hm]

theorem count_motif (negative : Bool) (o : Fin q) (hr : 2^n+o.val < 2^(n+high))
    (a : Fin t → ℕ) (ha : ∀ j, a j < 2^W)
    (hfit : Motif.part negative (tableLookup (tables o) (a ∘ localMap)) ≤ 2^motif) :
    (∑ w, (((frame (motif := motif) prod localMap tables parse path).circuit ()).eval
      (Sum.elim (query (high := high) negative (2^n+o.val) a) w)).toNat) =
      if ∀ i, a (prod i) = 0 then Motif.part negative (tableLookup (tables o) (a ∘ localMap)) else 0 := by
  classical
  let M := Motif.part negative (tableLookup (tables o) (a ∘ localMap))
  rw [sum_witnesses]
  have hinner (f : Fin flags → Bool) (u : Fin clock → Bool) :
      (∑ b : Fin motif → Bool, (((frame (high := high) prod localMap tables parse path).circuit ()).eval
        (assignment negative (2^n+o.val) a f u b)).toNat) =
        if (∀ i, a (prod i) = 0) ∧ f = (fun _ => false) ∧ u = (fun _ => false) then M else 0 := by
    rw [← (RAMSerialization.wordBits motif).sum_comp]
    simp only [Frame.circuit_eval, eval_motif prod localMap tables parse path negative o hr a ha]
    by_cases h : (∀ i, a (prod i) = 0) ∧ f = (fun _ => false) ∧ u = (fun _ => false)
    · rw [ite_eq_left h]
      simp only [h, and_true, implies_true]
      calc
        _ = ∑ v : Fin (2^motif), if v.val < M then 1 else 0 := Finset.sum_congr rfl fun v _ => by
          change (decide (v.val < M)).toNat = _
          by_cases hv : v.val < M <;> simp [hv]
        _ = M := by
          rw [Finset.sum_boole, ← Fintype.card_subtype (fun v : Fin (2^motif) => v.val < M)]
          exact Fintype.card_fin_lt_of_le hfit
    · simp [h]
  simp only [assignment_eq, hinner]
  by_cases hp : ∀ i, a (prod i) = 0
  · simp [hp, ite_and, M]
  · simp [hp]

end JointScalar

end VPVNP
end Computability
end OAI
