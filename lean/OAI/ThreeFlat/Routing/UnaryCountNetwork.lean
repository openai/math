import OAI.ThreeFlat.Routing.TypedWiring
import OAI.ThreeFlat.Routing.StableCompactionPadding
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Compute a unary count and connect it to a bit network -/

namespace ThreeFlat.Routing.UnaryCount

open scoped BigOperators Classical
noncomputable section

private def levels (n : ℕ) := Nat.log 2 (n+1)+1

private theorem rows_le (n : ℕ) : n ≤ 2^(levels n) :=
  (Nat.le_succ n).trans (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n+1)).le

private theorem rows_upper (n : ℕ) : 2^(levels n) ≤ 2*(n+1) := by
  rw [levels, pow_succ, Nat.mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self _ (Nat.succ_ne_zero n))

abbrev Pin (L n : ℕ) := Fin L ⊕ Fin n

private def arity (L n : ℕ) : Bool → ℕ
  | false => n+(n+n)
  | true => Fintype.card (Pin L n)

private def component (F : Type*) [Zero F] [One F] (L n : ℕ) (consumer : BitNetwork F (Fintype.card (Pin L n))) :
    (b : Bool) → BitNetwork F (arity L n b)
  | false => StableCompaction.paddedNetwork F n (levels n) (rows_le n)
  | true => consumer

private def wire (L n : ℕ) : (b : Bool) → Fin (arity L n b) → BitSource n (Fintype.card (Pin L n))
  | false => Fin.append (fun j => .pin (Fintype.equivFin (Pin L n) (.inr j)))
      (Fin.append (fun _ => .constant true) (fun j => .hidden j))
  | true => fun t => match (Fintype.equivFin (Pin L n)).symm t with
    | .inl l => .pin (Fintype.equivFin (Pin L n) (.inl l))
    | .inr j => .hidden j

/-- Supply a unary count to the consumer while leaving its other pins external. -/
def network (F : Type*) [Zero F] [One F] (L n : ℕ) (consumer : BitNetwork F (Fintype.card (Pin L n))) :
    BitNetwork F (Fintype.card (Pin L n)) :=
  BitNetwork.glue (component F L n consumer) (wire L n)

theorem network_value {F : Type*} [CommSemiring F] (L n : ℕ) (consumer : BitNetwork F (Fintype.card (Pin L n)))
    (M : Fin n → Bool) (label : Fin L → Bool) :
    TypedWiring.value (network F L n consumer) (Sum.elim label M) =
      TypedWiring.value consumer (Sum.elim label (StableCompaction.compact M (fun _ => true))) := by
  let ext := Sum.elim label M
  let pins := fun k => ext ((Fintype.equivFin (Pin L n)).symm k)
  let unary := StableCompaction.compact M (fun _ => true)
  have hc (a : Fin n → Bool) :
      (component F L n consumer false).eval (fun k => (wire L n false k).read a pins) =
        if a = unary then 1 else 0 := by
    refine Eq.trans ?_ (StableCompaction.paddedNetwork_eval n (levels n) (rows_le n) M (fun _ => true) a)
    apply congrArg (StableCompaction.paddedNetwork F n (levels n) (rows_le n)).eval
    funext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp [wire, BitSource.read, pins, ext]
    · refine Fin.addCases (fun t => ?_) (fun t => ?_) j
      · simp [wire, BitSource.read]
      · simp [wire, BitSource.read]
        simp only [show t.addNat n = Fin.natAdd n t from Fin.ext (Nat.add_comm ..), Fin.append_right]
  have ht (a : Fin n → Bool) :
      (component F L n consumer true).eval (fun k => (wire L n true k).read a pins) =
        TypedWiring.value consumer (Sum.elim label a) := by
    apply congrArg consumer.eval
    funext k
    cases he : (Fintype.equivFin (Pin L n)).symm k <;>
      simp [wire, he, pins, ext, BitSource.read]
  change (network F L n consumer).eval pins = _
  rw [network, BitNetwork.glue_eval]
  simp_rw [Fintype.prod_bool, hc, ht]
  simp [mul_ite, unary]

theorem network_cells (F : Type*) [Zero F] [One F] (L n : ℕ) (consumer : BitNetwork F (Fintype.card (Pin L n))) :
    (network F L n consumer).cells ≤ 32768 * (n+1) * (Nat.log 2 (n+1)+2)^3 + consumer.cells := by
  have hc := StableCompaction.paddedNetwork_cells F n (levels n) (rows_le n)
  have hu := Nat.mul_le_mul_right ((levels n+1)^3) (Nat.mul_le_mul_left 16384 (rows_upper n))
  have hbound : (StableCompaction.paddedNetwork F n (levels n) (rows_le n)).cells ≤
      32768 * (n+1) * (Nat.log 2 (n+1)+2)^3 :=
    hc.trans (by simpa only [← Nat.mul_assoc, levels] using hu)
  rw [network, BitNetwork.glue_cells, Fintype.sum_bool]
  simp only [component]
  omega

theorem network_internal (F : Type*) [Zero F] [One F] (L n : ℕ) (consumer : BitNetwork F (Fintype.card (Pin L n))) :
    (network F L n consumer).internal ≤ n + 32768 * (n+1) * (Nat.log 2 (n+1)+2)^3 + consumer.internal := by
  have hc := StableCompaction.paddedNetwork_internal F n (levels n) (rows_le n)
  have hu := Nat.mul_le_mul_right ((levels n+1)^3) (Nat.mul_le_mul_left 16384 (rows_upper n))
  have hbound : (StableCompaction.paddedNetwork F n (levels n) (rows_le n)).internal ≤
      32768 * (n+1) * (Nat.log 2 (n+1)+2)^3 :=
    hc.trans (by simpa only [← Nat.mul_assoc, levels] using hu)
  rw [network, BitNetwork.glue_internal, Fintype.sum_bool]
  simp only [component]
  omega

end
end ThreeFlat.Routing.UnaryCount

end OAI
