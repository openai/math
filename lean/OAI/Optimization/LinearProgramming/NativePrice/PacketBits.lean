import OAI.Optimization.LinearProgramming.NativePrice.Tape
import OAI.Optimization.LinearProgramming.Compression.BinaryCanonical

/-! Canonical scalar lengths for the signed reduced price packet and all integer intermediates. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NativePrice

open RAM OracleSpec

theorem field_width (q : ℚ) :
    max q.num.natAbs.bits.length q.den.bits.length ≤ (encodeRat q).length := by
  simp only [encodeRat,encodeNat,List.length_cons,List.length_append,frameLen]
  omega

theorem ratBits_field (q : ℚ) : ratBits q ≤ (encodeRat q).length+3 := by
  have hlog (n : ℕ) : n.log2 ≤ n.bits.length := by
    obtain rfl | hn := eq_or_ne n 0
    · decide
    apply Nat.le_of_lt_succ ((Nat.log2_lt hn).mpr ?_)
    have hn' : n < 2^n.bits.length := by simpa only [value_bits] using value_lt n.bits
    exact hn'.trans (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
  unfold ratBits
  simp only [encodeRat,encodeNat,List.length_cons,List.length_append,frameLen]
  have hm := hlog q.num.natAbs
  have hd := hlog q.den
  omega

private theorem field_le_flatMap (q : ℚ) (xs : List ℚ) (hm : q∈xs) :
    (encodeRat q).length ≤ (xs.flatMap encodeRat).length := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    rcases List.mem_cons.mp hm with rfl|h
    · simp
    · simpa only [List.flatMap_cons,List.length_append] using (ih h).trans (Nat.le_add_left _ _)

theorem field_le_packet {N : ℕ} (i : Fin N) (p : Fin N → ℚ) (j : Fin N) :
    (encodeRat (p j)).length ≤ (priceQuery i p).length := by
  have h := field_le_flatMap (p j) (List.ofFn p) (List.mem_ofFn.mpr ⟨j,rfl⟩)
  unfold priceQuery
  rw [List.length_append]
  exact h.trans (Nat.le_add_left _ _)

theorem designation_width {N : ℕ} (i : Fin N) (p : Fin N → ℚ) :
    i.val.bits.length ≤ (priceQuery i p).length := by
  simp only [priceQuery,encodeNat,List.length_append,frameLen]
  omega

/-- Scalar safety premises for the decoder. They apply over any ordered field. -/
structure Values {K : Type*} [Field K] {N : ℕ} (P : K → Prop) (i : Fin N) (p : Fin N → ℚ) : Prop where
  designation : ∀ v : ℕ, v ≤ 2^i.val.bits.length → P (v:K)
  counter : ∀ v : ℕ, v ≤ i.val+1 → P (v:K)
  fields : ∀ j, ∀ v : ℕ, v ≤ 2^(max (p j).num.natAbs.bits.length (p j).den.bits.length) → P (v:K)
  signed : ∀ j, P ((p j).num:K)
  price : ∀ j, P ((p j):K)

/-- The actual word length plus three bounds every newly produced rational register. -/
theorem values_packet {N : ℕ} (i : Fin N) (p : Fin N → ℚ) (B : ℕ)
    (hB : (priceQuery i p).length+3 ≤ B) : Values (fun x : ℚ => ratBits x ≤ B) i p := by
  have bound (e x : ℕ) (he : e≤(priceQuery i p).length) (hx : x≤2^e) : ratBits (x:ℚ) ≤ B := by
    have h := Compression.ratBits_signed_integer_of_le_pow (x:ℤ) e (by simpa using hx)
    exact (by simpa using h : ratBits (x:ℚ) ≤ e+3).trans (by omega)
  have hi : i.val < 2^i.val.bits.length := by simpa only [value_bits] using value_lt i.val.bits
  refine ⟨fun x hx => bound _ _ (designation_width i p) hx,
    fun x hx => bound _ _ (designation_width i p) (by omega),?_,?_,?_⟩
  · intro j x hx
    exact bound _ _ ((field_width (p j)).trans (field_le_packet i p j)) hx
  · intro j
    have h := Compression.ratBits_signed_integer_of_le_pow (p j).num (p j).num.natAbs.bits.length
      (by have v := value_lt (p j).num.natAbs.bits; rw [value_bits] at v; exact v.le)
    have hwidth := field_width (p j)
    have hfield := field_le_packet i p j
    omega
  · intro j
    exact (ratBits_field (p j)).trans (by have := field_le_packet i p j; omega)

end NativePrice
end LinearProgramming
end Optimization
end OAI
