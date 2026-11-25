import OAI.LinearAlgebra.SpectralBooks.ComparisonCatalyst

/-!
# Adjoining a reversed tensor comparison

To separate `x` from `y`, impose the comparison `y ≤ x` and allow tensor
multipliers and a common direct summand. A compression of a positive natural
number in this enlarged preorder is a trade giving a scalar gain in the
original restriction order.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- Compare after trading a multiple of `x` on the left for a multiple of `y`
on the right, retaining an arbitrary common summand. -/
def TradeLE (x y a b : S) : Prop := ∃ s w : S, a + s * x + w ≤ b + s * y + w

theorem TradeLE.of_le {x y a b : S} (h : a ≤ b) : TradeLE x y a b :=
  ⟨0, 0, by simpa using h⟩

theorem TradeLE.reversed (x y : S) : TradeLE x y y x :=
  ⟨1, 0, by simp [add_comm]⟩

variable [IsOrderedAddMonoid S]

theorem TradeLE.trans {x y a b c : S} (h : TradeLE x y a b) (g : TradeLE x y b c) :
    TradeLE x y a c := by
  obtain ⟨s, w, hs⟩ := h
  obtain ⟨t, v, ht⟩ := g
  refine ⟨s + t, w + v, ?_⟩
  calc
    _ = (a + s*x + w) + (t*x + v) := by ring
    _ ≤ (b + s*y + w) + (t*x + v) := add_le_add_left hs _
    _ = (s*y + w) + (b + t*x + v) := by ring
    _ ≤ (s*y + w) + (c + t*y + v) := add_le_add_right ht _
    _ = _ := by ring

theorem TradeLE.add {x y a b c d : S} (h : TradeLE x y a b) (g : TradeLE x y c d) :
    TradeLE x y (a + c) (b + d) := by
  obtain ⟨s, w, hs⟩ := h
  obtain ⟨t, v, ht⟩ := g
  refine ⟨s + t, w + v, ?_⟩
  calc
    _ = (a + s*x + w) + (c + t*x + v) := by ring
    _ ≤ (b + s*y + w) + (d + t*y + v) := add_le_add hs ht
    _ = _ := by ring

variable [IsOrderedMonoid S]

omit [IsOrderedAddMonoid S] in
theorem TradeLE.mul_left {x y a b : S} (z : S) (h : TradeLE x y a b) :
    TradeLE x y (z*a) (z*b) := by
  obtain ⟨s, w, hs⟩ := h
  refine ⟨z*s, z*w, ?_⟩
  calc
    _ = z * (a + s*x + w) := by ring
    _ ≤ z * (b + s*y + w) := mul_le_mul_right hs z
    _ = _ := by ring

/-- The enlarged preorder is installed only while extracting a separating state. -/
@[instance_reducible] def tradePreorder (x y : S) : Preorder S where
  le := TradeLE x y
  lt a b := TradeLE x y a b ∧ ¬ TradeLE x y b a
  le_refl a := TradeLE.of_le (le_refl a)
  le_trans _ _ _ := TradeLE.trans

/-- A compression in the enlarged preorder pays for all tensor powers in the
original order. -/
theorem powerComparison_of_tradeCompression (hzero : ∀ a : S, 0 ≤ a)
    (hbound : ∀ a : S, ∃ n : ℕ, a ≤ (n : S)) {x y : S} (hy : 1 ≤ y)
    {D : S} {m : ℕ} (hm : 0 < m) (h : TradeLE x y (D + m) D) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → x ^ n ≤ C • y ^ n := by
  obtain ⟨s, w, hs⟩ := h
  have hm' : (1 : S) ≤ (m : S) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simpa using add_le_add_left (hzero (n : S)) (1 : S)
  apply powerComparison_of_additiveGain hzero hbound hy
  refine ⟨s, D + w, ?_⟩
  calc
    _ ≤ (m : S) + s*x + (D+w) := add_le_add_left (add_le_add_left hm' _) _
    _ = D + m + s*x + w := by ring
    _ ≤ D + s*y + w := hs
    _ = _ := by ring

end SpectralBooks
end LinearAlgebra
end OAI
