import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNodeIdeal

/-! # The ordinal rows of an embedded binary Walsh window -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshWindow

open Matrix FlatWalshNode

/-- Reassemble an active window from two spectator fields and its data bits. -/
def pack (P L d n : ℕ) (width : P+L+d=n) :
    (Fin (2^P) × Fin (2^d)) × Fin (2^L) ≃ Fin (2^n) :=
  ((((Equiv.prodAssoc _ _ _).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _))).trans
    (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv)).trans finProdFinEquiv).trans
    (finCongr (by simp only [←width, pow_add]; ring))

theorem pack_val (P L d n : ℕ) (width : P+L+d=n) (p : Fin (2^P)) (b : Fin (2^d)) (y : Fin (2^L)) :
    (pack P L d n width ((p,b),y)).val = (p.val*2^L + y.val)*2^d+b.val := by
  change b.val + 2^d*y.val + (2^L*2^d)*p.val = _
  ring

theorem pack_split (P L d n : ℕ) (width : P+L+d=n) (p : Fin (2^P)) (b : Fin (2^d)) (y : Fin (2^L)) :
    (pack P L d n width ((p,b),y)).val%(2^d) = b.val ∧
      (pack P L d n width ((p,b),y)).val/(2^d)%(2^L) = y.val ∧
      (pack P L d n width ((p,b),y)).val/(2^(d+L)) = p.val := by
  rw [pack_val, pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm _ (2^d), Nat.mul_add_mod,
    Nat.mod_eq_of_lt b.isLt, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt b.isLt, Nat.add_zero,
    Nat.mul_comm p.val (2^L), Nat.mul_add_mod, Nat.mod_eq_of_lt y.isLt,
    Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt y.isLt, Nat.add_zero]
  exact ⟨rfl,rfl,rfl⟩

/-- Applying a selected-window matrix to an input with arbitrary external
spectator fields equals a contiguous physical child transform. -/
theorem activeRow_window (P L d n : ℕ) (width : P+L+d=n) (suffix : ℕ) (hs : 0 < suffix)
    (g : ℕ) (t : Fin suffix) (v : ℕ → ℂ) (z : Fin (2^n))
    (K : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (entry : ∀ p b y q c x, K (pack P L d n width ((p,b),y)) (pack P L d n width ((q,c),x)) =
      if p=q ∧ b=c then BoxFin.flatWalsh Finset.univ y x else 0) :
    activeRow L (2^d*suffix) v ((g*2^n+z.val)*suffix+t.val) =
      ∑ u : Fin (2^n), K z u * v ((g*2^n+u.val)*suffix+t.val) := by
  classical
  obtain ⟨⟨⟨p,b⟩,y⟩,rfl⟩ := (pack P L d n width).surjective z
  let b' := finProdFinEquiv (b,t)
  have low : b'.val = b.val*suffix+t.val := by
    change t.val+suffix*b.val = _; ring
  have pos (q : Fin (2^L)) :
      (g*2^n + (pack P L d n width ((p,b),q)).val)*suffix+t.val =
        ((g*2^P+p.val)*2^L+q.val)*(2^d*suffix)+b'.val := by
    rw [pack_val, low, ← width, pow_add, pow_add]; ring
  rw [pos, activeRow_at L _ (Nat.mul_pos (Nat.two_pow_pos _) hs)]
  rw [← (pack P L d n width).sum_comp]
  simp only [Fintype.sum_prod_type, entry, ite_mul, zero_mul]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single b]
    · simp only [and_self, ite_true, pos]
    · intro b₁ _ h
      simp [Ne.symm h]
    · simp
  · intro p₁ _ h
    simp [Ne.symm h]
  · simp

end FlatWalshWindow

end NearSquareRoot
end Computability
end OAI
