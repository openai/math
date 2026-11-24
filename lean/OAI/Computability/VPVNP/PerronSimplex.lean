import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Counting monomials of bounded total degree for Perron's theorem

Bound the exponent of the first input variable by `B` and the sum of the
remaining `m` exponents by `B`. Substituting polynomials of degree at most
`D` gives output monomials of total degree at most `2 * B * D`.
Dividing each output exponent by `2 * (D + 1)` places the quotients in the
simplex of degree `B`. The remainders account for at most `B` possibilities
when `B = (2 * (D + 1)) ^ m`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate

/-- Exponents of the monomials of total degree at most `d` in `m` variables. -/
abbrev Simplex (m d : ℕ) := {e : Fin m → Fin (d + 1) // ∑ i, (e i).val ≤ d}

/-- Degree bound on each of the two input blocks. -/
def perronRadius (m D : ℕ) : ℕ := (2 * (D + 1)) ^ m

/-- Total degree bound on the resulting polynomial relation. -/
def perronSimplexBound (m D : ℕ) : ℕ := 2 * perronRadius m D

/-- Divide each exponent by `q`, keeping both quotient and remainder. -/
private def divideSimplex {m d B q : ℕ} (hq : 0 < q) (hd : d ≤ B * q) :
    Simplex m d ↪ Simplex m B × (Fin m → Fin q) where
  toFun e := by
    have hsum : (∑ i, (e.val i).val / q) ≤ B := by
      apply Nat.le_of_mul_le_mul_right _ hq
      rw [Finset.sum_mul]
      exact (Finset.sum_le_sum fun i _ ↦ Nat.div_mul_le_self (e.val i).val q).trans
        (e.prop.trans hd)
    let quotient (i : Fin m) : Fin (B + 1) := ⟨(e.val i).val / q, Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun j _ ↦ Nat.zero_le ((e.val j).val / q))
        (Finset.mem_univ i)).trans hsum)⟩
    exact (⟨quotient, hsum⟩, fun i ↦ ⟨(e.val i).val % q, Nat.mod_lt _ hq⟩)
  inj' := by
    intro e f h
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hdiv : (e.val i).val / q = (f.val i).val / q :=
      congrArg (fun x : Simplex m B × (Fin m → Fin q) ↦ (x.1.val i).val) h
    have hmod : (e.val i).val % q = (f.val i).val % q :=
      congrArg (fun x : Simplex m B × (Fin m → Fin q) ↦ (x.2 i).val) h
    calc
      _ = (e.val i).val % q + q * ((e.val i).val / q) := (Nat.mod_add_div _ _).symm
      _ = _ := by rw [hmod, hdiv, Nat.mod_add_div]

/-- There are strictly more input monomials in the two blocks than there are
output monomials of the possible substituted degrees. -/
theorem perron_simplex_card_lt (m D : ℕ) :
    Fintype.card (Simplex m (perronSimplexBound m D * D)) <
      Fintype.card (Fin (perronRadius m D + 1) × Simplex m (perronRadius m D)) := by
  let B := perronRadius m D
  let q := 2 * (D + 1)
  have hq : 0 < q := Nat.mul_pos Nat.zero_lt_two (Nat.succ_pos D)
  have hd : perronSimplexBound m D * D ≤ B * q := by
    change 2 * B * D ≤ B * (2 * (D + 1))
    rw [Nat.mul_comm 2 B, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_succ _))
  have hle := Fintype.card_le_of_embedding (divideSimplex (m := m) hq hd)
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at hle ⊢
  change _ ≤ Fintype.card (Simplex m B) * B at hle
  have : Nonempty (Simplex m B) := ⟨⟨fun _ ↦ 0, by simp⟩⟩
  exact hle.trans_lt (by rw [Nat.mul_comm]; exact
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self B) Fintype.card_pos)

end RadicalCertificate

end VPVNP
end Computability
end OAI
