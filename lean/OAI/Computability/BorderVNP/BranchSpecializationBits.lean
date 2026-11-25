import OAI.Computability.BorderVNP.BranchSpecializationBoundedClosure
import OAI.Computability.VPVNP.PerronBounds

/-!
# Polynomial bit length of the specialization prime

The determinant may have exponentially many binary digits. Its avoiding
prime has polynomially many, even for the effective separating-degree bound
obtained from a Perron relation. The size parameter here is the manuscript's
`M` in §9.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace BranchSpecialization

open VPVNP PolynomiallyBounded

/-- Polynomial parameter dimension and polynomial logarithms of the degree
and height allowances suffice for the row-specialization prime. -/
theorem polynomiallyBounded_primeExponent {h d D b e : ℕ → ℕ}
    (hh : PolynomiallyBounded h) (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n))
    (hD : PolynomiallyBounded fun n => Nat.clog 2 (D n))
    (hb : PolynomiallyBounded fun n => Nat.clog 2 (b n))
    (he : PolynomiallyBounded fun n => Nat.clog 2 (e n)) :
    PolynomiallyBounded fun n => primeExponent (h n) (d n) (D n) (b n) (e n) := by
  have ha := (clog_add (clog_mul hd hD) (.clog (.const 1))).mul hh
  exact ((PolynomiallyBounded.const 2).mul (ha.add
      (clog_add (clog_add (clog_add ha.clog (clog_mul hb hD)) he) (.clog (.const 2))))).add (.const 1)

/-- With the effective separating degree in `h+1` parameters, the resulting
prime exponent is still polynomially bounded. -/
theorem polynomiallyBounded_perron_primeExponent {h d b e : ℕ → ℕ}
    (hh : PolynomiallyBounded h) (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n))
    (hb : PolynomiallyBounded fun n => Nat.clog 2 (b n))
    (he : PolynomiallyBounded fun n => Nat.clog 2 (e n)) :
    PolynomiallyBounded fun n => primeExponent (h n) (d n)
      (2 * RadicalCertificate.perronSimplexBound (h n + 1) (d n + 1)) (b n) (e n) := by
  apply polynomiallyBounded_primeExponent hh hd _ hb he
  exact PolynomiallyBounded.clog_mul (.clog (.const 2))
    (RadicalCertificate.polynomiallyBounded_clog_perronSimplexBound (hh.add (.const 1))
      (PolynomiallyBounded.clog_add hd (.clog (.const 1))))

end BranchSpecialization

end BorderVNP
end Computability
end OAI
