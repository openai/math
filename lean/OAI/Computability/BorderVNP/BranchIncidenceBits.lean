import OAI.Computability.BorderVNP.BranchIncidenceCount

/-! # Field size for simultaneous incidence exclusions

For all strata and graph coordinates together, the number of excluded
hypersurfaces is at most the product of the slice polynomial degree and
the ambient graph dimension. Multiplying by the bound for each relation
preserves a singly exponential grid bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch.Incidence

open VPVNP

/-- A larger stratum degree only increases the allowed incidence box. -/
theorem radius_mono_stratum (h d : ℕ) {r B : ℕ} (hr : r ≤ B) :
    radius h r d ≤ radius h B d :=
  Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (max_le_max_right 1 hr)) h

/-- The bit length of the grid size bound is polynomial when the graph
dimension and stratum cutoff have polynomial bit length and the number
of independent parameters is polynomially bounded. -/
theorem polynomiallyBounded_clog_gridBound {h B coords d : ℕ → ℕ}
    (hh : PolynomiallyBounded h) (hB : PolynomiallyBounded fun n => Nat.clog 2 (B n))
    (hc : PolynomiallyBounded fun n => Nat.clog 2 (coords n))
    (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n)) :
    PolynomiallyBounded fun n => Nat.clog 2
      (B n * coords n * ((h n+1)*radius (h n) (B n) (d n))) := by
  have hs := (hh.add (.const 1)).clog
  have hone := (PolynomiallyBounded.const 1).clog
  have hm : PolynomiallyBounded fun n => Nat.clog 2 (max (B n) 1) :=
    (PolynomiallyBounded.clog_add hB hone).of_le fun n =>
      Nat.clog_mono_right 2 (by omega)
  have hr := PolynomiallyBounded.clog_pow (PolynomiallyBounded.clog_mul hm
    (PolynomiallyBounded.clog_add (PolynomiallyBounded.clog_mul hs hd) hone)) hh
  exact PolynomiallyBounded.clog_mul (PolynomiallyBounded.clog_mul hB hc)
    (PolynomiallyBounded.clog_mul hs hr)

end Branch.Incidence

end BorderVNP
end Computability
end OAI
