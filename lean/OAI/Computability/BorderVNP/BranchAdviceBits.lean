import OAI.Computability.BorderVNP.BranchFiniteCuts
import OAI.Computability.BorderVNP.BranchTarget
import OAI.Computability.VPVNP.LogBounds

/-! # Bit lengths of the finite fields used to choose the branch

The parameter count and degree are polynomial in the paper's size parameter `M`.
The number of output coordinates and their scalar exponents can be exponential. Every
extension-cardinality threshold used to choose the slices and the displacement vector
has polynomial binary logarithm under precisely these bounds.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open VPVNP VPVNP.RadicalCertificate

private theorem clog_max {f g : ℕ → ℕ}
    (hf : PolynomiallyBounded (fun m ↦ Nat.clog 2 (f m)))
    (hg : PolynomiallyBounded (fun m ↦ Nat.clog 2 (g m))) :
    PolynomiallyBounded (fun m ↦ Nat.clog 2 (max (f m) (g m))) :=
  (PolynomiallyBounded.clog_add hf hg).of_le fun m ↦ Nat.clog_mono_right _ (by omega)

private theorem perron_clog {h d : ℕ → ℕ} (hh : PolynomiallyBounded h)
    (hd : PolynomiallyBounded (fun m ↦ Nat.clog 2 (d m))) :
    PolynomiallyBounded (fun m ↦ Nat.clog 2 (perronSimplexBound (h m) (d m))) := by
  let c := fun k ↦ (PolynomiallyBounded.const k).clog
  exact PolynomiallyBounded.clog_mul (c 2) (PolynomiallyBounded.clog_pow
    (PolynomiallyBounded.clog_mul (c 2) (PolynomiallyBounded.clog_add hd (c 1))) hh)

private theorem fiber_pin_clog {h d : ℕ → ℕ} (hh : PolynomiallyBounded h)
    (hd : PolynomiallyBounded (fun m ↦ Nat.clog 2 (d m))) :
    PolynomiallyBounded (fun m ↦ Nat.clog 2 (fiberPinBound (h m) (d m))) := by
  let c := PolynomiallyBounded.const
  have hH := PolynomiallyBounded.clog_pow (PolynomiallyBounded.clog_mul (c 2).clog hd)
    ((c 4).mul (hh.add (c 2)))
  exact PolynomiallyBounded.clog_mul (c 2).clog (PolynomiallyBounded.clog_pow
    (PolynomiallyBounded.clog_add (PolynomiallyBounded.clog_add hH hd) (c 1).clog) hh)

private theorem mixture_clog {h d B n : ℕ → ℕ} (hh : PolynomiallyBounded h)
    (hd : PolynomiallyBounded d) (hB : PolynomiallyBounded (fun m ↦ Nat.clog 2 (B m)))
    (hn : PolynomiallyBounded (fun m ↦ Nat.clog 2 (n m))) :
    PolynomiallyBounded (fun m ↦ Nat.clog 2 (mixtureBound (h m) (B m) (n m) (d m))) := by
  let c := PolynomiallyBounded.const
  have hrad := PolynomiallyBounded.clog_pow (PolynomiallyBounded.clog_mul
    (clog_max hB (c 1).clog) (((hh.add (c 1)).mul hd).add (c 1)).clog) hh
  exact PolynomiallyBounded.clog_mul (PolynomiallyBounded.clog_mul hB hn)
    (PolynomiallyBounded.clog_mul (hh.add (c 1)).clog hrad)

/-- The finite constant grid for all fiber cuts has polynomial bit length, even with
exponentially many output coordinates and exponentially large slice exponents. -/
theorem sliceGridBound_clog {h d B n : ℕ → ℕ} (hh : PolynomiallyBounded h)
    (hd : PolynomiallyBounded d) (hB : PolynomiallyBounded (fun m ↦ Nat.clog 2 (B m)))
    (hn : PolynomiallyBounded (fun m ↦ Nat.clog 2 (n m))) :
    PolynomiallyBounded (fun m ↦ Nat.clog 2 (sliceGridBound (h m) (d m) (B m) (n m))) := by
  let c := PolynomiallyBounded.const
  have hgeom := clog_max (c 3).clog (PolynomiallyBounded.clog_mul (c 2).clog
    (perron_clog (hh.add (c 2)) (hd.add (c 3)).clog))
  exact clog_max (fiber_pin_clog (hh.add (c 1)) hgeom) (mixture_clog hh (hd.add (c 1))
    (PolynomiallyBounded.clog_add (PolynomiallyBounded.clog_add hB hh.clog) (c 1).clog)
    (PolynomiallyBounded.clog_add (hh.add (c 1)).clog hn))

/-- The exceptional polynomial in the generic displacement variables has singly
exponential degree, measured in the same size parameter as the grid for the fiber. -/
theorem displacementDegree_clog {h d r : ℕ → ℕ} (hh : PolynomiallyBounded h)
    (hd : PolynomiallyBounded d) (hr : PolynomiallyBounded r) :
    PolynomiallyBounded (fun m ↦ Nat.clog 2 (displacementDegree (h m) (d m) (r m))) := by
  let c := PolynomiallyBounded.const
  exact perron_clog (hh.add (c 1))
    ((((hh.mul ((c 2).mul hr)).add (c 1)).mul (hd.add (c 1))).add (c 1)).clog

/-- Each extension produced by the grid construction keeps polynomial bit length. -/
theorem grid_field_card_clog {q e D : ℕ → ℕ}
    (hq : PolynomiallyBounded (fun m ↦ Nat.clog 2 (q m)))
    (hD : PolynomiallyBounded (fun m ↦ Nat.clog 2 (D m)))
    (he : ∀ m, e m ≤ q m * max (D m) 1) :
    PolynomiallyBounded (fun m ↦ Nat.clog 2 (e m)) :=
  (PolynomiallyBounded.clog_mul hq (clog_max hD (PolynomiallyBounded.const 1).clog)).of_le
    fun m ↦ Nat.clog_mono_right _ (he m)

/-- The entire matrix of row advice (one scalar, offset, target and `h` slopes per row)
requires polynomially many bits over the final field. -/
theorem slice_advice_bits {h e : ℕ → ℕ} (hh : PolynomiallyBounded h)
    (he : PolynomiallyBounded (fun m ↦ Nat.clog 2 (e m))) :
    PolynomiallyBounded (fun m ↦ h m * (h m + 3) * Nat.clog 2 (e m)) :=
  (hh.mul (hh.add (PolynomiallyBounded.const 3))).mul he

end Branch

end BorderVNP
end Computability
end OAI
