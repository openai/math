import OAI.Optimization.LinearProgramming.OracleSpec.Companion
import OAI.Optimization.LinearProgramming.Geometry.Admissible
import OAI.Optimization.LinearProgramming.Geometry.LabelBasis
import OAI.Optimization.LinearProgramming.Geometry.BorderWire

/-! Transport the sealed, finitely supported four-term comparison to the
dense finite-index form used by the geometric estimates. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open OracleSpec BorderBatch Compression
open scoped BigOperators

private theorem public_index_roundtrip {r s n : ℕ} (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (u : MinorLog.Index D E) :
    interfaceIndex D E (MinorLog.indexEquiv D E u)=u := by
  rcases u with ⟨u,hu⟩
  cases u <;> rename_i sq <;> cases sq <;> rfl

/-- The canonical compression contract gives the signed four-minor comparison
used in Section 2, including its precise base-two error and cutoff. -/
theorem fourLogAccuracy_of_sparse {r s n : ℕ} (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (F : MinorLog.Index D E → ℚ)
    (h : ∀ a : MinorLog.Index D E →₀ ℤ, a.sum (fun _ c => c.natAbs) ≤ 4 →
      |MinorLog.clip (MinorLog.threshold n) (a.sum (fun u c => (c : ℝ)*(F u : ℝ))) -
        MinorLog.clip (MinorLog.threshold n) (a.sum (fun u c => (c : ℝ)*MinorLog.logarithm D E u))| ≤
        (1/2 : ℝ)^(MinorLog.threshold n)) :
    FourLogAccuracy (geoCutoff n : ℝ) (pairMinorLog D E) (fun u => (F (interfaceIndex D E u) : ℝ)) := by
  classical
  let e := MinorLog.indexEquiv D E
  let : Fintype (MinorLog.Index D E) := Fintype.ofEquiv _ e.symm
  intro z hz
  let a : MinorLog.Index D E →₀ ℤ := Finsupp.equivFunOnFinite.symm (fun u => z (e u))
  have mass : ∑ u, (z u).natAbs ≤ 4 := by
    have hc : (∑ u, |(z u : ℝ)|) = ((∑ u, (z u).natAbs : ℕ) : ℝ) := by
      push_cast
      simp only [Nat.cast_natAbs,Int.cast_abs]
    rw [hc] at hz
    exact_mod_cast hz
  have ha : a.sum (fun _ c => c.natAbs) ≤ 4 := by
    rw [a.sum_fintype (fun _ c => c.natAbs) (fun _ => rfl)]
    change (∑ u, (z (e u)).natAbs) ≤ 4
    rw [e.sum_comp (fun u => (z u).natAbs)]
    exact mass
  have form (g : NonzeroPairMinor D E → ℝ) :
      a.sum (fun u c => (c : ℝ) * g (e u)) = intForm z g := by
    rw [a.sum_fintype (fun u c => (c : ℝ)*g (e u)) (fun _ => by simp)]
    exact e.sum_comp (fun u => (z u : ℝ)*g u)
  have logs (u : MinorLog.Index D E) : pairMinorLog D E (e u)=MinorLog.logarithm D E u := by
    simp only [pairMinorLog,MinorLog.logarithm,e,MinorLog.indexEquiv_minor]
  have inds (u : MinorLog.Index D E) : interfaceIndex D E (e u)=u := public_index_roundtrip D E u
  have err : (2:ℝ)^(-(geoCutoff n : ℝ))=(1/2:ℝ)^(MinorLog.threshold n) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,one_div,inv_pow]
    rfl
  rw [err,←form (fun u => (F (interfaceIndex D E u) : ℝ)),←form (pairMinorLog D E)]
  simpa only [inds,logs,Compression.clip,MinorLog.clip,geoCutoff,MinorLog.threshold] using h a ha

end Geometry
end LinearProgramming
end Optimization
end OAI
