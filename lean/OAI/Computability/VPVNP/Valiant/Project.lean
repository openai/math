import OAI.Computability.VPVNP.PermanentCompleteness
import OAI.Computability.VPVNP.PolynomialBounds
import OAI.Computability.VPVNP.Valiant.ProjectCircuitEquiv

/-! # Valiant's theorem in the project's exact arithmetic circuit model -/

namespace OAI
namespace Computability
namespace VPVNP

namespace Valiant.Project

variable {F : Type*} [Field F] {σ : ℕ → Type} [∀ n, Fintype (σ n)]

/-- A polynomial bound on realizable table sizes is equivalent to a bound on the
project's minimum gate counts. -/
theorem isVP_iff (p : Family F σ) : IsVP p ↔ VPVNP.IsVP p := by
  constructor
  · rintro ⟨hfamily, s, hs, h⟩
    refine ⟨hfamily, VPVNP.PolynomiallyBounded.of_le hs fun n => ?_⟩
    obtain ⟨c, hc⟩ := computes_iff.mp (h n)
    exact hc ▸ VPVNP.circuitSize_le_of_circuit c
  · rintro ⟨hfamily, hsize⟩
    exact ⟨hfamily, fun n => VPVNP.circuitSize (p n), hsize,
      fun n => computes_iff.mpr (VPVNP.circuitSize_spec (p n))⟩

/-- Identical Boolean witness substitutions and the same size bounds give identical VNP classes. -/
theorem isVNP_iff (p : Family F σ) : IsVNP p ↔ VPVNP.IsVNP p := by
  constructor
  · rintro ⟨hf, W, inst, g, hW, hg, h⟩
    exact ⟨hf, W, inst, g, hW, (isVP_iff g).mp hg, h⟩
  · rintro ⟨hf, W, inst, g, hW, hg, h⟩
    exact ⟨hf, W, inst, g, hW, (isVP_iff g).mpr hg, h⟩

omit [∀ n, Fintype (σ n)] in
/-- The source index, substitutions, and formal polynomial equalities in a projection
are definitionally the same as in the project. -/
theorem pProjects_iff {τ : ℕ → Type} (target : Family F τ) (source : Family F σ) :
    PProjects target source ↔ VPVNP.PProjects target source := Iff.rfl

/-- The standalone completeness predicate agrees with the original on every family. -/
theorem complete_iff (p : Family F σ) : VNPComplete p ↔ VPVNP.VNPComplete p := by
  constructor
  · rintro ⟨hp, hh⟩
    refine ⟨(isVNP_iff p).mp hp, fun τ _ g hg => ?_⟩
    exact (pProjects_iff g p).mp (hh τ g ((isVNP_iff g).mpr hg))
  · rintro ⟨hp, hh⟩
    refine ⟨(isVNP_iff p).mpr hp, fun τ _ g hg => ?_⟩
    exact (pProjects_iff g p).mpr (hh τ g ((isVNP_iff g).mp hg))

/-- Over every field of characteristic different from two, the permanent is VNP-complete. -/
theorem permanent_complete (F : Type*) [Field F] (hchar : ringChar F ≠ 2) :
    VNPComplete (permanent F) :=
  (complete_iff _).mpr (VPVNP.permanent_vnpComplete F (ringChar F) hchar)

end Valiant.Project

end VPVNP
end Computability
end OAI
