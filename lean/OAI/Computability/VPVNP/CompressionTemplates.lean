import OAI.Computability.VPVNP.CompressionSchedule
import OAI.Computability.VPVNP.ShrinkMotif
import OAI.Computability.VPVNP.DegreeRefreshPass
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# The fixed equations for one compressor block

The shrinking identities all use the same six-party template, independently
of the base degree. The degree refresh uses one template on the chosen
port graph. Tagging their parameter and equation indices gives a single
finite system over the integers, fixed before the input network or the
number of iterations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule

open MotifBlocks MotifGrid MotifConversion

variable {k : Type*} [Field k] (S : BlockSchedule k)

/-- Port order exponent at the last shrinking step. -/
abbrev portExponent := S.degreeExponent (Fin.last S.steps)

/-- Comparison constant for the internal port demands, before the unit slack. -/
noncomputable def portComparison : ℝ := 2 * S.poincare * S.baseDegree / (2 ^ S.expanderExponent : ℕ)

theorem portComparison_pos : 0 < S.portComparison := by
  unfold portComparison baseDegree
  positivity [S.poincare_pos]

/-- The expander as the connected supply motif for the fixed refresh graph. -/
noncomputable abbrev portSupply := Refresh.expanderSupply S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1

/-- The two families of base maps and all their widths. -/
structure Templates where
  /-- Fixed six-party block used for the local wire identity at each shrinking substep. -/
  shrink : FixedBlock k ShrinkMotif.demandSource ShrinkMotif.demandTarget ShrinkMotif.supply
    (realWidths ShrinkMotif.demandMass) (realWidths ShrinkMotif.supplyMass)
    (31 / 16) shrinkComparison
  /-- Fixed block implementing the refresh identity on the schedule's chosen port graph. -/
  refresh : DegreeRefresh.RefreshBlock k S.portSupply S.baseDegree
    S.portComparison (S.portComparison + 1)

/-- Both templates exist over the field in which the spectral bound was established. -/
theorem exists_templates : Nonempty S.Templates := by
  obtain ⟨A⟩ := ShrinkMotif.exists_block (k := k) shrink_constants.1
  obtain ⟨B⟩ := Refresh.exists_expander_block S.graph (Nat.two_pow_pos _) S.port_order
    (show 0 < S.baseDegree from Nat.two_pow_pos _) S.port_bound
  exact ⟨⟨A, B⟩⟩

namespace Templates

variable {S} (P : S.Templates)

/-- Parameter indices of the joint equation system, tagged by the shrinking or refresh block
they belong to. -/
abbrev Entry := (parameterData P.shrink).Entry ⊕ (parameterData P.refresh).Entry

/-- Output-equation indices of the joint system, tagged by which of the two fixed blocks
supplies the equation. -/
abbrev EquationIndex := (parameterData P.shrink).Output ⊕ (parameterData P.refresh).Output

instance : Finite P.Entry := by unfold Entry; infer_instance
instance : Finite P.EquationIndex := by unfold EquationIndex; infer_instance

/-- Distinct variable names for the two sets of integral equations. -/
noncomputable def equation (o : P.EquationIndex) : MvPolynomial P.Entry ℤ :=
  match o with
  | .inl z => MvPolynomial.rename Sum.inl ((parameterData P.shrink).equation z)
  | .inr z => MvPolynomial.rename Sum.inr ((parameterData P.refresh).equation z)

/-- Simultaneous vanishing of the fixed template equations in a coefficient ring. -/
def IsSolution {R : Type*} [CommRing R] (f : P.Entry → R) : Prop :=
  ∀ o, MvPolynomial.eval₂Hom (Int.castRingHom R) f (P.equation o) = 0

theorem solution_iff {R : Type*} [CommRing R] (f : P.Entry → R) :
    P.IsSolution f ↔ (parameterData P.shrink).IsSolution (f ∘ Sum.inl) ∧
      (parameterData P.refresh).IsSolution (f ∘ Sum.inr) := by
  constructor
  · intro h
    exact ⟨fun o => by simpa only [equation, MvPolynomial.eval₂Hom_rename] using h (.inl o),
      fun o => by simpa only [equation, MvPolynomial.eval₂Hom_rename] using h (.inr o)⟩
  · rintro ⟨h₁, h₂⟩ (o | o)
    · exact (MvPolynomial.eval₂Hom_rename ..).trans (h₁ o)
    · exact (MvPolynomial.eval₂Hom_rename ..).trans (h₂ o)

theorem exists_solution : ∃ f : P.Entry → k, P.IsSolution f := by
  obtain ⟨f, hf⟩ := MotifConversion.exists_solution P.shrink
  obtain ⟨g, hg⟩ := MotifConversion.exists_solution P.refresh
  exact ⟨Sum.elim f g, (P.solution_iff _).2 ⟨hf, hg⟩⟩

end Templates
end Compression.BlockSchedule

end VPVNP
end Computability
end OAI
