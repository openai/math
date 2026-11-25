import OAI.Computability.BorderVNP.CubeScatterTransmissionRoutedDispatch
import OAI.Computability.BorderVNP.FiniteDiagonalCubeRawGrid

/-! # Field contraction over the full selector-bearing transmission and private tapes

The native row words replace the routed component of each actual cell layout.
The internal cable choices, private work slabs, exterior assignment and
profile index retain their original multiplicity. The bijection is applied
separately at each profile's true greedy team assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

set_option synthInstance.maxSize 2048

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter.Assignment
open scoped Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S)

/-- Checked common transmissions and chronological team words paired with the
original complete private vectors of all cells. -/
abbrev Transmitted (R : ℕ) :=
  {z : Routed.Words L.dimension L.alphabet (Fin (R+1)) // Routed.Accepts L.bitWidth L.supply (V.owners R) z} ×
    S.FlatWork L

/-- Exact replacement of the first component of the actual routed raw cube evaluator. -/
noncomputable def transmissionEquiv (R : ℕ) : V.Raw R ≃ V.Transmitted R :=
  (Routed.wordsEquiv (V.owners R) L.bitWidth L.supply).prodCongr (Equiv.refl _)


/-- One host, at arbitrary supplied port values, contracts to the sum over
its full received words and flat cell choices. This applies directly to an
already-sewn exterior host before summing over its profile. -/
theorem value_eq_transmitted (R : ℕ) (bank : Ports bits) :
    let e := V.transmissionEquiv R
    letI := Fintype.ofEquiv _ e
    N.value T bank = ∑ z : V.Transmitted R,
      let a := V.read R (e.symm z)
      S.pathValue L bank a.2 a.1 := by
  intro e
  let : Fintype (V.Transmitted R) := Fintype.ofEquiv _ e
  rw [S.value_eq_raw_sum L V.siteID (V.owners R) bank]
  exact (e.symm.sum_comp (fun q => let a := V.read R q; S.pathValue L bank a.2 a.1)).symm

end FiniteDiagonal.FieldRawLayout

namespace FinitePrewire

open Crossing Packing ParseBatch.Prewire TeamContraction FieldTeam FiniteDiagonal
open scoped BigOperators Classical

set_option synthInstance.maxSize 2048

variable {D R r t d link inner n b K h : ℕ} {Edge : Type} [Fintype Edge] {F : Type*} [Field F] [Fintype F]
variable (G : Wiring R r t d link inner n Edge) (teams : PackPorts Unit b K h ≃ Fin (R+1))
variable (H : ProfileSum (ValuedPack F D (packWidth (fun _ : Fin r × Fin (publicWidth G) => 1) b K h)))
variable (plans : ∀ i : H.Index, FieldPacketPlan (H.term i).1 F)
variable (dirs : ∀ i : H.Index, FieldSiteDirectory (H.term i).1 (H.term i).2)
variable (frames : ∀ i : H.Index, FieldRawLayout (plans i) (dirs i))

/-- Complete transmitted words on each profile of the physical exterior sum. -/
abbrev TransmittedTerm (R r link : ℕ) {P : Type} [Fintype P] {bits : P → ℕ}
    (H : ProfileSum (ValuedPack F D bits)) (plans : ∀ i : H.Index, FieldPacketPlan (H.term i).1 F)
    (dirs : ∀ i : H.Index, FieldSiteDirectory (H.term i).1 (H.term i).2)
    (frames : ∀ i : H.Index, FieldRawLayout (plans i) (dirs i)) :=
  (Exterior R r link → Bool) × (i : H.Index) × (frames i).Transmitted R

/-- The original raw grid term and every transmitted field remain in bijection, retaining exterior and profile. -/
noncomputable def transmittedTermEquiv :
    GridRawTerm R r link H plans dirs frames ≃ TransmittedTerm R r link H plans dirs frames :=
  (Equiv.refl _).prodCongr (Equiv.sigmaCongrRight fun i => (frames i).transmissionEquiv R)

/-- The original field contraction equals the sum over actual full shared
lists and independent native private tapes of the profile's greedy owners. -/
theorem field_contraction_eq_transmitted_words
    (B : ValuedPack F D (fun _ : Fin r × Fin (publicWidth G) => 1)) (pin : Fin d → Bool)
    (computes : ∀ ext team, B.tensor (fun p _ => publicBits G team pin ext p) = fieldValue G F pin ext team)
    (expand : ∀ ports, (unshortened B b K h).tensor ports = ∑ i, (H.term i).tensor ports) :
    let e := transmittedTermEquiv G H plans dirs frames
    letI := Fintype.ofEquiv _ e
    fieldContraction G F pin = ∑ z : TransmittedTerm R r link H plans dirs frames,
      rawValue G teams H plans dirs frames pin (e.symm z) := by
  intro e
  let : Fintype (TransmittedTerm R r link H plans dirs frames) := Fintype.ofEquiv _ e
  rw [field_contraction_eq_raw_values G teams H plans dirs frames B pin computes expand]
  exact (e.symm.sum_comp (rawValue G teams H plans dirs frames pin)).symm

end FinitePrewire

end BorderVNP
end Computability
end OAI
