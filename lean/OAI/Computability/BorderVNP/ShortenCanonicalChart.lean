import OAI.Computability.BorderVNP.ShortenEpochCrossingBins
import OAI.Computability.BorderVNP.ShortenAddressCost

/-!
# Choosing canonical representatives for occupied crossing bins

The seed bin itself can be empty in the moved pack. If any selected bin
`A_j b` contains a unit segment, involutivity of its signed flip nevertheless
provides a unit representative of `b` in the same center window. The choice
therefore works at every matched slot. Unoccupied seeds can use a fixed
fallback point and unit direction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Epoch Crossing Set
open scoped Classical

variable {D : ℕ}

/-- A public seed's actual signed endpoint, with the negative port denoted by `true`. -/
noncomputable def endpoint (c : HyperbolicHost (Cube D)) (v : Direction D ℂ) (s : ℝ) (neg : Bool) :=
  shiftTo c (productLine (if neg then -v else v) s)

/-- Finite relative tests and canonical seed sites at one scale and speed class. -/
structure BinChart (D : ℕ) (window : Set (HyperbolicHost (Cube D))) (s η : ℝ) where
  /-- Number of relative bin names. -/
  bins : ℕ
  /-- Actual bin test, evaluated on a center and its whole product direction. -/
  code : HyperbolicHost (Cube D) × Direction D ℂ → Fin bins
  /-- Direction action on the finite names. -/
  perm : Fin D → Equiv.Perm (Fin bins)
  /-- This code transforms under the actual signed axis maps. -/
  equivariant : ∀ j c v, code (c,signedFlip j v) = perm j (code (c,v))
  /-- Chosen center for every seed. -/
  center : Fin bins → HyperbolicHost (Cube D)
  /-- Chosen unit direction giving all the perpendicular axes at once. -/
  vector : Fin bins → Direction D ℂ
  /-- Each chosen direction has unit norm. -/
  unit : ∀ b, ‖vector b‖ = 1
  /-- Each slot in a matched direction has the correct signed terminal tolerance. -/
  close : ∀ b j, ∀ c ∈ window, ∀ v : Direction D ℂ, ‖v‖ = 1 → code (c,v) = perm j b →
    ∀ sign, dist (endpoint c v s sign) (endpoint (center b) (signedFlip j (vector b)) s sign) ≤ η*s

/-- The physical Euclidean gadget is embedded along the perpendicular signed-flip axes. -/
noncomputable def BinChart.seed {window : Set (HyperbolicHost (Cube D))} {s η : ℝ}
    (C : BinChart D window s η) (b : Fin C.bins) : SeedChart (Cube D) D :=
  ⟨s,crossingAxes (C.vector b) (C.unit b),C.center b⟩

/-- The terminal positions of the actual gadget are the two signed geodesic endpoints. -/
theorem BinChart.terminal_eq {window : Set (HyperbolicHost (Cube D))} {s η : ℝ}
    (C : BinChart D window s η) (b : Fin C.bins) (j : Fin D) (neg : Bool) :
    (C.seed b).atTerminal (j,neg) = endpoint (C.center b) (signedFlip j (C.vector b)) s neg := by
  cases neg <;> simp [SeedChart.atTerminal,BinChart.seed,antipodalPosition,endpoint,crossingAxes_axis]

/-- Canonical representatives exist at every sufficiently short scale, with the
Haar-null frontier and invariant masses of the same tests used in the motion law. -/
theorem exists_binChart_subset {η : ℝ} (hη : 0 < η) :
    ∃ h > 0, ∀ s ∈ Ioc (0:ℝ) h, ∀ (position : MeasureTheory.Measure (HyperbolicHost (Cube D)))
      [MeasureTheory.SFinite position] (speed : Cube D → ℝ)
      (window : Set (HyperbolicHost (Cube D))), IsCompact window →
      ∀ (allowed : Set (HyperbolicHost (Cube D))), allowed ⊆ window →
      ∀ (c₀ : HyperbolicHost (Cube D)) (u₀ : Direction D ℂ), ‖u₀‖ = 1 →
      ∃ C : BinChart D allowed s η,
        (∀ b, C.center b ∈ allowed ∨ C.center b = c₀) ∧
        (∀ b, MeasurableSet (C.code ⁻¹' {b}) ∧
          configurationLaw position speed (frontier (C.code ⁻¹' {b})) = 0) ∧
        (∀ j b, configurationLaw position speed (C.code ⁻¹' {C.perm j b}) =
          configurationLaw position speed (C.code ⁻¹' {b})) := by
  obtain ⟨h,hh,hbins⟩ := canonical_crossing_bins (D := D) hη
  refine ⟨h,hh,?_⟩
  intro s hs pos inst speed window hwin allowed hal c₀ u₀ hu₀
  obtain ⟨n,code,A,ha,hnull,hinv,_,hnear⟩ := hbins s hs pos speed hwin
  let good (b : Fin n) (x : HyperbolicHost (Cube D) × Direction D ℂ) :=
    x.1 ∈ allowed ∧ ‖x.2‖ = 1 ∧ code x = b
  let rep (b : Fin n) := if H : ∃ x, good b x then H.choose else (c₀,u₀)
  have hrs (b : Fin n) (H : ∃ x, good b x) : good b (rep b) := by simpa only [rep,dite_eq_left H] using H.choose_spec
  have hu (b : Fin n) : ‖(rep b).2‖ = 1 := by
    by_cases H : ∃ x, good b x
    · exact (hrs b H).2.1
    · simpa only [rep,dite_eq_right H] using hu₀
  refine ⟨⟨n,code,A,ha,fun b => (rep b).1,fun b => (rep b).2,hu,?_⟩,?_,hnull,hinv⟩
  swap
  · intro b
    by_cases H : ∃ x, good b x
    · exact Or.inl (hrs b H).1
    · exact Or.inr (by simp only [rep,dite_eq_right H])
  intro b j c hc v hv hcode sign
  have hx : code (c,signedFlip j v) = b := by
    apply (A j).injective
    rw [← ha, signedFlip_involutive]
    exact hcode
  have hr := hrs b ⟨(c,signedFlip j v),hc,(signedFlip_orthonormal v hv).1 j,hx⟩
  have hsame : code (c,v) = code ((rep b).1,signedFlip j (rep b).2) := by rw [ha,hr.2.2,hcode]
  have hterminal := hnear c (hal hc) (rep b).1 (hal hr.1) v (signedFlip j (rep b).2) hv.le
    ((signedFlip_orthonormal _ (hu b)).1 j).le hsame (!sign)
  cases sign <;> exact hterminal

/-- Canonical charts for the full compact center window. -/
theorem exists_binChart {η : ℝ} (hη : 0 < η) :
    ∃ h > 0, ∀ s ∈ Ioc (0:ℝ) h, ∀ (position : MeasureTheory.Measure (HyperbolicHost (Cube D)))
      [MeasureTheory.SFinite position] (speed : Cube D → ℝ)
      (window : Set (HyperbolicHost (Cube D))), IsCompact window →
      ∀ (u₀ : Direction D ℂ), ‖u₀‖ = 1 →
      ∃ C : BinChart D window s η,
        (∀ b, MeasurableSet (C.code ⁻¹' {b}) ∧
          configurationLaw position speed (frontier (C.code ⁻¹' {b})) = 0) ∧
        (∀ j b, configurationLaw position speed (C.code ⁻¹' {C.perm j b}) =
          configurationLaw position speed (C.code ⁻¹' {b})) := by
  obtain ⟨h,hh,hbin⟩ := exists_binChart_subset (D := D) hη
  refine ⟨h,hh,?_⟩
  intro s hs pos inst speed window hwin u₀ hu₀
  obtain ⟨C,_,hreg,hinv⟩ := hbin s hs pos speed window hwin window Subset.rfl
    (WithLp.toLp 2 (fun _ => UpperHalfPlane.I)) u₀ hu₀
  exact ⟨C,hreg,hinv⟩

end Shortening

end BorderVNP
end Computability
end OAI
