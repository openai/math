import OAI.Computability.BorderVNP.ShortenFramedPlacement
import OAI.Computability.BorderVNP.ShortenPackCatalogMean

/-!
# Preparing the short segment types and their canonical charts

For a fixed upper bound on all wire lengths, the relative sites determine a
finite list of types valid at every congruence level. We discard types longer
than the common upper bound before choosing a chart. This gives the same
positive scale throughout all the rounds of an epoch, including when the set
of relative sites changes after every profile replacement.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Epoch Cover Cover.Frame Hecke Set MeasureTheory Filter Packing
open scoped Topology Classical

variable {D : ℕ}

/-- The catalog radius measures exactly half of the distance between its two lifted endpoints. -/
theorem Catalog.SegmentType.dist_ends {I : Type*} [Fintype I] (s : Catalog.SegmentType I) :
    dist s.ends.1 s.ends.2 = 2*s.radius := by
  change dist (shiftTo s.center _) (shiftTo s.center _) = _
  rw [(shiftTo_isometry s.center).dist_eq,dist_productLine,s.unit,mul_one,
    show -s.radius-s.radius = -(2*s.radius) by ring,abs_neg,abs_of_nonneg (by linarith [s.positive])]

/-- Finite public geometric data chosen for one combining round. No field
coefficients, packet width, fan-in, cover level or profile histogram enter this list. -/
structure PreparedBins (D : ℕ) (S : Finset (HyperbolicHost (Cube D))) (h η : ℝ) where
  /-- Finite ordered type list. -/
  types : Finset (Catalog.SegmentType (Cube D))
  /-- One reserved public type provides an address for inactive cable descriptors. -/
  nonempty : types.Nonempty
  /-- Every prepared type is short at the common scale. -/
  short : ∀ t ∈ types, t.radius ≤ h
  /-- Every actual nonconstant cable of length at most `2h` appears at every level. -/
  represents : ∀ d (x y : SurfaceHost (Cube D) (d+1)),
    Catalog.relative d x ∈ S → Catalog.relative d y ∈ S → x ≠ y → dist x y ≤ 2*h →
    ∃ t ∈ types, Catalog.Realizes x y t.ends
  /-- The canonical chart at each prepared segment type. -/
  chart : ∀ t : types, BinChart D (Framed.relativeWindow (Cube D)) t.val.radius η
  /-- Even boundary representatives use the tie-resolved base tile. -/
  relative : ∀ t b, (chart t).center b ∈ Framed.relativeWindow (Cube D)
  /-- Every actual test is measurable, with Haar-null frontier. -/
  regular : ∀ (t : types) b, MeasurableSet ((chart t).code ⁻¹' {b}) ∧
    configurationLaw (productPositions (Cube D)) (Framed.speed t.val)
      (frontier ((chart t).code ⁻¹' {b})) = 0
  /-- Each signed direction action preserves the ideal bin masses. -/
  invariant : ∀ (t : types) j b,
    configurationLaw (productPositions (Cube D)) (Framed.speed t.val) ((chart t).code ⁻¹' {(chart t).perm j b}) =
    configurationLaw (productPositions (Cube D)) (Framed.speed t.val) ((chart t).code ⁻¹' {b})

/-- One common short scale works for every possible input catalog, even catalogs
arising from a different fan-in or an earlier stage in a physical epoch. -/
theorem exists_preparedBins {η : ℝ} (hη : 0 < η) :
    ∃ hMax > 0, ∀ h ∈ Ioc (0:ℝ) hMax, ∀ S : Finset (HyperbolicHost (Cube D)),
      Nonempty (PreparedBins D S h η) := by
  obtain ⟨hMax,hm,hbins⟩ := exists_binChart_subset (D := D) hη
  refine ⟨hMax,hm,?_⟩
  intro h hh S
  obtain ⟨V,hV,hcatalog⟩ := Catalog.finite_segments S.finite_toSet (2*h)
  let reserved : Catalog.SegmentType (Cube D) :=
    ⟨WithLp.toLp 2 (fun _ => UpperHalfPlane.I),PiLp.single 2 (fun _ => false) (1:ℂ),h,
      by rw [PiLp.norm_single,norm_one],hh.1⟩
  let V' := hV.toFinset.filter (fun t => t.radius ≤ h)
  let T := insert reserved V'
  have hshort (t) (ht : t ∈ T) : t.radius ≤ h := by
    rcases Finset.mem_insert.mp ht with he | he
    · subst t; exact le_rfl
    · exact (Finset.mem_filter.mp he).2
  let c₀ : HyperbolicHost (Cube D) := WithLp.toLp 2
    (fun _ => gammaSL 1 (toBaseTile UpperHalfPlane.I) • UpperHalfPlane.I)
  have hc₀ : c₀ ∈ Framed.relativeWindow (Cube D) := fun _ => toBaseTile_mem UpperHalfPlane.I
  have test (t : T) := hbins t.val.radius ⟨t.val.positive,(hshort t.val t.property).trans hh.2⟩
    (productPositions (Cube D)) (Framed.speed t.val) (Framed.window (Cube D)) Framed.window_compact
    (Framed.relativeWindow (Cube D)) Framed.relativeWindow_subset c₀ t.val.direction t.val.unit
  choose charts spec using test
  refine ⟨⟨T,Finset.insert_nonempty _ _,hshort,?_,charts,?_,fun t => (spec t).2.1,fun t => (spec t).2.2⟩⟩
  swap
  · intro t b
    rcases (spec t).1 b with hm | he
    · exact hm
    · simpa only [he] using hc₀
  intro d x y hx hy hne hxy
  obtain ⟨t,ht,hr⟩ := hcatalog d x y hx hy hne hxy
  have he := hr.choose_spec.2.2
  rw [t.dist_ends] at he
  exact ⟨t,Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hV.mem_toFinset.mpr ht,by linarith⟩),hr⟩

variable {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)

/-- The positive minimum length used to bound the midpoint bit concentration exists
also when the prepared catalog is empty. -/
theorem PreparedBins.exists_minLength : ∃ δ > 0, ∀ t : B.types, δ ≤ 2*t.val.radius := by
  by_cases hn : Nonempty B.types
  · let U := B.types.image (fun t => 2*t.radius)
    have hu : U.Nonempty := (show B.types.Nonempty from ⟨hn.some.val,hn.some.property⟩).image _
    refine ⟨U.min' hu,?_,fun t => Finset.min'_le _ _ (Finset.mem_image_of_mem _ t.property)⟩
    obtain ⟨t,_,he⟩ := Finset.mem_image.mp (U.min'_mem hu)
    rw [←he]; linarith [t.positive]
  · exact ⟨1,zero_lt_one,fun t => (hn ⟨t⟩).elim⟩

end Shortening

end BorderVNP
end Computability
end OAI
