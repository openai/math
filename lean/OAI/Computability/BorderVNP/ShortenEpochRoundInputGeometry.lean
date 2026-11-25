import OAI.Computability.BorderVNP.ShortenEpochRoundPlacedInitial
import OAI.Computability.BorderVNP.ShortenCatalogBounds
import OAI.Computability.BorderVNP.ShortenCatalogProgram

/-!
# Finite relative catalogs of the exact starting subdivision

The relative site alphabet contains the origin and the catalog hop ends.
An oriented catalog segment and one common integral translation recover
both physical cable endpoints and their selected midpoint. At every
sufficiently deep level the cable has its exact positive catalog length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.SiteRoutes

open BorderVNP.Shortening BorderVNP.Shortening.Catalog BorderVNP.Crossing BorderVNP.Epoch Finset
open scoped Classical

variable {I P : Type} [Fintype I] {D d : ℕ} {bits : P → ℕ} {R : Type*} [CommSemiring R]
  {L h : ℝ} {p : Pack D P bits R}

/-- Oriented segment type of one fixed catalog hop. -/
noncomputable def hopType (hh : 0 < h) (t : Hop I L h) : SegmentType I where
  center := (framedHop hh t).center
  direction := (framedHop hh t).direction
  unit := (framedHop hh t).unit
  radius := hopLength h t.1 / 2
  positive := half_pos (hopLength_bounds hh t.1).1

/-- The finite normalized site catalog, including all inserted equality sites. -/
noncomputable def startingSites (I : Type) [Fintype I] (L h : ℝ) : Finset (HyperbolicHost I) :=
  insert (normalize (productOrigin I)) (univ.image (fun t : Hop I L h => normalize (hopPosition t 1)))

/-- Site locations of the real starting network are in the fixed relative site alphabet. -/
theorem initial_site_catalog (s : SiteRoutes p I d L) (hh : 0 < h) (v : (s.initialPlacedPack hh).pack.layout.Site) :
    relative d ((s.initialPlacedPack hh).site v) ∈ startingSites I L h := by
  classical
  rcases v with v | ⟨e,j⟩
  · change relative d (productProjection _ (translatePoint _ (productOrigin I))) ∈ _
    rw [relative_projection,normalize_translate]
    exact mem_insert_self _ _
  · by_cases he : s.active e
    · change relative d (s.physical h (.inr ⟨e,j⟩)) ∈ _
      rw [s.physical_equality he,relative_projection,normalize_translate]
      exact mem_insert_of_mem (mem_image.mpr ⟨_,mem_univ _,rfl⟩)
    · have hj := j.isLt
      simp [routes,he] at hj

/-- One cutoff works for all depths, all inputs and all active subdivided cables. Each
entry identifies its two true endpoints and its true selected midpoint by a single
common tile translation, and realizes the exact catalog length. -/
theorem initial_framed_catalog (I : Type) [Fintype I] {L h : ℝ} (hh : 0 < h) :
    ∃ l, ∀ d, l ≤ d+1 → ∀ {D : ℕ} {P : Type} {bits : P → ℕ} {R : Type*} [CommSemiring R]
      {p : Pack D P bits R} (s : SiteRoutes p I d L),
      let initial := s.initialPlacedPack hh
      ∀ e : initial.pack.layout.Edge, initial.charged e = true →
      ∃ (t : Hop I L h) (a : I → gamma 1),
        productProjection (d+1) (translatePoint a (hopType hh t).ends.1) = initial.site (initial.pack.layout.src e) ∧
        productProjection (d+1) (translatePoint a (hopType hh t).ends.2) = initial.site (initial.pack.layout.dst e) ∧
        productProjection (d+1) (translatePoint a (hopType hh t).center) = initial.midpoint e ∧
        dist (initial.site (initial.pack.layout.src e)) (initial.site (initial.pack.layout.dst e)) =
          2*(hopType hh t).radius ∧ 2*(hopType hh t).radius ≤ h := by
  obtain ⟨l,hl⟩ := eventually_hop_length (I := I) (L := L) hh
  refine ⟨l,?_⟩
  intro d hd D P bits R _ p s initial e he
  rcases e with ⟨c,j⟩
  change s.active c = true at he
  let t : Hop I L h := (s.step c he,⟨j.val,s.hop_index he j⟩)
  let a := s.origin (p.layout.src c)
  have ha := s.physical_source he j
  have hb := s.physical_target he j
  have hleft : (hopType hh t).ends.1 = hopPosition t 0 := (framedHop hh t).first
  have hright : (hopType hh t).ends.2 = hopPosition t 1 := (framedHop hh t).last
  refine ⟨t,a,?_,?_,?_,?_,?_⟩
  · rw [hleft]; exact ha.symm
  · rw [hright]; exact hb.symm
  · change _ = if he' : s.active c then _ else _
    simp only [he,reduceDIte]
    rfl
  · change dist (s.physical h ((p.layout.subdivide (s.routes h)).src ⟨c,j⟩))
      (s.physical h ((p.layout.subdivide (s.routes h)).dst ⟨c,j⟩)) = 2*(hopType hh t).radius
    rw [ha,hb]
    exact (hl (d+1) hd a t).trans (by change _ = 2*(hopLength h t.1/2); ring)
  · change 2*(hopLength h t.1/2) ≤ h
    linarith [(hopLength_bounds hh t.1).2]

private theorem center_to_first (t : SegmentType I) : dist t.center t.ends.1 = t.radius := by
  have zero : productLine t.direction 0 = productChart 0 := by
    ext1 i
    change tangentLine (unitDirection (t.direction i)) (0 * ‖t.direction i‖) = tangentChart 0
    simp [tangentLine]
  have hc := (congrArg (shiftTo t.center) zero).trans (shiftTo_chart_zero _)
  calc
    _ = dist (shiftTo t.center (productLine t.direction 0))
        (shiftTo t.center (productLine t.direction (-t.radius))) := congrArg (fun x => dist x _) hc.symm
    _ = _ := by rw [(shiftTo_isometry _).dist_eq,dist_productLine,zero_sub,neg_neg,abs_of_pos t.positive,t.unit,mul_one]

/-- The physical input of the prepared epoch satisfies its full three-part catalog predicate
at every sufficiently deep level, uniformly in the starting site pack. -/
theorem initial_placedAt (I : Type) [Fintype I] {L h : ℝ} (hh : 0 < h) :
    ∃ floor, ∀ d, floor ≤ d+1 → ∀ {D : ℕ} {P : Type} {bits : P → ℕ} {R : Type*} [CommSemiring R]
      {p : Pack D P bits R} (s : SiteRoutes p I d L),
        PlacedAt (startingSites I L h) h (s.initialPlacedPack hh) := by
  obtain ⟨l,hl⟩ := initial_framed_catalog (L := L) I hh
  refine ⟨l,?_⟩
  intro d hd D P bits R _ p s
  refine ⟨s.initial_site_catalog hh,?_,?_⟩
  · intro e he
    obtain ⟨t,_,_,_,_,hdist,hlen⟩ := hl d hd s e he
    exact hdist.le.trans (hlen.trans (by linarith))
  · intro e he
    obtain ⟨t,a,hs,_,hm,hdist,_⟩ := hl d hd s e (((s.initialPlacedPack hh).active_iff _).mp he).1
    rw [hdist,← hm,← hs]
    apply (productProjection_dist_le _ _ _).trans
    rw [(translatePoint_isometry a).dist_eq,center_to_first]
    linarith

end Cover.SiteRoutes

end BorderVNP
end Computability
end OAI
