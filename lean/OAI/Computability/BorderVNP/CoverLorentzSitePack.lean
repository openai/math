import OAI.Computability.BorderVNP.CoverLorentzSubdivisionCounts
import OAI.Computability.BorderVNP.PackedSubdivision
import OAI.Computability.BorderVNP.ShortenNetworkHistory
import OAI.Computability.BorderVNP.ShortenNetworkHost

/-!
# Subdividing the charged cables of a site pack

At an initial site each charged cable has an allowed move from its starting
address to its final address. The identity subdivision retains every external
port, gives every hop a fresh shared index, and inserts equality tables only on
charged wires. The independent physical placement of the resulting network
uses the corresponding translated geodesic catalog.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open BorderVNP.Epoch BorderVNP.Shortening BorderVNP.Crossing
open scoped Classical

variable {I : Type*} [Fintype I] {L h : ℝ} {D d : ℕ} {P R : Type*} {bits : P → ℕ}

/-- Concrete site addresses and allowed moves for the designated charged edges. -/
structure SiteRoutes (p : Pack D P bits R) (I : Type*) [Fintype I] (d : ℕ) (L : ℝ) where
  /-- Integral representatives of the product site addresses. -/
  origin : p.layout.Site → I → gamma 1
  /-- Exactly the nonlocal charged cables to subdivide. -/
  active : p.layout.Edge → Bool
  /-- Each such wire is one of the fixed site moves. -/
  step : (e : p.layout.Edge) → active e → allowedMoves I L
  /-- Final and initial tile addresses agree with the registered move at this cover level. -/
  aligned : ∀ e (he : active e), reduceMove d (origin (p.layout.dst e)) =
    reduceMove d (origin (p.layout.src e)) * reduceMove d (step e he).val

namespace SiteRoutes

variable {p : Pack D P bits R} (r : SiteRoutes p I d L)

/-- Equality sites for internal index subdivision. Placement in the hyperbolic host is
provided separately by `physical`, as in the general pack representation. -/
noncomputable def routes (h : ℝ) : Network.WireRoutes p.layout where
  interior e := if r.active e then ⌈L/h⌉₊ else 0
  place _ _ := ⟨0,by simp⟩

/-- The exact pack with the equality factors and all the split cable indices. -/
noncomputable def subdivided [CommSemiring R] (h : ℝ) : Pack D P bits R :=
  ⟨p.layout.subdivide (r.routes h),p.layout.subdivideTables (r.routes h) p.table⟩

/-- Subdivision preserves the complete tensor on all external port assignments. -/
theorem tensor_subdivided [CommSemiring R] (h : ℝ) : (r.subdivided h).tensor = p.tensor := by
  funext x
  exact p.layout.value_subdivide (r.routes h) p.table x

/-- The product site corresponding to the address of an original pack vertex. -/
noncomputable def site (v : p.layout.Site) : SurfaceHost I (d+1) :=
  productProjection (d+1) (translatePoint (r.origin v) (productOrigin I))

private theorem site_of_move {e : p.layout.Edge} (he : r.active e) :
    productProjection (d+1) (translatePoint (r.origin (p.layout.src e))
      (translatePoint (r.step e he).val (productOrigin I))) = r.site (p.layout.dst e) := by
  apply PiLp.ext
  intro i
  have hr := congrFun (r.aligned e he) i
  change ((r.origin (p.layout.dst e) i : gamma 1) : Deck (d+1)) =
    ↑(r.origin (p.layout.src e) i) * ↑((r.step e he).val i) at hr
  rw [← QuotientGroup.mk_mul] at hr
  have hs := congrArg (deckSite d) hr.symm
  change projectPoint (d+1) (gammaSL 1 (r.origin (p.layout.src e) i) •
    (gammaSL 1 ((r.step e he).val i) • UpperHalfPlane.I)) = _
  rw [← mul_smul,← map_mul]
  exact hs

/-- The actual quotient location of every old vertex and every inserted equality vertex. -/
noncomputable def physical (h : ℝ) :
    (p.layout.subdivide (r.routes h)).Site → SurfaceHost I (d+1) :=
  Sum.elim r.site (fun j => if he : r.active j.1 then
    productProjection (d+1) (translatePoint (r.origin (p.layout.src j.1))
      ((moveLine (r.step j.1 he)).atTime (((j.2.val:ℝ)+1)*hopLength h (r.step j.1 he))))
    else r.site (p.layout.src j.1))

/-- Every charged index in the subdivided tensor network belongs to the geometric catalog. -/
theorem hop_index {e : p.layout.Edge} (he : r.active e)
    (j : Fin ((r.routes h).interior e + 1)) : j.val < hopCount L h := by
  simpa only [routes,he,ite_true,hopCount] using j.isLt

/-- The source slot of every charged hop is the translated initial endpoint in the catalog. -/
theorem physical_source {e : p.layout.Edge} (he : r.active e)
    (j : Fin ((r.routes h).interior e + 1)) :
    r.physical h ((p.layout.subdivide (r.routes h)).src ⟨e,j⟩) =
      productProjection (d+1) (translatePoint (r.origin (p.layout.src e))
        (hopPosition (r.step e he, ⟨j.val,r.hop_index he j⟩) 0)) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · change r.site (p.layout.src e) = _
    rw [hopPosition_first _ _ rfl]
    rfl
  · simp only [Network.subdivide,Fin.cases_succ,physical,Sum.elim_inr,he,reduceDIte,
      hopPosition,Fin.val_succ,Nat.cast_add,Nat.cast_one,add_zero]

/-- The target slot of every charged hop is the translated final endpoint in the catalog. -/
theorem physical_target {e : p.layout.Edge} (he : r.active e)
    (j : Fin ((r.routes h).interior e + 1)) :
    r.physical h ((p.layout.subdivide (r.routes h)).dst ⟨e,j⟩) =
      productProjection (d+1) (translatePoint (r.origin (p.layout.src e))
        (hopPosition (r.step e he, ⟨j.val,r.hop_index he j⟩) 1)) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Network.subdivide,Fin.lastCases_last,physical,Sum.elim_inl]
    rw [hopPosition_last _ _ (by simp [routes,he,hopCount])]
    exact (r.site_of_move he).symm
  · simp only [Network.subdivide,Fin.lastCases_castSucc,physical,Sum.elim_inr,he,reduceDIte,
      hopPosition,Fin.val_castSucc]

/-- Every physically placed charged hop has length at most the chosen subdivision scale. -/
theorem physical_hop_le {e : p.layout.Edge} (he : r.active e) (hh : 0 < h)
    (j : Fin ((r.routes h).interior e + 1)) :
    dist (r.physical h ((p.layout.subdivide (r.routes h)).src ⟨e,j⟩))
      (r.physical h ((p.layout.subdivide (r.routes h)).dst ⟨e,j⟩)) ≤ hopLength h (r.step e he) := by
  rw [r.physical_source he,r.physical_target he]
  exact (productProjection_dist_le _ _ _).trans_eq (((translatePoint_isometry _).dist_eq _ _).trans
    (dist_hopPosition hh _))

/-- The true network length of the subdivided pack is bounded by the initial total charged
width times the site-move budget. -/
theorem chargedLength_subdivided (hh : 0 < h) :
    chargedLength (p.layout.subdivide (r.routes h)) (r.physical h) (fun j => r.active j.1) ≤
      L * ∑ e, if r.active e then (p.layout.width e : ℝ) else 0 := by
  classical
  unfold chargedLength
  erw [Fintype.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases he : r.active e
  · simp only [he,ite_true]
    calc
      _ ≤ ∑ _j : Fin ((r.routes h).interior e + 1), (p.layout.width e : ℝ) * hopLength h (r.step e he) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (r.physical_hop_le he hh j) (Nat.cast_nonneg _)
      _ = (p.layout.width e:ℝ)*moveLength (r.step e he).val := by
        have hn : (hopCount L h : ℝ) ≠ 0 := by simp [hopCount]; positivity
        have hc : (r.routes h).interior e + 1 = hopCount L h := by simp [routes,he,hopCount]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hc,hopLength]
        field_simp
      _ ≤ _ := by
        rw [mul_comm L]
        exact mul_le_mul_of_nonneg_left (mem_allowedMoves.mp (r.step e he).2).2 (Nat.cast_nonneg _)
  · simp [he]

end SiteRoutes
end Cover

end BorderVNP
end Computability
end OAI
