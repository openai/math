import OAI.Computability.BorderVNP.PackedCompleteRoutes
import OAI.Computability.BorderVNP.ShortenSiteProgram

/-! # Complete charge masks through physical site subdivision and level reindexing -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.SiteRoutes

open Crossing Shortening Shortening.Adaptive
open scoped Classical

variable {D d : ℕ} {P I : Type} [Fintype I] {K : Type*} {bits : P → ℕ} {L h : ℝ}
    {p : Pack D P bits K} (s : SiteRoutes p I d L)

/-- Equal reduced site coordinates give the same quotient point in every factor. -/
private theorem site_eq_of_reduction (u v : p.layout.Site)
    (hv : reduceMove d (s.origin u) = reduceMove d (s.origin v)) : s.site u = s.site v := by
  apply PiLp.ext
  intro i
  exact congrArg (deckSite d) (congrFun hv i)

/-- A physically uncharged input cable has no equality vertices, and both original
endpoints have the same surface position. Every hop of an active cable is charged. -/
theorem initialPlaced_coversCrossings [CommSemiring K] (hh : 0 < h) (complete : s.CoversCrossings) :
    (s.initialPlacedPack hh).CoversCrossings := by
  rintro ⟨c,j⟩ hne
  change s.active c = true
  by_contra hn
  have hzero : (s.routes h).interior c = 0 := by simp [routes,hn]
  have j0 : j = 0 := Fin.ext (by have := j.isLt; omega)
  have jlast : j = Fin.last ((s.routes h).interior c) := Fin.ext (by simp [hzero,j0])
  apply hne
  change s.physical h ((p.layout.subdivide (s.routes h)).src ⟨c,j⟩) =
    s.physical h ((p.layout.subdivide (s.routes h)).dst ⟨c,j⟩)
  conv_lhs => rw [j0]
  conv_rhs => rw [jlast]
  simp only [Network.subdivide,Fin.cases_zero,Fin.lastCases_last,physical,Sum.elim_inl]
  exact s.site_eq_of_reduction _ _ (not_ne_iff.mp fun h => hn (complete c h))

/-- Relabeling a depth carries the completeness of the original route. -/
theorem CoversCrossings.reindex {d' : ℕ} (complete : s.CoversCrossings) (eqn : d = d') :
    (reindexRoutes eqn s).CoversCrossings := by subst d'; exact complete

/-- A complete input remains complete under identification of its stored dependent pack and route. -/
theorem CoversCrossings.of_heq {d' : ℕ} {p' : Pack D P bits K} (s' : SiteRoutes p' I d' L) (hd : d' = d)
    (hp : p' = p) (hs : HEq s' s) (complete : s.CoversCrossings) : s'.CoversCrossings := by
  subst d'
  subst p'
  cases eq_of_heq hs
  exact complete

end Cover.SiteRoutes

end BorderVNP
end Computability
end OAI
