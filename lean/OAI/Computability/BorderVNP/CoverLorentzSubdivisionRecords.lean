import OAI.Computability.BorderVNP.CoverLorentzHopCatalog
import OAI.Computability.BorderVNP.ShortenEpochLocalRecords

/-!
# The exact record accounting of wire subdivision

At each old box its payload, port intervals and the original cable end records
are retained. An inserted equality site adds precisely one box and two ends of
the width of its cable. This formula applies to both public and expanded counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open BorderVNP.Crossing BorderVNP.Shortening Finset
open scoped Classical

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}

/-- Exact public and expanded counts at arbitrary tested sites after equality subdivision. -/
theorem subdivision_records_eq (N : Network D P bits) (routes : Network.WireRoutes N)
    (expanded : Bool) (prior payload : N.Site → ℕ)
    (test : (N.subdivide routes).Site → Prop) :
    localRecords (N.subdivide routes) expanded (Sum.elim prior (fun _ => 0))
      (Sum.elim payload (fun _ => 0)) test =
      localRecords N expanded prior payload (fun v => test (.inl v)) +
        ∑ e : N.Edge, ∑ j : Fin (routes.interior e), if test (.inr ⟨e,j⟩) then
          1+2*recordCost expanded (N.width e) else 0 := by
  let endCost (e : N.Edge) := recordCost expanded (N.width e)
  let eqCount (e : N.Edge) (j : Fin (routes.interior e)) :=
    if test (.inr ⟨e,j⟩) then 1 else 0
  let ends (e : N.Edge) (j : Fin (routes.interior e)) :=
    if test (.inr ⟨e,j⟩) then endCost e else 0
  have hs (e : N.Edge) : (∑ j : Fin (routes.interior e+1),
      if test ((N.subdivide routes).src ⟨e,j⟩) then endCost e else 0) =
      (if test (.inl (N.src e)) then endCost e else 0) + ∑ j, ends e j := by
    rw [Fin.sum_univ_succ]; rfl
  have hd (e : N.Edge) : (∑ j : Fin (routes.interior e+1),
      if test ((N.subdivide routes).dst ⟨e,j⟩) then endCost e else 0) =
      (∑ j, ends e j) + (if test (.inl (N.dst e)) then endCost e else 0) := by
    rw [Fin.sum_univ_castSucc]
    simp [Network.subdivide,ends]
  have hbox :
      testedWidth (fun v : (N.subdivide routes).Site =>
        boxCost expanded (Sum.elim prior (fun _ => 0) v) (Sum.elim payload (fun _ => 0) v)) test =
      testedWidth (fun v : N.Site => boxCost expanded (prior v) (payload v)) (fun v => test (.inl v)) +
        ∑ e, ∑ j, eqCount e j := by
    unfold testedWidth
    erw [Fintype.sum_sum_type]
    congr 1
    rw [Fintype.sum_sigma]
    simp [eqCount,boxCost,recordCost]
  have hsrc : testedWidth (fun f => recordCost expanded ((N.subdivide routes).width f))
      (fun f => test ((N.subdivide routes).src f)) =
      testedWidth (fun e => endCost e) (fun e => test (.inl (N.src e))) + ∑ e, ∑ j, ends e j := by
    unfold testedWidth
    erw [Fintype.sum_sigma]
    change (∑ e, ∑ j, if test ((N.subdivide routes).src ⟨e,j⟩) then endCost e else 0) = _
    simp_rw [hs]; rw [sum_add_distrib]
  have hdst : testedWidth (fun f => recordCost expanded ((N.subdivide routes).width f))
      (fun f => test ((N.subdivide routes).dst f)) =
      (∑ e, ∑ j, ends e j) + testedWidth (fun e => endCost e) (fun e => test (.inl (N.dst e))) := by
    unfold testedWidth
    erw [Fintype.sum_sigma]
    change (∑ e, ∑ j, if test ((N.subdivide routes).dst ⟨e,j⟩) then endCost e else 0) = _
    simp_rw [hd]; rw [sum_add_distrib]
  have hlocal (e : N.Edge) (j : Fin (routes.interior e)) :
      (if test (.inr ⟨e,j⟩) then 1+2*recordCost expanded (N.width e) else 0) =
      eqCount e j + (ends e j + ends e j) := by
    by_cases h : test (.inr ⟨e,j⟩) <;> simp [eqCount,ends,endCost,h,two_mul]
  unfold localRecords
  rw [hbox,hsrc,hdst]
  simp_rw [hlocal,sum_add_distrib]
  change _ = _ + _
  dsimp only [endCost,Network.subdivide]
  omega

/-- The distinguished center is itself the selected representative of its base-tile address. -/
theorem baseTile_origin : Frame.toBaseTile UpperHalfPlane.I = 1 := by
  let o := UpperHalfPlane.I
  have hd : o ∈ dirichlet 1 := fun u => (dist_self o).le.trans dist_nonneg
  have hm : o ∈ planeTile 0 := by
    refine ⟨hd,?_⟩
    intro u hu
    have hh := hu u
    rw [dist_self] at hh
    have h := dist_eq_zero.mp (le_antisymm hh dist_nonneg)
    rw [h]
  have h1 : gammaSL 1 1 • o ∈ planeTile 0 := by simpa using hm
  exact (existsUnique_mem_planeTile 0 o).unique (Frame.toBaseTile_mem _) h1

variable {I : Type*} [Fintype I] {d : ℕ} {L h : ℝ} {R : Type*} {p : Pack D P bits R}

namespace SiteRoutes

omit [Fintype P] in
/-- Site representatives reconstruct the original deck address, including at the base site. -/
theorem address_site (r : SiteRoutes p I d L) (v : p.layout.Site) :
    productAddress d (r.site v) = reduceMove d (r.origin v) := by
  rw [site,productAddress_translate]
  have h1 : productAddress d (productProjection (d+1) (productOrigin I)) = 1 := by
    funext i
    change (↑(Frame.toBaseTile UpperHalfPlane.I)⁻¹ : Deck (d+1)) = 1
    simp [baseTile_origin]
  rw [h1,mul_one]

omit [Fintype P] in
/-- Each inserted equality site is the end of its preceding charged hop. -/
theorem physical_equality (r : SiteRoutes p I d L) {e : p.layout.Edge} (he : r.active e)
    (j : Fin ((r.routes h).interior e)) :
    r.physical h (.inr ⟨e,j⟩) =
      productProjection (d+1) (translatePoint (r.origin (p.layout.src e))
        (hopPosition (r.step e he,⟨j.val,r.hop_index he j.castSucc⟩) 1)) := by
  simp only [physical,Sum.elim_inr,he,reduceDIte,hopPosition]

end SiteRoutes
end Cover

end BorderVNP
end Computability
end OAI
