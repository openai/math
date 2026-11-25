import OAI.Computability.BorderVNP.PackedHistorySubdivisionSiteInput
import OAI.Computability.BorderVNP.ShortenEpochRoundInputGeometry

/-! # All actual geometric site rows of the geodesically subdivided pack -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Shortening Shortening.PublicCapacity Shortening.PublicRelative Shortening.Catalog
open Crossing Cover Cover.AddressCircuit Epoch StackFrame RationalHitting
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {I : Type} [Fintype I] {q : ℕ} (enum : Fin q ≃ I) {L h : ℝ}

/-- A missing hop key denotes the original site. A present key identifies the
end of the preceding subdivision hop. -/
private noncomputable def template : Option (Hop I L h) → HyperbolicHost I
  | none => productOrigin I
  | some t => hopPosition t 1

set_option maxHeartbeats 1200000 in
/-- The entire next geometric site table comes from one shared lookup of the
source origins, followed by the finite move-template translation per reserved site.
Both the tile and the relative type are the canonical descriptors of the exact
placed pack used by the analytic shortening argument. -/
theorem subdivision_sites (hh : 0 < h) :
    let S := SiteRoutes.startingSites I L h
    let extra := ⌈L/h⌉₊
    ∃ C e : ℕ, ∀ (d : ℕ) (s : Shape) (w : ℕ) (fit : s.sites ≤ 2^w),
      ∃ f : Frame (Pins (allowedMoves I L) q (d+1) s.sites s.edges w)
        (Fin (s.subdivide extra).sites × (ProductSlots q (d+1) ⊕ ↥S)),
        f.size ≤ (endpoints q (d+1) s.sites s.edges w (allowedMoves I L) fit).size + 1 +
          (s.subdivide extra).sites*C*(d+2)^e ∧
        ∀ {D : ℕ} {P : Type} {K : Type*} [CommSemiring K] {bits : P → ℕ} (p : Pack D P bits K)
          (r : SiteRoutes p I d L) (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site) x,
          Ready enum p r row dummy x → ∀ v,
            (fun j => f.eval x ((row.siteRoutes r h).site v,j)) =
              quotientRow enum S d rfl ((r.initialPlacedPack hh).site v) := by
  intro S extra
  obtain ⟨U,u,points⟩ := translatedPoint_frames (M := Option (Hop I L h)) enum S
  let B : TimeBound := .const (Fintype.card (Option (Hop I L h))) + .const (90*q)*TimeBound.variable +
    .const U*TimeBound.variable^u
  obtain ⟨C,e,_,_,hb⟩ := B.growth
  refine ⟨C,e,?_⟩
  intro d s w fit
  let key := siteIndex s.sites s.edges extra
  obtain ⟨geo,hg,ev⟩ := points d template
  let geom (i : Fin (s.subdivide extra).sites) :=
    geo.subst (originFrame (w := w) (key.symm i))
  let endFrame := endpoints q (d+1) s.sites s.edges w (allowedMoves I L) fit
  obtain ⟨all,hs,he⟩ := exists_parallelFrames (out := fun _ : Fin (s.subdivide extra).sites => ProductSlots q (d+1) ⊕ ↥S) geom
  let f := (all.select fun ij : Fin (s.subdivide extra).sites × (ProductSlots q (d+1) ⊕ ↥S) => ⟨ij.1,ij.2⟩).subst endFrame
  refine ⟨f,?_,?_⟩
  · have hrow (i : Fin (s.subdivide extra).sites) : (geom i).size ≤ C*(d+2)^e := by
      have hw := originFrame_size (I := I) (q := q) (d := d) (w := w) (key.symm i)
      have hcard : Fintype.card (Option (Hop I L h) ⊕ ProductSlots q (d+1)) =
          Fintype.card (Option (Hop I L h)) + 90*q*(d+2) := by
        rw [Fintype.card_sum]; simp [ProductSlots,Slots,width]; ring
      rw [hcard] at hw
      have h := hb (d+2) (by omega)
      simp only [B,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_pow,TimeBound.eval_variable,TimeBound.eval_const] at h
      simpa only [geom,Frame.subst_size] using (Nat.add_le_add hw hg).trans h
    have htotal := hs.trans (Nat.add_le_add_left (Finset.sum_le_sum (fun i _ => hrow i)) 1)
    simp only [f,Frame.subst_size,Frame.select_size]
    simpa [endFrame,Nat.mul_assoc,Nat.add_assoc] using Nat.add_le_add_left htotal endFrame.size
  · intro D P K _ bits p r row dummy x ready v
    have cell (i : Fin (s.subdivide extra).sites) (j : ProductSlots q (d+1) ⊕ ↥S) :
        f.eval x (i,j) = geo.eval ((originFrame (key.symm i)).eval (endFrame.eval x)) j := by
      simp only [f,Frame.subst_eval,Frame.select_eval,he,geom]
    rcases v with v | ⟨edge,j⟩
    · have hi : key.symm ((row.siteRoutes r h).site (.inl v)) = .inl (row.site v) := by
        have hk : (row.siteRoutes r h).site (.inl v) = key (.inl (row.site v)) := Fin.ext rfl
        exact (congrArg key.symm hk).trans (key.symm_apply_apply _)
      funext z
      rw [cell,hi,originFrame_old enum p r row dummy ready fit v]
      exact congrFun (ev none (r.origin v)) z
    · have ha : r.active edge := by
        by_contra hn
        have bound := j.isLt
        simp [SiteRoutes.routes,hn] at bound
      let j' : Fin extra := j.castLE (Rows.route_interior_le r h edge)
      have hi : key.symm ((row.siteRoutes r h).site (.inr ⟨edge,j⟩)) = .inr (row.edge edge,j') := by
        have hk : (row.siteRoutes r h).site (.inr ⟨edge,j⟩) = key (.inr (row.edge edge,j')) := Fin.ext rfl
        exact (congrArg key.symm hk).trans (key.symm_apply_apply _)
      let t : Hop I L h := (r.step edge ha,⟨j.val,r.hop_index ha j.castSucc⟩)
      funext z
      rw [cell,hi,originFrame_inner enum p r row dummy ready fit ha j']
      exact (congrFun (ev (some t) (r.origin (p.layout.src edge))) z).trans
        (congrArg (fun y => quotientRow enum S d rfl y z) (r.physical_equality ha j).symm)

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI
