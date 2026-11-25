import OAI.Computability.BorderVNP.ShortenEpochTerminalMinimum

/-!
# Public motion and route choices on the terminal catalog

The finite motion list is fixed before the cover level and before any pack
arrives. Every minimizer of the computable integer score yields a physical
site output. For a cable whose addresses differ, the move is the first
aligned move in the fixed allowed list.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.SiteRoutes

open Shortening Crossing Finset
open scoped Classical

variable {D d : ℕ} {P R I : Type*} [Fintype I] {bits : P → ℕ} {L : ℝ} {p : Pack D P bits R}

/-- Candidate move indices that carry the source tile to the destination. -/
noncomputable def alignedIndices (L : ℝ) (d : ℕ) (x y : I → Deck (d+1)) :=
  univ.filter fun j : Fin (Fintype.card (allowedMoves I L)) =>
    y = x * reduceMove d ((Fintype.equivFin (allowedMoves I L)).symm j).val

/-- Canonical physical move names. Congruence levels with colliding candidates
resolve the tie by the fixed list order. -/
def FirstAligned (s : SiteRoutes p I d L) : Prop :=
  ∀ e he, ∀ j ∈ alignedIndices L d (reduceMove d (s.origin (p.layout.src e)))
    (reduceMove d (s.origin (p.layout.dst e))),
    Fintype.equivFin (allowedMoves I L) (s.step e he) ≤ j

/-- Reselect every active move by its public ordinal. Integral origins, active
flags and both tile histograms retain their original values. -/
noncomputable def firstRoutes (s : SiteRoutes p I d L) : SiteRoutes p I d L := by
  let candidates e := alignedIndices L d (reduceMove d (s.origin (p.layout.src e)))
    (reduceMove d (s.origin (p.layout.dst e)))
  have nonempty e (he : s.active e) : (candidates e).Nonempty := by
    refine ⟨Fintype.equivFin _ (s.step e he),?_⟩
    simpa only [candidates,alignedIndices,mem_filter,mem_univ,true_and,Equiv.symm_apply_apply]
      using s.aligned e he
  exact { origin := s.origin, active := s.active
          step := fun e he => (Fintype.equivFin _).symm ((candidates e).min' (nonempty e he))
          aligned := fun e he => (mem_filter.mp ((candidates e).min'_mem (nonempty e he))).2 }

/-- The chosen physical route has the least aligned public ordinal at each active cable. -/
theorem firstRoutes_first (s : SiteRoutes p I d L) : s.firstRoutes.FirstAligned := by
  intro e he j hj
  change Fintype.equivFin _ ((Fintype.equivFin _).symm _) ≤ j
  rw [Equiv.apply_symm_apply]
  exact Finset.min'_le _ _ hj

end Cover.SiteRoutes

namespace Epoch.Round

open Shortening Shortening.Catalog Cover Cover.Frame Crossing Finset
open scoped Classical

/-- Uniform physical realization by the minimizing motion and least aligned
move on every reached terminal pack. The coefficient and initial move budget
are chosen before the length catalog. -/
theorem terminal_catalog_minimum : ∃ C ≥ (0:ℝ), ∀ (I : Type) [Fintype I] (h : ℝ), 4*h ≤ 1 →
    ∃ L > (0:ℝ), (∀ s : I → gamma 1, s ≠ 1 → (∀ i, s i = 1 ∨ (s i).val ∈ routingGenerators) →
      s ∈ allowedMoves I L) ∧
    ∀ (V : Set (SegmentType I)), V.Finite →
    ∃ (a m H : ℕ) (Cout : ℝ) (u : Fin m → SL) (hu : ∀ i, Clears (u i) a),
      0 ≤ Cout ∧ Nonempty (I → Fin m) ∧
      ∀ {d l D : ℕ} (η : l+1 = d+2+2*a) {P : Type} [Fintype P] {R : Type*} {bits : P → ℕ}
        (p : PlacedPack D P bits R I l), p.canonical → FitsCatalog p V h →
        let moved (σ : I → Fin m) (v : p.pack.layout.Site) :=
          productMotion (d+2) (Equiv.refl _) (fun k => hu (σ k)) (levelCast η (p.site v))
        ∀ σ, (∀ τ, terminalScore p.pack (moved σ) p.active ≤ terminalScore p.pack (moved τ) p.active) →
        ∃ o : SiteOutput p (d+1) L (Fintype.card I*C) Cout H,
          (∀ v, reduceMove (d+1) (o.routes.origin v) = productAddress (d+1) (moved σ v)) ∧
          (∀ e, o.routes.active e ↔ p.active e ∧ productAddress (d+1) (moved σ (p.pack.layout.src e)) ≠
            productAddress (d+1) (moved σ (p.pack.layout.dst e))) ∧ o.routes.FirstAligned := by
  obtain ⟨C,hC,round⟩ := final_site_minimum
  refine ⟨C,hC,?_⟩
  intro I _ h h4
  obtain ⟨L,hL,hgen,prep⟩ := round I h
  refine ⟨L,hL,hgen,?_⟩
  intro V hV
  let S := {v : SegmentType I | v ∈ V ∧ dist v.ends.1 v.ends.2 ≤ h}
  let _ := (hV.subset (show S ⊆ V from fun _ hv => hv.1)).fintype
  let r (s : S) := dist s.val.ends.1 s.val.ends.2
  obtain ⟨a,m,N,H,u,hu,hm,run⟩ := prep r (fun _ => dist_nonneg) (fun s => by linarith [s.property.2])
    (fun s => s.property.2)
  refine ⟨a,m,H,2*N,u,hu,by positivity,hm,?_⟩
  intro d l D η P _ R bits p hcanon hfit moved σ hmin
  have htag (e : Wires p.pack p.active) : ∃ j : S,
      dist (levelCast η (p.site (p.pack.layout.src e.val))) (levelCast η (p.site (p.pack.layout.dst e.val))) = r j := by
    obtain ⟨hcap,v,hv,_,_,_,he⟩ := hfit e
    exact ⟨⟨v,hv,he.le.trans hcap⟩,(levelCast_dist η _ _).trans he.symm⟩
  choose tag ht using htag
  obtain ⟨s,hs,hch,hw,hx,hr⟩ := run d p.pack (levelCast η ∘ p.site) p.active tag ht σ hmin
  obtain ⟨hW,hX⟩ := p.final_coordinates η hcanon
  rw [hW] at hw
  rw [hX] at hx
  refine ⟨⟨s.firstRoutes,hw,hx,?_⟩,hs,hch,s.firstRoutes_first⟩
  intro ex prior payload M hold t
  apply hr ex prior payload M _ t
  have htrans {n : ℕ} (eqn : l+1 = n) : ∀ s,
      localRecords p.pack.layout ex prior payload (fun v =>
        (fun k => addressAt n (by omega) (levelCast eqn (p.site v) k)) = s) ≤ M := by
    subst n; exact hold
  exact htrans η

end Epoch.Round

end BorderVNP
end Computability
end OAI
