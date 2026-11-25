import OAI.Computability.BorderVNP.ShortenEpochRoundPlacedFinish

/-!
# A fixed terminal segment catalog determines a uniform return to sites

Preparation of the physical last step supplies finite lifted endpoint pairs
before the input fan-in or the cover depth is specified. Restricting this set
to its permitted lengths gives the finite length list for the site motion.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch.Round

open BorderVNP.Shortening BorderVNP.Shortening.Catalog BorderVNP.Cover BorderVNP.Cover.Frame
open BorderVNP.Crossing Finset
open scoped Classical

/-- Every positive charged segment has its actual length in the fixed terminal catalog. -/
def FitsCatalog {I : Type} [Fintype I] {D l : ℕ} {P : Type} {R : Type*} {bits : P → ℕ}
    (p : PlacedPack D P bits R I l) (V : Set (SegmentType I)) (h : ℝ) : Prop :=
  ∀ e : Wires p.pack p.active,
    dist (p.site (p.pack.layout.src e.val)) (p.site (p.pack.layout.dst e.val)) ≤ h ∧
    ∃ v ∈ V, Realizes (p.site (p.pack.layout.src e.val)) (p.site (p.pack.layout.dst e.val)) v.ends

/-- The result of moving one physical terminal pack and returning its vertices to sites.
The site data refer to the identical underlying algebraic pack. -/
structure SiteOutput {I : Type} [Fintype I] {D l : ℕ} {P : Type} [Fintype P] {R : Type*} {bits : P → ℕ}
    (p : PlacedPack D P bits R I l) (d : ℕ) (L A Cout : ℝ) (H : ℕ) where
  /-- Integral addresses and allowed nonlocal moves in the final site pack. -/
  routes : SiteRoutes p.pack I d L
  /-- Actual remaining site width. -/
  width_le : routes.nonlocalWidth ≤ A*p.length
  /-- Actual site incidence concentration. -/
  concentration_le : routes.incidenceConcentration ≤ Cout*p.concentration
  /-- Both modes of the record count under this very same realization. -/
  records_le : ∀ (ex : Bool) (prior payload : p.pack.layout.Site → ℕ) (M : ℕ),
    (∀ t, localRecords p.pack.layout ex prior payload (fun v => productAddress l (p.site v) = t) ≤ M) →
    ∀ t, localRecords p.pack.layout ex prior payload (fun v => reduceMove d (routes.origin v) = t) ≤ H*M

/-- The bounded terminal segment population furnished by the last step gives uniform
site bounds with the length coefficient and site budget fixed before the catalog. -/
theorem terminal_catalog_rounding : ∃ C ≥ (0:ℝ), ∀ (I : Type) [Fintype I] (h : ℝ), 4*h ≤ 1 →
    ∃ L > (0:ℝ), (∀ s : I → gamma 1, s ≠ 1 → (∀ i, s i = 1 ∨ (s i).val ∈ routingGenerators) →
      s ∈ allowedMoves I L) ∧
    ∀ (V : Set (SegmentType I)), V.Finite → ∃ (a H : ℕ) (Cout : ℝ), 0 ≤ Cout ∧
      ∀ {d l D : ℕ} (_η : l+1 = d+2+2*a) {P : Type} [Fintype P] {R : Type*} {bits : P → ℕ}
        (p : PlacedPack D P bits R I l), p.canonical → FitsCatalog p V h →
        Nonempty (SiteOutput p (d+1) L (Fintype.card I*C) Cout H) := by
  classical
  obtain ⟨C,hC,round⟩ := final_site_rounding
  refine ⟨C,hC,?_⟩
  intro I _ h h4
  obtain ⟨L,hL,hgen,prep⟩ := round I h
  refine ⟨L,hL,hgen,?_⟩
  intro V hV
  let S := {v : SegmentType I | v ∈ V ∧ dist v.ends.1 v.ends.2 ≤ h}
  have hS : S.Finite := hV.subset (fun _ hv => hv.1)
  let := hS.fintype
  let r (s : S) := dist s.val.ends.1 s.val.ends.2
  obtain ⟨a,m,N,H,u,hu,run⟩ := prep r (fun _ => dist_nonneg) (fun s => by linarith [s.property.2])
    (fun s => s.property.2)
  refine ⟨a,H,2*N,by positivity,?_⟩
  intro d l D η P _ R bits p hcanon hfit
  have htag (e : Wires p.pack p.active) : ∃ j : S,
      dist (levelCast η (p.site (p.pack.layout.src e.val))) (levelCast η (p.site (p.pack.layout.dst e.val))) = r j := by
    obtain ⟨hcap,v,hv,_,_,_,he⟩ := hfit e
    exact ⟨⟨v,hv,he.le.trans hcap⟩,(levelCast_dist η _ _).trans he.symm⟩
  choose tag ht using htag
  obtain ⟨_,s,_,_,hw,hx,hr⟩ := run d p.pack (levelCast η ∘ p.site) p.active tag ht
  obtain ⟨hW,hX⟩ := p.final_coordinates η hcanon
  rw [hW] at hw
  rw [hX] at hx
  refine ⟨⟨s,hw,hx,?_⟩⟩
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
