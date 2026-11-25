import OAI.Computability.BorderVNP.PackedHistorySubdivisionSites
import OAI.Computability.BorderVNP.PackedHistorySubdivisionHoles

/-! # A complete public Boolean subdivision of the actual site-routed input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Shortening Shortening.PublicCapacity Shortening.PublicEndpoints Shortening.PublicRelative Shortening.PublicSegments
open Crossing Cover Cover.AddressCircuit Epoch Packing.Names
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

private def arrange {Y : Type*} {V E w : ℕ} :
    Fin E ⊕ Raw Y V E w w → (Fin V × Y) ⊕ (Fin E × CableBit w)
  | .inl i => .inr (i,.inl true)
  | .inr (.inl i) => .inr (i,.inl false)
  | .inr (.inr (.inl v)) => .inl v
  | .inr (.inr (.inr (i,b))) => .inr (i,.inr b)

/-- Chart and coordinate pins at the initial subdivision level. -/
noncomputable abbrev SiteFields (D q d : ℕ) (L h : ℝ) :=
  ProductSlots q (d+1) ⊕ ↥(SiteRoutes.startingSites (Cube D) L h)

variable {D q : ℕ} (enum : Fin q ≃ Cube D) {L h : ℝ}

set_option maxHeartbeats 1400000 in
/-- The first physical frame of a shortening epoch reconstructs the true equality
subdivision, including every live and padded endpoint, every cable width, the charge
mask, all finite relative chart labels and the modular coordinates of each site. -/
theorem subdivision_frame (hh : 0 < h) :
    ∃ C e : ℕ, ∀ (d : ℕ) (s : Shape) (w : ℕ), (s.subdivide ⌈L/h⌉₊).sites ≤ 2^w →
      ∃ f : Frame (Pins (allowedMoves (Cube D) L) q (d+1) s.sites s.edges w)
          (Fin (s.subdivide ⌈L/h⌉₊).edges ⊕ Raw (SiteFields D q d L h) (s.subdivide ⌈L/h⌉₊).sites (s.subdivide ⌈L/h⌉₊).edges w w),
        f.size ≤ 300*(s.sites+2*s.edges+1)*(Nat.clog 2 (s.sites+2*s.edges)+w+Fintype.card (ProductSlots q (d+1))+1)^3 +
          1 + (s.subdivide ⌈L/h⌉₊).sites*C*(d+2)^e + (s.subdivide ⌈L/h⌉₊).edges*(2+3*w)*8 ∧
        ∀ {P : Type} {K : Type*} [CommSemiring K] {bits : P → ℕ} (p : Pack D P bits K)
          (r : SiteRoutes p (Cube D) d L) (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site) (x : Pins (allowedMoves (Cube D) L) q (d+1) s.sites s.edges w → Bool),
          Ready enum p r row dummy x →
          let init := r.initialPlacedPack hh
          let placed := row.siteRoutes r h
          SegmentReady (SiteRoutes.startingSites (Cube D) L h) init.pack.layout placed.site placed.edge (stripeDummy p r row dummy) init.site
            (segmentField enum (SiteRoutes.startingSites (Cube D) L h) (lev := d) rfl) init.charged (f.eval x ∘ Sum.inr) ∧
          ∀ i, f.eval x (.inl i) = true ↔ i ∈ Set.range placed.edge := by
  let S := SiteRoutes.startingSites (Cube D) L h
  let extra := ⌈L/h⌉₊
  obtain ⟨C,e,sites⟩ := subdivision_sites (L := L) enum hh
  refine ⟨C,e,?_⟩
  intro d s w fit
  let next := s.subdivide extra
  let B := SiteFields D q d L h
  let move := allowedMoves (Cube D) L
  have hf : s.sites ≤ 2^w := (Nat.le_add_right s.sites (extra*s.edges)).trans fit
  obtain ⟨sf,hs,ev⟩ := sites d s w hf
  let cf := cableFrame move q (d+1) s.sites s.edges w extra
  let f := (parallelFrame sf cf).select (arrange (Y := B))
  refine ⟨f,?_,?_⟩
  · have hj := endpoints_size q (d+1) s.sites s.edges w move hf
    have hc := cableFrame_size move q (d+1) s.sites s.edges w extra
    have sz : f.size = sf.size + cf.size := by simp [f]
    exact sz.le.trans (Nat.add_le_add (hs.trans (Nat.add_le_add_right (Nat.add_le_add_right hj 1) _)) hc)
  · intro P K _ bits p r row dummy x ready init placed
    have flag (i : Fin next.edges) (side : Bool) :
        f.eval x (if side then .inl i else .inr (.inl i)) = cf.eval x (i,.inl side) := by
      cases side <;> simp [f,arrange]
    have col (i : Fin next.edges) (b : Fin w ⊕ Bool × Fin w) :
        f.eval x (.inr (.inr (.inr (i,b)))) = cf.eval x (i,.inr b) := by simp [f,arrange]
    have addr (i : Fin next.edges) (side : Bool) :
        address ((f.eval x ∘ Sum.inr) ∘ Sum.inr) i side =
          ParseBatchSort.value (fun b => cf.eval x (i,.inr (.inr (side,b)))) :=
      congrArg ParseBatchSort.value (funext fun b => col i (.inr (side,b)))
    have wt (i : Fin next.edges) :
        ParseBatchSort.value (fun b => f.eval x (.inr (.inr (.inr (i,.inl b))))) =
          ParseBatchSort.value (fun b => cf.eval x (i,.inr (.inl b))) :=
      congrArg ParseBatchSort.value (funext fun b => col i (.inl b))
    have site (i : Fin next.sites) (b : B) : f.eval x (.inr (.inr (.inl (i,b)))) = sf.eval x (i,b) := by
      simp [f,arrange]
    constructor
    · refine ⟨r.initial_site_catalog hh,?_,?_,?_,?_⟩
      · apply represents_of_rows
        · rintro ⟨a,j⟩
          let t := j.castLE (Nat.succ_le_succ (Rows.route_interior_le r h a))
          have hi : placed.edge ⟨a,j⟩ = edgeIndex s.edges extra (row.edge a,t) := live_edgeIndex p r row a j
          constructor
          · intro side
            apply (addr (placed.edge ⟨a,j⟩) side).trans
            have hcol := cableFrame_pointer x (row.edge a) t side
            rw [ready.active a] at hcol
            exact (congrArg (fun i => ParseBatchSort.value (fun b => cf.eval x (i,.inr (.inr (side,b))))) hi).trans
              (hcol.trans (physical_pointer enum p r row dummy ready fit a j side))
          · exact (wt (placed.edge ⟨a,j⟩)).trans (live_width enum p r row dummy ready a j)
        · intro i missing
          obtain ⟨⟨u,j⟩,rfl⟩ := (edgeIndex s.edges extra).surjective i
          have hempty := empty_stripe enum p r row dummy ready u j missing
          exact ⟨fun side => (addr _ side).trans (hempty.1 side),(wt _).trans hempty.2.1⟩
      · intro v j
        apply (site (placed.site v) (segmentField enum S rfl j)).trans
        exact (congrFun (ev p r row dummy x ready v) _).trans
          (congrFun (quotientRow_siteBits enum S rfl (init.site v) (r.initial_site_catalog hh v)) j)
      · rintro ⟨a,j⟩
        have hg := cableFrame_charge x (row.edge a) (j.castLE (Nat.succ_le_succ (Rows.route_interior_le r h a)))
        exact (flag (placed.edge ⟨a,j⟩) false).trans
          ((congrArg (fun z => cf.eval x (z,.inl false)) (live_edgeIndex p r row a j)).trans (hg.trans (ready.active a)))
      · intro i missing
        obtain ⟨⟨u,j⟩,rfl⟩ := (edgeIndex s.edges extra).surjective i
        exact (flag _ false).trans (empty_stripe enum p r row dummy ready u j missing).2.2
    · intro i
      obtain ⟨⟨u,j⟩,rfl⟩ := (edgeIndex s.edges extra).surjective i
      exact (Iff.of_eq (congrArg (· = true) (flag (edgeIndex s.edges extra (u,j)) true))).trans
        (stripe_present enum p r row dummy ready u j)

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI
