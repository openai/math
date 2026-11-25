import OAI.Computability.BorderVNP.PackedTerminalCandidate
import OAI.Computability.BorderVNP.ShortenEpochRoundFlatSites

/-!
# Terminal score and selected routes on the physical pack

The sum over padded cable slots counts each physical width once. Distinct
moved addresses imply that the original charged wire had positive length.
The compiled least alignment agrees with the move carried by the calibrated
site output, even when two integral moves coincide at the current level.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Terminal

open Cover Cover.AddressCircuit Shortening Epoch Epoch.Round Catalog PublicRelative PublicSegments
open PublicEndpoints PublicCapacity Crossing
open scoped Classical

variable {D q d lev V E w a : ℕ} {P : Type} {R : Type*} {bits : P → ℕ}
  {enum : Fin q ≃ Cube D} {hl : lev+1=d+2+2*a}
  {g : Cube D → Cover.Frame.SL} {hg : ∀ i, Cover.Frame.Clears (g i) a}
  {p : PlacedPack D P bits R (Cube D) lev} {dir : Normalized.Directory p V E} {L : ℝ}
  {y : RouteRows.Pins (allowedMoves (Cube D) L) q (d+2) V E w → Bool}

/-- Rounding a coincident pair never separates its addresses. Consequently
the old charge field gives the same test as the positive-length mask. -/
private theorem charge_iff (e : p.pack.layout.Edge) :
    (p.charged e ∧ addressAfter hl hg (p.site (p.pack.layout.src e)) ≠
      addressAfter hl hg (p.site (p.pack.layout.dst e))) ↔
    (p.active e ∧ addressAfter hl hg (p.site (p.pack.layout.src e)) ≠
      addressAfter hl hg (p.site (p.pack.layout.dst e))) := by
  rw [p.active_iff]
  constructor
  · rintro ⟨hc,hn⟩; exact ⟨⟨hc,fun h => hn (congrArg (addressAfter hl hg) h)⟩,hn⟩
  · exact fun h => ⟨h.1.1,h.2⟩

/-- Exact physical integer width represented by the word-sum of this candidate. -/
theorem CandidateRows.score (h : CandidateRows enum hl hg dir L y) :
    (∑ i, if y (.inr (.inl i)) then ParseBatchSort.value (fun j => y (.inr (.inr (.inr (i,.inl j))))) else 0) =
      terminalScore p.pack (fun v => productMotion (d+2) (Equiv.refl _) hg (levelCast hl (p.site v))) p.active := by
  unfold terminalScore
  symm
  apply Fintype.sum_of_injective dir.cables dir.cables.injective
  · intro i hi
    simp [h.hole i hi]
  · intro e
    rw [h.active,h.names.widths]
    change (if p.active e ∧ addressAfter hl hg (p.site (p.pack.layout.src e)) ≠
      addressAfter hl hg (p.site (p.pack.layout.dst e)) then p.pack.layout.width e else 0) =
      if p.charged e && decide _ then storedWidth p.pack.layout dir.cables dir.dummy (dir.cables e) else 0
    have hw := Packing.Names.width_slot p.pack.layout dir.cables dir.dummy e
    change storedWidth p.pack.layout dir.cables dir.dummy (dir.cables e) = p.pack.layout.width e at hw
    rw [hw]
    simp only [Bool.and_eq_true,decide_eq_true_eq,charge_iff (hl := hl) (hg := hg)]

/-- The same reserved sparse rows, now interpreted as rows of the site pack. -/
def boundaryRows (dir : Normalized.Directory p V E) : Rows ⟨V,E⟩ p.pack.layout :=
  ⟨dir.sites,dir.cables⟩

set_option maxHeartbeats 1200000 in
/-- The returned data form the next subdivision's public route-row input. -/
theorem CandidateRows.ready (h : CandidateRows enum hl hg dir L y) (r : SiteRoutes p.pack (Cube D) (d+1) L)
    (hs : ∀ v, reduceMove (d+1) (r.origin v) = addressAfter hl hg (p.site v))
    (ha : ∀ e, r.active e ↔ p.active e ∧ addressAfter hl hg (p.site (p.pack.layout.src e)) ≠
      addressAfter hl hg (p.site (p.pack.layout.dst e))) (hm : r.FirstAligned) :
    RouteRows.Ready enum p.pack r (boundaryRows dir) dir.dummy y := by
  refine ⟨h.names,?_,h.present,?_,h.hole,?_⟩
  · intro v j
    change y (.inr (.inr (.inl (dir.sites v,j)))) = _
    rw [h.origins v j,← hs]
    rfl
  · intro e
    change y (.inr (.inl (dir.cables e))) = _
    rw [h.active]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    exact (charge_iff e).trans (ha e).symm
  · intro e he t
    apply Bool.eq_iff_iff.mpr
    let src := addressAfter hl hg (p.site (p.pack.layout.src e))
    let dst := addressAfter hl hg (p.site (p.pack.layout.dst e))
    have hx := h.moves e t
    change y (.inl (dir.cables e,.inr t)) = true ↔ dst = src * reduceMove (d+1) t.val ∧ _ at hx
    change y (.inl (dir.cables e,.inr t)) = true ↔ decide _ = true
    rw [hx,decide_eq_true_eq]
    let τ := r.step e he
    let ord := Fintype.equivFin ↥(allowedMoves (Cube D) L)
    have hit : dst = src * reduceMove (d+1) τ.val := by
      change addressAfter hl hg (p.site (p.pack.layout.dst e)) =
        addressAfter hl hg (p.site (p.pack.layout.src e)) * _
      rw [← hs,← hs]; exact r.aligned e he
    have min (j : Fin (Fintype.card ↥(allowedMoves (Cube D) L))) (hj : j ∈ SiteRoutes.alignedIndices L (d+1) src dst) :
        ord τ ≤ j := hm e he j (by rw [hs,hs]; exact hj)
    have mem (v : ↥(allowedMoves (Cube D) L)) (hv : dst = src*reduceMove (d+1) v.val) :
        ord v ∈ SiteRoutes.alignedIndices L (d+1) src dst := by
      simpa only [SiteRoutes.alignedIndices,Finset.mem_filter,Finset.mem_univ,true_and,ord,Equiv.symm_apply_apply] using hv
    constructor
    · rintro ⟨ht,hmin⟩
      exact ord.injective (le_antisymm (hmin (ord τ) (mem τ hit)) (min (ord t) (mem t ht)))
    · rintro rfl; exact ⟨hit,min⟩

end PackedHistoryCircuit.Terminal

namespace PackedHistoryCircuit.RouteRows

open Cover Cover.AddressCircuit Shortening Shortening.Adaptive Shortening.PublicCapacity
open scoped Classical

/-- Relabelling the external ports at an epoch boundary keeps the exact stored
site and cable rows. Each flattened port is still attached to its original site. -/
theorem Ready.flatten {I P : Type} [Fintype I] {K : Type*} {q d D k b w : ℕ} {L : ℝ}
    {enum : Fin q ≃ I} {bits : P → ℕ} {p : Pack D (Port k P b) (width bits k b) K}
    {r : SiteRoutes p I d L} {s : Shape} {rows : Rows s p.layout} {dummy : Fin s.edges → p.layout.Site}
    {x : Pins (allowedMoves I L) q (d+1) s.sites s.edges w → Bool}
    (h : Ready enum p r rows dummy x) :
    Ready enum (flattenPack b p) r.flatten rows.flatten dummy x :=
  ⟨⟨h.names.addresses,h.names.widths⟩,h.origins,h.present,h.active,h.hole,h.move⟩

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI
