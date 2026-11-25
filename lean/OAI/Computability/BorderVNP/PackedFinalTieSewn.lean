import OAI.Computability.BorderVNP.PackedFinalTieWork
import OAI.Computability.BorderVNP.PackedTerminalRoutingFields
import OAI.Computability.BorderVNP.DiagonalExternalSewFieldFrame

/-! # Live final binding slots on the actual sewn endpoint directory

Internal occupation comes from the returned route, independently of its
cable widths. The extra four-slot rectangle uses the same exterior probe as
the exported endpoint and width fields. Grouped exterior ports fill their
entire static rectangle. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing Shortening Shortening.PublicCapacity Cover Cover.AddressCircuit PackedHistoryCircuit
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical
open private routed from OAI.Computability.BorderVNP.PackedTerminalRoutingFields

/-- Occupied exterior probes are precisely the stable ordinals of true cables. -/
theorem exterior_present (p : Params) (hp : p.Valid) (i : Fin p.slots) :
    (p.record i).live = true ↔ i ∈ Set.range (p.ordinal hp) := by
  have row := FourSlot.row_live_iff hp.block hp.small (by omega : p.literal+p.R*p.link ≤ 2*p.literal+p.R*p.link)
    hp.room (p.key i)
  constructor
  · intro active
    obtain ⟨c,he⟩ := row.mp active
    refine ⟨c,(FourSlot.slotOrdinal _ _).symm.injective ?_⟩
    exact ((FourSlot.slotOrdinal _ _).symm_apply_apply _).trans he
  · rintro ⟨c,rfl⟩
    exact row.mpr ⟨c,((FourSlot.slotOrdinal _ _).symm_apply_apply _).symm⟩

/-- Fixed pin of each occupied endpoint of the combined terminal cable table. -/
def sewnPresent {old : ℕ} {σ : Type*} (p : Params) (occupied : Fin old → σ) (i : Fin (old+p.slots)) : σ ⊕ Bool :=
  (finSumFinEquiv.symm i).elim (fun j => .inl (occupied j)) (fun j => .inr (p.record j).live)

/-- The complete live incidence flag on the actual combined sparse fields. -/
theorem sewn_present {old : ℕ} {σ γ E : Type*} [Fintype σ] [Fintype γ] (p : Params) (hp : p.Valid)
    (edgeID : E ↪ Fin old) (occupied : Fin old → σ) (source : Frame γ σ) (x : γ → Bool)
    (h : ∀ i, source.eval x (occupied i) = true ↔ i ∈ Set.range edgeID) (i : Fin (old+p.slots)) :
    (withSewnFields source).eval x (sewnPresent p occupied i) = true ↔
      i ∈ Set.range (mergedEdges p hp edgeID) := by
  obtain ⟨a,rfl⟩ := finSumFinEquiv.surjective i
  cases a with
  | inl j =>
    simp only [withSewnFields,Frame.subst_eval,constants_eval,sewnPresent,Equiv.symm_apply_apply,Sum.elim_inl,h]
    constructor
    · rintro ⟨e,rfl⟩; exact ⟨.inl e,rfl⟩
    · rintro ⟨e,he⟩
      cases e with
      | inl e => exact ⟨e,Sum.inl.inj (finSumFinEquiv.injective he)⟩
      | inr c =>
        have falseEq : (Sum.inr (p.ordinal hp c) : Fin old ⊕ Fin p.slots) = .inl j := finSumFinEquiv.injective he
        cases falseEq
  | inr j =>
    simp only [withSewnFields,Frame.subst_eval,constants_eval,sewnPresent,Equiv.symm_apply_apply,Sum.elim_inr,
      id_eq,exterior_present p hp]
    constructor
    · rintro ⟨c,rfl⟩; exact ⟨.inr c,rfl⟩
    · rintro ⟨e,he⟩
      cases e with
      | inr c => exact ⟨c,Sum.inr.inj (finSumFinEquiv.injective he)⟩
      | inl e =>
        have falseEq : (Sum.inl (edgeID e) : Fin old ⊕ Fin p.slots) = .inr j := finSumFinEquiv.injective he
        cases falseEq

/-- Every grouped exterior port has a live row, including its zero-use fiber. -/
theorem grouped_port_present (p : Params) (j : Fin ((p.R+1)*p.sites)) :
    (true = true) ↔ j ∈ Set.range (finProdFinEquiv.toEmbedding : FreeBlock p.R p.sites ↪ _) :=
  ⟨fun _ => ⟨finProdFinEquiv.symm j,finProdFinEquiv.apply_symm_apply j⟩,fun _ => rfl⟩

/-- Pin of the cable occupancy returned by the actual retained route computation. -/
def routePresent {q d V E w b : ℕ} {Move : Type*} (i : Fin E) : TerminalCells.Wires Move q d V E w b :=
  routed (.inl (i,.inl ()))

/-- The original occupancy bits remain available through the true terminal allocation frame. -/
theorem route_present {D q d w C b : ℕ} {P K σ : Type*} {I : Type} {bits : P → ℕ} [Fintype σ] [Fintype I]
    (enum : Fin q ≃ I) (number : (I → Deck (d+1)) ≃ Fin C) (cf : C ≤ 2^b)
    (N : Pack D P bits K) {L : ℝ} (r : SiteRoutes N I d L) {s : Shape}
    (rows : Rows s N.layout) (dummy : Fin s.edges → N.layout.Site)
    (route : Frame σ (RouteRows.Pins (allowedMoves I L) q (d+1) s.sites s.edges w))
    (aux : Frame σ (Fin s.sites × Fin w)) (x : σ → Bool)
    (ready : RouteRows.Ready enum N r rows dummy (route.eval x)) (i : Fin s.edges) :
    (TerminalCells.boundFrame enum number cf route aux).eval x (routePresent i) = true ↔ i ∈ Set.range rows.edge := by
  simpa only [TerminalCells.boundFrame,routePresent,routed,Frame.subst_eval,constants_eval,Sum.elim_inl,
    Frame.withInput_eval_inl,parallelFrame_eval_inl] using ready.present i

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI
