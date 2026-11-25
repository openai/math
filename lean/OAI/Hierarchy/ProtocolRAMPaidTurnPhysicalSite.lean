import OAI.Hierarchy.ProtocolRAMPaidRawTurn
import OAI.Hierarchy.ProtocolRAMTurnCanonicalGeometry

namespace OAI
/-! # The purchased chart seat visits its mounted original row at the canonical boundary -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAMPaidTurnPlacement
open ProbeStage CoreBoard WordSeats ReportSockets AdaptiveProbe WireTelescope SettledMatrix
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM.Calendar ProtocolRAMTurnOrder ProtocolRAMTurnGeometry ProtocolRAMTurnChart ProtocolRAMTurnShelf
open scoped Classical

variable {h W k attempts edges n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : Marks h W k attempts) (uni : Exclusive mark)
    (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges) (pad : Chord (siteLast h (2^W) k+1))
    (fixed : Fin edges→ℕ) (ident : {i // 0<fixed i} ↪ Catalogue S π depth mark)
local notation "L" => B.matrixLayout (siteNumber h (2^W) k).injective pad
variable (aligned : ∀e : {i //0<fixed i},filledChord B.actual pad e.val=HistoryRoles.sorted S π depth mark (.inl (ident e)))
local notation "siteAt" => ProtocolRAMTurnEdges.visit B (siteNumber h (2^W) k).injective pad

include aligned in
theorem forward_site (z : RawBoundary (h:=h) (W:=W) (k:=k) (edges:=edges)) (keep : ProtocolRAMLiveTurnOrder.retain fixed z.1) :
    (HistoryRoles.name (allSite S π depth mark (liveVisit S π depth mark B pad fixed ident
      (rawLive S π B pad fixed z keep)))).val=siteAt z.1 z.2.val := by
  rcases z with ⟨(e|i|c),j⟩
  · let sp:=(Spine.exists_of_walk ((L).paths (.inl e))).some
    have fixed_at (side : Bool) :
        (HistoryRoles.name (allSite S π depth mark (liveVisit S π depth mark B pad fixed ident
          (.inl (⟨e,keep⟩,side))))).val =
        if side then (filledChord B.actual pad e).1.2.val else (filledChord B.actual pad e).1.1.val := by
      let v : LiveVisit S π B pad fixed := .inl (⟨e,keep⟩,side)
      have placed := live_site S π depth mark B pad fixed ident aligned v sp
      have edge := visit_fixed B (siteNumber h (2^W) k).injective pad e sp (boundaryOf S π B pad fixed v)
      have law := congrArg Fin.val (placed.symm.trans edge)
      cases side <;> exact law
    change Fin 2 at j
    fin_cases j
    · exact fixed_at false
    · exact fixed_at true
  · change (HistoryRoles.name (site π (commodityTurn i (boundaryIndex _ _ _ (rawBoundary _ _ _ _)).val))).val=_
    rw [raw_phase];rfl
  · change (HistoryRoles.name (site π (reserveTurn c (boundaryIndex _ _ _ (rawBoundary _ _ _ _)).val))).val=_
    rw [raw_phase];rfl

variable (order : Fin n ≃ ProtocolRAMTurnGeometry.Source edges h (2^W) k)
variable (col : Fin (turns (ProtocolRAMTurnGeometry.length ∘ order))→Fin 7→ℕ)
    (kept : ∀u : Live col,ProtocolRAMLiveTurnOrder.retain fixed (rawItem order u.val).1)

def chartPut : Live col ↪ Seats (siteLast h (2^W) k+1) (room (k:=k) (attempts:=attempts) S) :=
  paid ((onRaw S π B pad fixed order col kept).trans (liveVisit S π depth mark B pad fixed ident))
    (allSite S π depth mark) (siteNumber h (2^W) k).toEmbedding (allSeat S π depth mark uni)

end Hierarchy.ProtocolRAMPaidTurnPlacement

namespace Hierarchy.ProtocolRAMPaidTurnPlacement.Canonical
open AdaptiveProbe ProbeStage CoreBoard WordSeats ReportSockets HistoryRoles WireTelescope SettledMatrix
open ProtocolRAM.Calendar CoreRoute ProtocolRAMTurnOrder ProtocolRAMTurnChart ProtocolRAMTurnShelf
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical

variable {h W k attempts edges : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : Marks h W k attempts) (uni : Exclusive mark)
    (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges) (pad : Chord (siteLast h (2^W) k+1))
local notation "inj" => Equiv.injective (siteNumber h (2^W) k)
local notation "names" => Equiv.symm (ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k)
local notation "len" => ProtocolRAMTurnGeometry.length ∘ names

/-- The physical shelf embedding and the chosen settled spine name the same
party at the canonical boundary. The comparison also covers repeated visits. -/
theorem put_site (fixed : Fin edges → ℕ) (ident : {e // 0 < fixed e} ↪ Catalogue S π depth mark)
    (aligned : ∀e : {e //0<fixed e},filledChord B.actual pad e.val = HistoryRoles.sorted S π depth mark (.inl (ident e)))
    (col : Fin (turns len) → Fin 7 → ℕ)
    (kept : ∀u : Live col,ProtocolRAMLiveTurnOrder.retain fixed (rawItem names u.val).1)
    (u : Live col) :
    (chartPut S π depth mark uni B pad fixed ident names col kept u).1 =
      (spines B inj pad (posn B inj pad u.val).1).visit (posn B inj pad u.val).2 := by
  apply Fin.ext
  exact (forward_site S π depth mark B pad fixed ident aligned (rawItem names u.val) (kept u)).trans
    (visit_at B inj pad u.val).symm

end Hierarchy.ProtocolRAMPaidTurnPlacement.Canonical

end
end OAI
