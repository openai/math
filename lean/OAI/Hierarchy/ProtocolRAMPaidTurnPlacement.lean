import OAI.Hierarchy.ProtocolRAMLiveTurnOrder
import OAI.Hierarchy.TaggedWireSeatCodes
import OAI.Hierarchy.ProtocolRAMTurnInstalled

namespace OAI
/-! # Paid coordinates of the actual fixed, commodity and reserve itinerary rows -/

noncomputable section
namespace Hierarchy.ProtocolRAMPaidTurnPlacement
open ProbeStage ProbeStage.CoreBoard ProbeStage.CoreBoard.WordSeats ReportSockets
open AdaptiveProbe WireTelescope SettledMatrix ProtocolRAMTurnShelf
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical

variable {h W k attempts edges n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
  (depth : ℕ) (marked : Marks h W k attempts) (uni : Exclusive marked)
  (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges)
  (pad : Chord (siteLast h (2^W) k+1)) (fixed : Fin edges→ℕ)
  (ident : {i // 0<fixed i} ↪ Catalogue S π depth marked)

private abbrev Sources (edges h W k : ℕ) :=
  SettledMatrix.Source edges (Commodity (Fin (2^h)) (Stages h (2^W)) k)
    (Columns h (2^W) × Fin k)

variable (order : Fin n ≃ Sources edges h W k) (width : Sources edges h W k→ℕ)
  (fixedWidth : ∀e,width (.inl e)=fixed e)
  (col : Fin (ProtocolRAMTurnOrder.turns (ProtocolRAMLiveTurnOrder.length S π B pad order))→Fin 7→ℕ)
  (live : ∀ i,col i 4=width (ProtocolRAMLiveTurnOrder.boundaries S π B pad order i).1)

def semantic : Live col ↪ LiveVisit S π B pad fixed :=
  (show Live col ↪ {i : Fin (ProtocolRAMTurnOrder.turns (ProtocolRAMLiveTurnOrder.length S π B pad order)) //
      0<width (ProtocolRAMLiveTurnOrder.boundaries S π B pad order i).1} from
    ⟨fun u=>⟨u.val,(live u.val) ▸ Nat.pos_of_ne_zero u.property⟩,
      fun _ _ eq=>Subtype.ext (congrArg
        (fun v : {i : Fin _ // 0<width (ProtocolRAMLiveTurnOrder.boundaries S π B pad order i).1} => v.val)
        eq)⟩).trans
        (ProtocolRAMLiveTurnOrder.positive S π B pad fixed order width fixedWidth)

/-- The destination uses the public half-port prefix for an active identity and
the separately paid payload, altimeter, and reserve seats for every other visit. -/
def put : Live col ↪ Seats (siteLast h (2^W) k+1) (room (k:=k) (attempts:=attempts) S) :=
  paid ((semantic S π B pad fixed order width fixedWidth col live).trans
      (liveVisit S π depth marked B pad fixed ident))
    (allSite S π depth marked) (siteNumber h (2^W) k).toEmbedding (allSeat S π depth marked uni)

theorem coordinate (u : Live col) :
    let x := semantic S π B pad fixed order width fixedWidth col live u
    let p := put S π depth marked uni B pad fixed ident order width fixedWidth col live u
    p.1=HistoryRoles.name (allSite S π depth marked (liveVisit S π depth marked B pad fixed ident x)) ∧
    p.2=localSeat S π depth marked uni B pad fixed ident x := ⟨rfl,rfl⟩

end Hierarchy.ProtocolRAMPaidTurnPlacement

end
end OAI
