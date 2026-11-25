import OAI.Hierarchy.ProtocolRAMDateSpillKeyRead
import OAI.Hierarchy.ProtocolRAMDateSpillTurns
import OAI.Hierarchy.ProtocolRAMPaidTurnCoordinates

namespace OAI
/-! # Physical occurrence, ordinal and seat on dated commodity visits -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.DateSpill.Turns
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreBoard.WordSeats WireTelescope
open ProtocolRAMTurnItinerary ProtocolRAMTurnChart ProtocolRAMTurnShelf ProtocolRAM.Calendar
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical Fin.CommRing

theorem indexed_occurrence (t : Turn) (bounded : t.position≤t.length) (side : Bool)
    (inside : ¬t.boundary side) : ∃j:Fin t.length,t.occurrence side=t.origin+j.val := by
  unfold Turn.boundary at inside
  cases side <;> cases rev : t.reverse <;> simp only [Bool.false_eq_true,ite_false,ite_true] at inside ⊢
  all_goals
    unfold Turn.occurrence
    simp only [rev,Bool.false_eq_true,ite_false,ite_true,Bool.not_true,Bool.not_false,Bool.toNat_false,Bool.toNat_true]
    exact ⟨⟨_,by omega⟩,rfl⟩

variable {h W k n edges attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges)
    (pad : Chord (siteLast h (2^W) k+1)) (o : CoreRoute.Orders h (2^W) k)
local notation "Src" => ProtocolRAMTurnGeometry.Source edges h (2^W) k
local notation "inj" => (siteNumber h (2^W) k).injective
local notation "vis" items => ProtocolRAMVisitAdjacency.vertex (ProtocolRAMTurnGeometry.length ∘ items)
  (fun a=>ProtocolRAMTurnEdges.visit B inj pad (items a))
local notation "roles" => WordSeats.fixedRoom (k:=k) (attempts:=attempts) S
local notation "reg" items => ProtocolRAMTurnGeometry.header o roles items

/-- A zero permanent head has no paid code to fabricate. All genuine live visits use
the authenticated positions in the existing paid/commodity/center header. -/
def noPaid (depth : ℕ) (mark : ReportSockets.Marks h W k attempts) :
    {_i : Fin edges // 0<(0:ℕ)} ↪ Catalogue S π depth mark :=
  ⟨fun x=>False.elim (Nat.not_lt_zero _ x.property),by intro x y h;exact False.elim (Nat.not_lt_zero _ x.property)⟩

def placed (depth : ℕ) (mark : ReportSockets.Marks h W k attempts) (unique : ReportSockets.Exclusive mark) (items : Fin n≃Src)
    (words : Words) (values : Values) (oldBase newBase : ℕ→ℕ)
    (zero : ∀e : Fin edges,words.width (ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k (.inl e)).val=0) :
    let col:=fun i=>fieldWords (record (reg items) words (vis items) i) values oldBase newBase
    {put : Live col ↪ Seats (siteLast h (2^W) k+1) (WordSeats.room (k:=k) (attempts:=attempts) S) //
      ∀z,(put z).1.val=(record (reg items) words (vis items) z.val).site ∧
        (put z).2.val=(record (reg items) words (vis items) z.val).seat} := by
  intro col
  have retained : ∀z:Live col,ProtocolRAMLiveTurnOrder.retain (fun _=>0)
      (ProtocolRAMPaidTurnPlacement.rawItem items z.val).1 :=
    ProtocolRAMPaidTurnPlacement.record_keep (S:=S) (π:=π) (B:=B) (pad:=pad) (fixed:=fun _=>0)
      (attempts:=attempts) (words:=words) (order:=items) o values zero
  let ident:=noPaid (edges:=edges) S π depth mark
  refine ⟨ProtocolRAMPaidTurnPlacement.chartPut S π depth mark unique B pad (fun _=>0) ident items col retained,?_⟩
  exact ProtocolRAMPaidTurnPlacement.loc (S:=S) (π:=π) (depth:=depth) (mark:=mark) (uni:=unique) (B:=B)
    (pad:=pad) (fixed:=fun _=>0) (ident:=ident) (order:=items) (col:=col) (kept:=retained) (words:=words)
    (aligned:=fun i=>False.elim (Nat.not_lt_zero _ i.property))
    (fixedWords:=fun i=>False.elim (Nat.not_lt_zero _ i.property)) o


end Hierarchy.ProtocolRAM.DateSpill.Turns

end
end OAI
