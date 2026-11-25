import OAI.Hierarchy.TaggedWideCalendarPacket
import OAI.Hierarchy.TaggedWideCalendarPacketMiddle

namespace OAI
/-! # Evaluating the actual fixed signed branch against an occupied original party -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal MotifOuterTerms TraceWords
open Probe Computability.VPVNP.BurstRAM Tagged AdaptiveProbe TurnShelf CalendarTape
open scoped Classical BigOperators

variable {F V A E B : Type} [Field F] [Fintype V] [Fintype A] [Fintype E] [Fintype B]
    {k r D width cap digits : ℕ} [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}
    (P : Packet F edge req) (G : PortGraph (Fin k) B) (i : Fin k) (t : (portGraph k).Port i)
local notation "keptWidths" => G.chordWidths (fun _=>r*P.selectorBits)
local notation "Pin" => (portGraph k).Port i×Fin cap
local notation "Key" => Fin k→Word digits
variable (fit : r*P.selectorBits≤(G.chordWidths (fun _=>r*P.selectorBits)) t.val.1) (keyPin : Fin k→Fin digits→V)
    (meterPin : Fin P.terms→Fin (Nat.clog 2 (r+1))→V⊕Bool) (pre : Fin D×Fin width→V)

private def branchSocket (key : Key) : SiteHardware.Sockets i→Fin cap→(V⊕Pin)⊕Bool
  | .inl u,j=>Sum.map Sum.inl id (PacketNeighbor.wantedSocket (P.inputWidths r) i key pre u j)
  | .inr u,j=>.inl (.inr (u,j))

/-- The amount vector, spatial placement and complete selector history do not
index its physical branches. Only the fixed strip and the public batch size do. -/
def signedUse : BitNetwork F (Fintype.card (V⊕Pin)) :=
  PacketNeighbor.socketProgram (fun a j=>Sum.inl (keyPin a j)) fun key=>
    SiteHardware.signedProgram P G i t fit (fun a j=>Sum.map Sum.inl id (meterPin a j))
      (branchSocket (r:=r) P i pre key)

private theorem socket_bound {Y : Type} [Fintype Y] {m d : ℕ}
    (pin : Fin m→Fin d→Y) (body : (Fin m→Word d)→BitNetwork F (Fintype.card Y))
    (fee : ℕ) (same : ∀j, (body j).cells+(body j).internal=fee) :
    (PacketNeighbor.socketProgram pin body).cells+(PacketNeighbor.socketProgram pin body).internal≤
      177^(m*d)*Fintype.card (Fin m→Word d)*fee := by
  calc
    _ ≤ 177^(m*d)*∑j,((body j).cells+(body j).internal) := PacketNeighbor.socketProgram_cost pin body
    _ = _ := by simp only [same,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_assoc]

theorem signedUse_cost :
    let n:=signedUse (cap:=cap) P G i t fit keyPin meterPin pre
    let terminal:=P.terminal G i t fit
    n.cells+n.internal≤177^(k*digits)*Fintype.card Key*(terminal.cells+terminal.internal) := by
  let body := fun key : Key => SiteHardware.signedProgram P G i t fit
    (fun a j=>Sum.map Sum.inl id (meterPin a j)) (branchSocket (r:=r) (cap:=cap) P i pre key)
  exact socket_bound (fun a j=>(Sum.inl (keyPin a j) : V⊕Pin)) body _
    (fun key => SiteHardware.signedProgram_cost ..)

private theorem peel {X Y : Type} (x : X→Bool) (y : Y→Bool) (pin : X⊕Bool) :
    Sum.elim (Sum.elim x y) id (Sum.map Sum.inl id pin)=Sum.elim x id pin := by cases pin <;>rfl

theorem signedUse_value (rt : Fin k) (hist : Histogram (Fin P.terms) r) (v : V→Bool)
    (key : Key) (old : State (P.inputWidths r) i) (mid : State (P.outputWidths hist+keptWidths) i)
    (capacity : ∀s : (portGraph k).Port i,keptWidths s.val.1+r*SiteHardware.widthCap (SiteHardware.localWidth P i)≤cap)
    (keyRead : ∀a j,v (keyPin a j)=TraceWords.bits (key a) j)
    (counters : ∀a j,Sum.elim v id (meterPin a j)=SelectorShelf.bits hist _ a j)
    (live : ∀s (j : Fin cap),Sum.elim v id (PacketNeighbor.wantedSocket (P.inputWidths r) i key pre s j)=
      (old s).val.testBit j.val) :
    let m:=fun z : Pin=>(mid z.1).val.testBit z.2.val
    TypedWiring.value (signedUse P G i t fit keyPin meterPin pre) (Sum.elim v m)=
      P.broadcastMatrix rt r G hist i old mid := by
  intro m
  unfold signedUse
  rw [PacketNeighbor.socketProgram_value (fun a j=>(Sum.inl (keyPin a j) : V⊕Pin)) _
    (Sum.elim v m) key (fun a j=>keyRead a j)]
  apply SiteHardware.signedProgram_value P G i t fit _ _ rt hist _ old mid capacity
  · intro a j
    exact (peel v m _).trans (counters a j)
  · intro s j
    exact (peel v m _).trans (live s j)
  · intro s j;rfl

section PlacedParty
variable {S N r D width cap digits b : ℕ} (Q : Placed F S) (hist : Histogram (Fin Q.data.terms) r)
    {rows : Fin N→Chord S} (R : RowRouting (Row.packet Q r) rows)
    (i : Fin Q.sites) (t : (portGraph Q.sites).Port i)
local notation "U" => Q.data.outputWidths hist+Q.graph.chordWidths (fun _=>r*Q.data.selectorBits)
local notation "Roles" => Fintype.card R.Roles
local notation "Role" => Fin Roles×Bool
local notation "w" => Installs.numbered R.order (R.bits hist)
local notation "starts" => Installs.starts (source:=R.source) R.order
local notation "Len" => Fin (BinaryBarrelTurns.digits cap)
variable (fit : r*Q.data.selectorBits≤Q.graph.chordWidths (fun _=>r*Q.data.selectorBits) t.val.1)
    (keyPin : Fin Q.sites→Fin digits→V)
    (meterPin : Fin Q.data.terms→Fin (Nat.clog 2 (r+1))→V⊕Bool) (pre : Fin D×Fin width→V)
    (localEnds : Fin (Fintype.card R.Roles)→Chord Q.sites) (aligned : ∀i,Installs.starts (source:=R.source) R.order i=Probe.physicalChord Q.place (localEnds i))
    (lengthPin : (Fin (Fintype.card R.Roles)×Bool)×(Fin (Fintype.card R.Roles)×Bool)→Fin (BinaryBarrelTurns.digits cap)→V⊕Bool)
    (startPin : (Fin (Fintype.card R.Roles)×Bool)→Bool→Fin (BinaryBarrelTurns.digits cap)→V⊕Bool)
    (middlePin : Fin (middleRoom (Fintype.card R.Roles) cap)→V⊕Bool) (roomPin : (Fin (Fintype.card R.Roles)×Bool)→Fin b→V)
    (fits : ∀i,Installs.numbered R.order (R.bits hist) i≤cap)
local notation "oi" => Middle.parts R hist (Q.place i) cap fits
local notation "term" => signedUse (cap:=cap) Q.data Q.graph i t fit keyPin meterPin pre

include aligned in
theorem signedContribution (v : V→Bool) (key : Fin Q.sites→Word digits)
    (old : State (Q.wants r) (Q.place i)) (yy : State (Q.offers hist) (Q.place i))
    (allFit : ∀p : (portGraph S).Port (Q.place i),(Q.offers hist) p.val.1≤cap)
    (columns : cap≤2^b) (roomFit : ∀q,ChordAperture.room oi q<2^b)
    (sizeRead : ∀u q b,Sum.elim v id (lengthPin (u,q) b)=
      (addressEquiv _).symm (BinaryBarrelTurns.address (ChordAperture.sizeAt oi u q)) b)
    (headRead : ∀u side b,Sum.elim v id (startPin u side b)=
      (addressEquiv _).symm (BinaryBarrelTurns.address (ChordAperture.head oi u side)) b)
    (widthRead : ∀q j,v (roomPin q j)=TraceWords.bits (⟨ChordAperture.room oi q,roomFit q⟩ : Word b) j)
    (middleRead : ∀j,Sum.elim v id (middlePin j)=packedMiddle hist (Q.place i) (middlePlace R hist (Q.place i) cap fits) yy j)
    (capacity : ∀s : (portGraph Q.sites).Port i,
      (Q.graph.chordWidths (fun _=>r*Q.data.selectorBits)) s.val.1+
        r*SiteHardware.widthCap (SiteHardware.localWidth Q.data i)≤cap)
    (keyRead : ∀a j,v (keyPin a j)=TraceWords.bits (key a) j)
    (counters : ∀a j,Sum.elim v id (meterPin a j)=SelectorShelf.bits hist _ a j)
    (before : ∀s (j : Fin cap),Sum.elim v id (PacketNeighbor.wantedSocket (Q.data.inputWidths r) i key pre s j)=
      ((PhysicalMatrix.read Q.place _ i
        (cast (congrArg (fun W=>State W (Q.place i)) (Q.placedInput (r:=r)).symm) old)) s).val.testBit j.val) :
    TypedWiring.value (Middle.packetOrient localEnds i lengthPin startPin middlePin roomPin term) v=
      Q.signed r hist (Q.place i) old yy := by
  rw [Q.signed_at hist i]
  let middle:=PhysicalMatrix.read Q.place U i
    (cast (congrArg (fun W=>State W (Q.place i)) (Q.placedOutput hist).symm) yy)
  calc
    _=TypedWiring.value term (Sum.elim v (fun p : (portGraph Q.sites).Port i×Fin cap=>
        (middle p.1).val.testBit p.2.val)) := by
      apply Middle.packetOrient_value (R:=R) (c:=hist) (v:=v) (yy:=yy) (place:=Q.place)
        (fits:=fits) («U»:=U) (eqn:=(Q.placedOutput hist).symm) <;>assumption
    _=_:=signedUse_value Q.data Q.graph i t fit keyPin meterPin pre Q.root hist v key _ middle
      capacity keyRead counters before

end PlacedParty
end Hierarchy.WireTelescope.ChosenPackets.RowRouting
end

end OAI
