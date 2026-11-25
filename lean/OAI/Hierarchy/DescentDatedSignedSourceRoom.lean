import OAI.Hierarchy.DescentDatedSignedCuts

namespace OAI
/-! Containment of actual donor and return columns, prior port windows, and the
three source-side lookup tables. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentParallelBase DescentSixParty.Chronology DescentSharedCableNames DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (s:SignedExtent) (base:ℕ) {w:ℕ}

theorem local_slice (z:s.Socket) (f:Fin 11) (stop:ℕ) (paid:s.projectedStart base≤ stop) (room:stop<2^w):
    (subbank (s.localStart base) s.slab (s.localId z f)).Fits w stop:=
  slice_fits (finProdFinEquiv (s.socketId z,f)) paid room

theorem proj_slice (z:s.Socket) (f:Fin 11) (l:Fin s.lowSites) (stop:ℕ) (paid:s.forwardBase base≤ stop) (room:stop<2^w):
    (subbank (s.projectedStart base) s.oldSlab (s.projectedId z f l)).Fits w stop:=
  slice_fits (finProdFinEquiv (finProdFinEquiv (s.socketId z,f),l)) paid room

theorem return_slice (c:s.Consumer) (f:Fin 11) (stop:ℕ) (paid:s.shapesStart base≤ stop) (room:stop<2^w):
    (subbank (s.returnedStart base) s.oldSlab (s.returnedId c f)).Fits w stop:=
  slice_fits (finProdFinEquiv (s.requestId c,f)) paid room

theorem room_later {s₀ s₁:ℕ} {B:Bank} (old:B.Fits w s₀) (order:s₀≤ s₁):B.Fits w s₁:=
  ⟨old.1,old.2.1,old.2.2.trans order⟩

theorem retarget {H G M P:ℕ} {B B':Bank} {src stop:ℕ} {ports:Ports P}
    (old:Accessible ports B H G M w src) (order:src≤ stop) (target:B'.Fits w stop)
    (size:H*chunks G M≤B'.size):Accessible ports B' H G M w stop:=
  ⟨fun i=>room_later (old.ids i) order,old.idsRoom,room_later old.roster order,old.rosterRoom,
    room_later old.offsets order,old.offRoom,room_later old.chunks order,old.chunkRoom,target,size⟩

variable (I:s.Input)
/-- Every numerical source originates before the first physical write. -/
structure Prior (s:SignedExtent) (I:s.Input) (base w:ℕ):Prop where
  rank:DescentOrdinaryDonorRankDirectory.Fits I.rankBanks base s.priorHosts s.reach w
  path:∀z,(I.path z).Fits w base
  endpoint:∀z t,(I.endpoints z t).Fits w base
  material:∀z j,(I.donor z j).Fits w base
  mark:∀z,(I.mark z).Fits w base
  forward:∀x o,(I.donorForward x o).Fits w base
  low:∀x o,(I.donorLow x o).Fits w base
  reverse:I.reversePath.Fits w base
  reverseRows:s.priorHosts*s.reach≤I.reversePath.size
  ports:∃B,Accessible I.ports B s.priorHosts s.groups s.lanes w base

theorem rank_fitted (ok:s.Prior I base w) (f:DescentOrdinaryDonorRankDirectory.Field):
    (DescentOrdinaryDonorRankDirectory.expression I.rankBanks s.priorHosts f).Fits w base:=by
  have prev:(Expr.lookup I.rankBanks.previous .row).Fits w base:=⟨ok.rank.previous,trivial⟩
  have peer:(Expr.lookup I.rankBanks.endpoints (.lookup I.rankBanks.previous .row)).Fits w base:=⟨ok.rank.endpoints,prev⟩
  cases f
  · exact ⟨peer,trivial,trivial,ok.rank.reverse,prev⟩
  · exact ⟨peer,trivial,trivial,ok.rank.localFit,⟨ok.rank.offset,peer⟩,ok.rank.suffix,trivial⟩
  · exact ⟨peer,trivial,trivial,ok.rank.shared,trivial⟩

local notation "P"=>s.reach
local notation "a"=>s.reverseBits
local notation "lf"=>Packed.bits s.lowSites
local notation "joint"=>Packed.bits (P*s.lowSites)
local notation "fwd"=>joined (binary (SourceReturn.Query.forward P s.lowSites) s.lanes) s.forwardBits (s.forwardBase base) id
local notation "bwd"=>joined (binary (SourceReturn.Query.finish P s.lowSites) s.lanes) s.finishBits (s.backBase base) id
local notation "chart"=>DescentPackedChildNeighbor.SIMD.ROM.layout (s.reverseBase base) P a a s.lanes (Nat.clog 2 s.oldSlab) I.reversePath

theorem reverse_room (ok:s.Prior I base w) (x:Fin s.blocks) (o:Fin s.residentSlots) (stop:ℕ)
    (paid:s.viewBase base≤ stop) (room:stop+s.oldSlab<2^w):
    DescentPackedChildNeighbor.SIMD.Room chart (I.donorForward x o) s.priorHosts s.groups a a s.lanes w stop:=by
  have early:base≤ stop:=(s.cuts_mono base (by decide:(0:Fin 22)≤2)).trans paid
  refine packed_room _ _ (room_later ok.reverse early) ok.reverseRows (ProtocolRAMGeneratedWrite.fits_mono _ early (ok.forward _ _)) ?_ room
  simpa only [viewBase,reverseBase,mapWords,reverseLookup,oldSlab,Nat.add_assoc] using paid

theorem forward_room (ok:s.Prior I base w) (x:Fin s.blocks) (o:Fin s.residentSlots) (stop:ℕ)
    (paid:s.backBase base≤ stop) (room:stop<2^w):
    DescentPackedZip.Fits fwd (I.donorForward x o) (I.donorLow x o) a lf s.lanes stop w:=by
  have early:base≤ stop:=(s.cuts_mono base (by decide:(0:Fin 22)≤10)).trans paid
  apply binary_fits _ _ _ _ _ (ProtocolRAMGeneratedWrite.fits_mono _ early (ok.forward _ _))
    (ProtocolRAMGeneratedWrite.fits_mono _ early (ok.low _ _)) (fun _=>rfl) _ le_rfl paid room
  exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)

theorem route_room (ok:s.Prior I base w) (x:Fin s.blocks) (o:Fin s.residentSlots) (stop:ℕ)
    (paid:s.routeStart base≤ stop) (room:stop+s.oldSlab<2^w):
    DescentPackedZip.Fits bwd ((fwd).read (I.donorForward x o) (I.donorLow x o)) (s.backDigit I base x o)
      joint a s.lanes stop w:=by
  have wide:stop<2^w:=(Nat.le_add_right ..).trans_lt room
  have f:=s.forward_room base I ok x o stop ((s.cuts_mono base (by decide:(10:Fin 22)≤11)).trans paid) wide
  have r:=s.reverse_room base I ok x o stop ((s.cuts_mono base (by decide:(2:Fin 22)≤11)).trans paid) room
  apply binary_fits _ _ _ ((fwd).read (I.donorForward x o) (I.donorLow x o)) _ ⟨f.apply,f.right,f.shift,f.left⟩ (DescentPackedChildNeighbor.SIMD.fitted _ _ r _) (fun _=>rfl) _ le_rfl paid wide
  exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)

theorem project_access (ok:s.Prior I base w) (z:s.Socket) (f:Fin 11) (l:Fin s.lowSites) (stop:ℕ)
    (paid:s.forwardBase base≤ stop) (room:stop<2^w):
    Accessible I.ports (subbank (s.projectedStart base) s.oldSlab (s.projectedId z f l)) s.priorHosts s.groups s.lanes w stop:=by
  obtain ⟨B,before⟩:=ok.ports
  exact retarget before ((s.cuts_mono base (by decide:(0:Fin 22)≤9)).trans paid) (s.proj_slice base z f l stop paid room) (span_ge _)

theorem traverse_room (ok:s.Prior I base w) (c:s.Consumer) (f:Fin 11) (j:Fin s.routeTotal) (stop:ℕ)
    (paid:s.returnedStart base≤ stop) (room:stop+s.oldSlab<2^w):
    DescentPackedZip.Fits (SourceReturn.RAM.ROM.table P s.lowSites s.fieldBits s.lanes (s.routeStart base) j)
      (s.routeQuery I base c.1.1 (s.priorSlot c).2)
      (peerExpr I.ports (subbank (s.projectedStart base) s.oldSlab (s.projectedId
        (s.sourceAt c (SourceReturn.RAM.parts j).2.2) f (SourceReturn.RAM.parts j).2.1)) s.priorHosts (SourceReturn.RAM.parts j).1)
      (Packed.bits s.routeTotal) s.fieldBits s.lanes stop w:=by
  have wide:stop<2^w:=(Nat.le_add_right ..).trans_lt room
  have q:=s.route_room base I ok c.1.1 (s.priorSlot c).2 stop ((s.cuts_mono base (by decide:(11:Fin 22)≤12)).trans paid) room
  have access:=s.project_access base I ok (s.sourceAt c (SourceReturn.RAM.parts j).2.2) f (SourceReturn.RAM.parts j).2.1 stop
    ((s.cuts_mono base (by decide:(9:Fin 22)≤12)).trans paid) wide
  apply binary_fits _ _ _ (s.routeQuery I base c.1.1 (s.priorSlot c).2) _ ⟨q.apply,q.right,q.shift,q.left⟩ (peer_fits _ _ _ access _)
    (SourceReturn.RAM.ROM.at_ j) _ le_rfl paid wide
  exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
