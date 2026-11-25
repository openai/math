import OAI.Hierarchy.DescentDatedOrdinarySignedMeasured
import OAI.Hierarchy.DescentDatedSignedSourceRoom

namespace OAI
/-! All numerical bounds needed to compare a parent at its true remote
source. Only the prior physical banks and the public floor and ceiling enter. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentParallelBase DescentSixParty.Chronology DescentSharedCableNames DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (s:SignedExtent) (I:s.Input) (base:ℕ) {w:ℕ}
local notation "end₀"=>s.tailStart base
local notation "end₁"=>s.viewBase base

structure MapRoom (s:SignedExtent) (base stop w:ℕ):Prop where
  normalize:(subbank (s.mapBase base) s.viewRows 0).Fits w stop
  transpose:∀l:Fin s.lowSites,(subbank (s.mapTranspose base) s.oldSlab l.val).Fits w stop
  cell:(subbank (s.mapHost base) s.slab 0).Fits w stop
  chunk:(subbank (s.mapChunk base) s.slab 0).Fits w stop
  offset:(subbank (s.mapOffset base) s.priorHosts 0).Fits w stop

theorem map_room (stop:ℕ) (paid:end₁≤ stop) (room:stop<2^w):s.MapRoom base stop w:=by
  have cum:s.mapBase base+span s.viewRows+s.lowSites*span s.oldSlab+span s.slab+span s.slab+span s.priorHosts≤ stop:=by
    dsimp only [viewBase,mapWords,mapIndices] at paid;omega
  have single (x n:ℕ) (h:x+span n≤ stop):(subbank x n 0).Fits w stop:=
    slice_fits (0:Fin 1) (by simpa only [Nat.one_mul] using h) room
  exact ⟨single _ _ (by omega),fun l=>slice_fits l (by unfold mapTranspose;omega) room,
    single _ _ (by unfold mapHost mapTranspose;omega),
    single _ _ (by unfold mapChunk mapHost mapTranspose;omega),
    single _ _ (by unfold mapOffset mapChunk mapHost mapTranspose;omega)⟩

theorem remote_fitted (ok:s.Prior I base w) (c:s.Consumer) (f:Fin 11) (stop:ℕ)
    (paid:s.shapesStart base≤ stop) (room:stop<2^w):(s.remoteWord I base c f).Fits w stop:=by
  have chart:=s.map_room base stop ((s.cuts_mono base (by decide:(2:Fin 22)≤13)).trans paid) room
  have old:=room_later ok.rank.endpoints ((s.cuts_mono base (by decide:(0:Fin 22)≤13)).trans paid)
  have value:=s.return_slice base c f stop paid room
  have head:(Expr.lookup (subbank (s.mapHost base) s.slab 0) .row).Fits w stop:=⟨chart.cell,trivial⟩
  have pos:(Expr.lookup I.rankBanks.endpoints (.op .add (.lookup (subbank (s.mapHost base) s.slab 0) .row) (.lit (s.priorSlot c).1.val))).Fits w stop:=
    ⟨old,head,trivial⟩
  exact ⟨head,trivial,trivial,pos,trivial,trivial,value,⟨chart.offset,pos⟩,chart.chunk,trivial⟩

theorem gate_room (ok:s.Prior I base w) (c:s.Consumer) (f:Fin 11)
    (gate:(s.flags I base (c.1.1,c.2.1)).Fits w end₀) (room:end₀<2^w):
    DescentPackedZip.Fits (gateTable (s.gateStart base) s.fieldBits s.lanes)
      (s.flags I base (c.1.1,c.2.1)) (if c.1.2.val=2 then s.remoteWord I base c f else s.rawField base (s.socketAt c) f)
      (1*4) s.fieldBits s.lanes end₀ w:=by
  have word:(if c.1.2.val=2 then s.remoteWord I base c f else s.rawField base (s.socketAt c) f).Fits w end₀:=by
    split
    · exact s.remote_fitted I base ok c f end₀ (s.cuts_mono base (by decide:(13:Fin 22)≤21)) room
    · exact ⟨s.local_slice base (s.socketAt c) f end₀ (s.cuts_mono base (by decide:(8:Fin 22)≤21)) room,trivial⟩
  apply binary_fits _ _ _ _ _ gate word (fun _=>rfl) _ le_rfl (s.cuts_mono base (by decide:(17:Fin 22)≤21)) room
  exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)

theorem return_room (ok:s.Prior I base w) (room:s.roof base+max s.slab s.oldSlab<2^w)
    (flags:∀z,(s.flags I base z).Fits w end₀):s.ReturnRoom I base w:=by
  have big:=s.clock_room base room 21
  have hi:end₀+s.oldSlab<2^w:=(Nat.add_le_add_left (le_max_right ..) _).trans_lt big
  have cap:end₀<2^w:=(Nat.le_add_right ..).trans_lt hi
  have p (i:Fin 22):s.cuts base i≤end₀:=s.cuts_mono base (show i≤(21:Fin 22) by omega)
  have m:=s.map_room base end₀ (p 2) cap
  have returns (c:s.Consumer) (f:Fin 11):
      (subbank (s.returnedStart base) s.oldSlab (s.returnedId c f)).base+s.oldSlab≤end₀:=by
    have bank:=(s.return_slice base c f end₀ (p 13) cap).2.2
    exact (Nat.add_le_add_left (span_ge _) _).trans bank
  refine ⟨ok.rank,s.rank_fitted base I ok,fun i=>slice_fits i (p 1) cap,m.normalize,m.transpose,
    fun z f=>s.local_slice base z f end₀ (p 8) cap,fun x o=>⟨ok.forward _ _,ok.low _ _⟩,
    ok.reverse,ok.reverseRows,fun x o=>s.reverse_room base I ok x o end₀ (p 2) hi,
    fun x o=>s.forward_room base I ok x o end₀ (p 10) cap,
    fun x o=>s.route_room base I ok x o end₀ (p 11) hi,ok.ports,
    fun c f l r=>s.project_access base I ok (s.sourceAt c r) f l end₀ (p 9) cap,?_,
    fun c f=>(returns c f).trans_lt cap,m.cell,room_later ok.rank.endpoints (p 0),m.offset,m.chunk,
    fun c f=>s.return_slice base c f end₀ (p 13) cap,fun c f=>s.gate_room I base ok c f (flags _) cap⟩
  intro c f j
  have begins:s.returnedStart base≤(subbank (s.returnedStart base) s.oldSlab (s.returnedId c f)).base:=Nat.le_add_right ..
  exact s.traverse_room base I ok c f j _ begins ((returns c f).trans_lt cap)

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
