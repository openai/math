import OAI.Hierarchy.DescentRetainedSevenRun
import OAI.Hierarchy.DescentResetRetainedResidents

namespace OAI
namespace Hierarchy.DescentRetainedSeven.Chart
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM DescentPackedColony
open DescentPacking.PackedMatch.Local DescentSixParty.Chronology DescentResetRetainedSetup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical
noncomputable section
variable {w : ℕ} (c : DescentRetainedSeven.Chart)

abbrev Packets := Fin c.retained.hosts→Fin c.retained.grouped→Cell c.control.rootWidth
def roster (which : c.control.Targets) (X : c.Packets) (t : Fin c.placement.shapes) (h : Fin c.retained.hosts) (g : Fin c.retained.grouped) :=
  DescentRetainedControl.filter (D:=c.degree) (cap:=c.capacity) (L:=c.retained.donors) (field:=c.packetBits) (which t) (X h g)
def stripes (which : c.control.Targets) (X : c.Packets) (Y : c.retained.Strips) (t : Fin c.placement.shapes) : c.retained.Strips:=
  fun j h g=>DescentRetainedControl.take c.retained.bits (c.roster which X t h g) (Y j h g)
def decoded (which : c.control.Targets) (X : c.Packets) (Y : c.retained.Strips) (o : Fin c.retained.outputs)
    (t : Fin c.placement.shapes) (h : Fin c.retained.hosts) (g : Fin c.retained.grouped) :=
  let word:=c.retained.function o (c.retained.site (c.stripes which X Y t) h g)
  match (finSumFinEquiv.symm o : Fin ((2*7*c.retained.args)*c.retained.nodes) ⊕ Fin c.retained.nodes) with
  | .inl _=>word
  | .inr _=>c.control.original word (c.roster which X t h g)

/-- The query uses the previously elected matrix and the packet's actual home/comparator fields. -/
theorem query_read (floor : ℕ) (which : c.control.Targets) (old : Fin c.retained.sources→Bank) (saved : Bank)
    (packet : Expr) (m : Memory w) (pf : packet.Fits w floor) (pos : 0<c.packetLanes)
    (X : c.Packets) (seen : Source packet X c.packetLanes m) (Y : c.retained.Strips)
    (previous : ∀j,Reads (c.retained.hostBank floor j) (Y j) c.retained.decodedLanes (c.retained.movedImage floor old saved m))
    (early : ∀i,(old i).Fits w floor) (key : saved.Fits w floor)
    (room : c.place floor<2^w) (o : Fin c.retained.outputs) (t : Fin c.placement.shapes) :
    Source (c.query floor which o t) (c.decoded which X Y o t) c.retained.decodedLanes (c.prepared which floor old saved packet m):=by
  obtain ⟨a,b,d,e,_⟩:=c.intervals floor
  have r2:=d.trans_lt (e.trans_lt room)
  have r1:=b.trans_lt r2
  let m1:=c.retained.movedImage floor old saved m
  let m2:=c.selected which floor old saved packet m
  let m3:=c.joinMem floor m2
  let m4:=c.prepared which floor old saved packet m
  have stayed (z : ℕ) (hz : z<c.tabs floor) : m4 z=m2 z:=
    (ROM.frame _ _ _ _ z (.inl (hz.trans_le d))).trans (ROM.frame _ _ _ _ z (.inl hz))
  have pf1:=ProtocolRAMGeneratedWrite.fits_mono _ a pf
  have pkt : Source packet X c.packetLanes m1:=fun j=>(eval_below _ _ m m1 pf
    (fun z below=>(c.retained.moved_any floor old saved m early key r1).2.1 z (.inl below))).trans (seen j)
  have zero : Source (.lit 0) (fun (_ : Fin c.retained.hosts) (_ : Fin c.retained.grouped)=>(0:Cell c.retained.bits)) c.retained.decodedLanes m1:=by
    intro rowId
    change (0:Word w)=((data (fun (_:Fin c.retained.hosts) (_:Fin c.retained.grouped)=>(0:Cell c.retained.bits)) rowId).val:Word w)
    have h : (data (fun (_:Fin c.retained.hosts) (_:Fin c.retained.grouped)=>(0:Cell c.retained.bits)) rowId).val=0:=by
      change (finFunctionFinEquiv (fun j:Fin c.retained.decodedLanes=>if _ : rowId.2.val*c.retained.decodedLanes+j.val<c.retained.grouped then (0:Cell c.retained.bits) else 0)).val=0
      simp
    simp [h]
  have src (j : Fin c.retained.channels) : Source (c.feeds floor which t j) ((c.stripes which X Y t) j) c.retained.decodedLanes m4:=by
    have bank:=Strip.fits (w:=w) (c.retained.mixed floor) c.retained.hosts c.retained.grouped c.retained.matrixLanes c.retained.decodedLanes c.retained.stripWord j r1
    let expr:=Expr.lookup (c.retained.hostBank floor j) .row
    have expFit : expr.Fits w (c.seen floor):=⟨bank.1,trivial⟩
    have selected:=c.control.issued which (c.seen floor) packet m1 pf1 r2 pos X pkt t expr (.lit 0) expFit trivial
      (Y j) (fun _ _=>0) (source_column _ _ expFit.1 _ _ bank.2 (previous j)) zero
    have fit:=(c.control.paths_fit which (c.seen floor) expr (.lit 0) t
      (ProtocolRAMGeneratedWrite.fits_mono _ b expFit) trivial r2).1
    exact fun k=>(eval_below _ _ m2 m4 fit stayed).trans (selected.1 k)
  have static (j : Fin c.retained.channels) : Static (c.joinTables floor j) (Gather.setField (d:=c.retained.stripWord) j) c.retained.decodedLanes m4:=by
    have installed:=DescentResetNodeBooks.static (c.tabs floor) c.retained.channels c.retained.stripWord c.retained.decodedLanes m2 j
    have guard (i : Fin (c.retained.channels+1)):=ROM.bank_room (DescentResetNodeBooks.page c.retained.stripWord c.retained.channels c.retained.decodedLanes)
      ((c.retained.siteWord+c.retained.stripWord)*c.retained.decodedLanes) (c.tabs floor) (c.lookup floor) i
      (DescentResetNodeBooks.page_bits ..) le_rfl (e.trans_lt room)
    constructor
    · intro k
      exact (ROM.frame _ _ _ _ _ (.inl ((Nat.add_lt_add_left k.isLt _).trans_le (guard 0).2.2))).trans (installed.1 k)
    · intro k
      exact (ROM.frame _ _ _ _ _ (.inl ((Nat.add_lt_add_left k.isLt _).trans_le (guard j.succ).2.2))).trans (installed.2 k)
  let word:=c.retained.site (c.stripes which X Y t)
  have assembled : Source (c.joined floor which t) word c.retained.decodedLanes m4:=by
    have read:=Gather.collected (c.joinTables floor) (c.feeds floor which t) (c.place floor)
      (c.join_bounds floor which t room) m4 static (fun h g j=>c.stripes which X Y t j h g) src (List.finRange c.retained.channels)
    unfold word Layout.site
    unfold feeds at read
    simpa only [joined,joinTables,Gather.assembly,List.mem_finRange,ite_true] using read
  let exp:=Expr.lookup (c.dictionary floor o) (c.joined floor which t)
  have numbers : Source exp (fun h g=>c.retained.function o (word h g)) c.retained.decodedLanes m4:=by
    intro k
    have safe:=ROM.bank_room c.retained.wordPages (c.retained.siteWord*c.retained.decodedLanes) (c.lookup floor) (c.place floor) o le_rfl le_rfl room
    change (c.dictionary floor o).read m4 ((c.joined floor which t).eval m4 _) = _
    rw [assembled k]
    refine (bank_read (c.dictionary floor o) m4 (data word k).isLt safe).trans ?_
    apply (ROM.read c.retained.wordPages (c.retained.siteWord*c.retained.decodedLanes) (c.lookup floor) m3 o le_rfl (data word k)).trans
    apply congrArg (fun z : Cell (c.retained.bits*c.retained.decodedLanes)=>(z.val:Word w))
    simp only [DescentSIMDLookup.table,data,Equiv.symm_apply_apply]
    apply congrArg (encode _ _);funext j
    by_cases live:k.2.val*c.retained.decodedLanes+j.val<c.retained.grouped <;> simp [live,c.retained.function_zero]
  unfold query decoded
  cases ord : (finSumFinEquiv.symm o : Fin ((2*7*c.retained.args)*c.retained.nodes) ⊕ Fin c.retained.nodes) with
  | inl u=>simpa only [query,decoded,ord] using numbers
  | inr u=>
    have orig:=c.control.original_at which (c.seen floor) packet m1 pf1 r2 pos X pkt t m4 stayed
      (c.place floor) (d.trans e) exp (c.lookup_fit floor which t o room) _ numbers
    exact orig.2

end
end Hierarchy.DescentRetainedSeven.Chart

end OAI
