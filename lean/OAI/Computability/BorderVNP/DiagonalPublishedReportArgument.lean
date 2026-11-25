import OAI.Computability.BorderVNP.DiagonalPublishedReachedRows

/-! # A signed argument preparation from a published packet and a bare report return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock
open CellSparse CellSparse.Packet CellSparse.Packet.Source SiteWords CellPacket CellPacket.Supplement
open TypedTaskBuilder FragmentRows SignedTaskArena DiagonalTallyCellReports DiagonalTallyAllocation

variable {w n p d H description ctl offsets length : ℕ} {a : SignedTaskArena.Layout} {O E : Type}
    (G : SiteWords.Directory (Fin n) O (a.cube.cells+1)) (ptr : O → E) (base : ℕ → ℕ) (slot : O → ℕ)
    (fs : O → List Factor) {pub : Arg → Word w} {m : Memory w} {s : RoutingISA.Bank w} {mac : TeamOpcode.Macros w 8}
    {banks : CellBanks.Layout} {rl : ReportLayout} {reports : List (ReportCell rl)} {q : ReportCursor}
    (r : Returns prepareCellReports pub mac s m) {team live ports : ℕ}
set_option quotPrecheck false
local notation "head" => readings pub 0
local notation "mem" => readings r.val.2.2
local notation "f" => FragmentRows.Layout.fromFrame head mem
local notation "R" => a.controlRows team head offsets ctl live ports
local notation "top" => descriptorBank (ctl+37) p
local notation "pubRoom" => a.cube.cells+1+G.words.length+(a.cube.cells+1)≤2^p
local notation "descRoom" => a.cube.cells+1+(Schema.coords (G.referenceRows ptr).length).length+(a.cube.cells+1)≤2^d

set_option maxHeartbeats 1600000 in
/-- Run the two deterministic producers, using the original ordered packet,
the delivered original boxes and the cell-budget bounds on the sampled report.
This constructs the entire argument input before any later native call. -/
theorem Published.owned_report_argument_input {args : E → ℕ} (out : Published G p d (ctl+37) H ptr args base)
    (addresses : ∀ i, args (ptr i)=slot i) (alloc : ReportAllocation a.before a.after banks rl reports q)
    (seed : PreparedReportInput pub m reports q description)
    (fit : (f).Fits w mem) (pointer : mem (head+92)=ctl) (words : ∀ j : Fin 37, mem (ctl+j.val)=a.controls j.val)
    (place : a.SparsePlacement head ctl) (gp : SparseGeometry a f offsets ctl)
    (cables : (f).host.count=a.cube.cables) (raw : mem (head+9)≤a.cube.maxRows)
    (cc : mem (head+11)=a.cube.cells) {u v k : ℕ} (limit : a.endAddress w u v k<2^w)
    (outer : (R).Fields mem) (word : mem (head+30)=w) (calls : mem (head+14)=a.before.limit)
    (tasks : mem (head+89)=(R).tasks) (geometry : TaskSourceGeometry a head offsets ctl mem (some team))
    (fromControls : ∀ z, ctl+37≤z → z<a.cube.header.header → readings m z=base z)
    (physical : banks.bankStart=a.cube.cellBank) (frameEq : rl.frame=head)
    (sorted : (R).sorted=top) (padded : (R).padded=2^d)
    (stops : (R).stops=a.cube.cells+1+(Schema.coords (G.referenceRows ptr).length).length)
    (tableRoom : top+2*(2^d)≤a.cube.header.header)
    (ranks : ∀ j : Fin (2^d), base (top+(2^d+j.val))<2^d)
    (ordered : DescriptorRanks (a.cube.cells+1) (R).stops d (R).sorted base)
    {source : ℕ → ℕ} (controls : (R).Room w) (image : readings m=(R).published source)
    (fitBefore : a.before.limit<2^w)
    (numeric : ∀ i, a.cube.cellBank ≤ slot i ∧ slot i+description≤a.cube.stop)
    (body : ∀ i, H+(boxBody (fs i)).length≤description) (widths : ∀ i, (boxBody (fs i)).length<2^H)
    (reportsAt : ∀ c : Fin a.cube.cells, ∃ b, G.reports c.castSucc=countFields b a.before.bound.gadgets a.before.bound.countWidth)
    (hn : 1≤length) (hw : 0<w) (hW : w≤length)
    (scratch : scratchWindow length≤a.p.scratchStride) (burst : burstWindow length≤a.p.burstStride)
    (returned : ∀ (e : SparseEmission a f r.val.2.2 fit cc.symm)
      (first : Returns emitBucket pub mac r.val.2.1 r.val.2.2),
      e.bank=first.val.2.1 → e.output=first.val.2.2 →
      let emitted := readings e.output
      (R).before emitted (R).cells=reports.length ∧
      (∀ j : Fin reports.length, reports[j].number=globalCell (R).toLayout emitted j.val) ∧
      (∀ c : Fin a.cube.cells, (R).owner emitted c.val=(R).team → ∀ i, Sum.inr i∈G.cellBoxes c.castSucc →
        Delivered (description:=description) mem (slot i) H (fs i)) ∧
      ∃ (data : ℕ → ℕ → Bool) (rows : (i : Fin ((R).before emitted (R).cells)) → SparseCell a f r.val.2.2 data i.val),
        (∀ i, (rows i).number.val=globalCell (R).toLayout emitted i.val) ∧
        ∀ (hf : pubRoom) (hs : descRoom),
          let places := Terminal.placeAt (signedPlaces (ctl:=ctl) (H:=H) G ptr base slot fs (R) emitted hf hs)
          let fields := SparseEmission.globalCells (team:=team) (frame:=head) (offsets:=offsets) (ctl:=ctl)
            (live:=live) (ports:=ports) e rows
          ∀ c < (R).cells, (R).owner emitted c=(R).team →
            let logical := SparseExterior.logicalCell (places c) (seedExtras reports q c) (fields c).field
            (CompactFrame.pack w (Packet.input logical.directory logical.privateWires (fields c).field.bytes)).length ≤
              TeamScales.width length (1/2) ∧ logical.directory.ProfileWidths ∧
                SparseExterior.clock w logical.directory logical.privateWires (fields c).field≤length^25) :
    Nonempty (SignedPrep.ArgumentInput pub mac r.val.2.1 r.val.2.2) := by
  apply SignedPrep.ArgumentInput.ofOwnedCells (Site:=O) (n:=length) pub mac r.val.2.1 r.val.2.2 a fit pointer words
    place gp cables raw cc limit outer word calls tasks geometry description
  intro first e hb hm next built
  obtain ⟨size,ordinal,bodiesAt,data,rows,rowOrder,paid⟩ := returned e first hb hm
  obtain ⟨_,_,_,patch,result,_,_,facts⟩ := out.reached_report_fields G ptr base slot fs r addresses alloc seed
    fit pointer place gp cc limit geometry fromControls physical frameEq sorted padded stops tableRoom ranks ordered
    controls image fitBefore numeric body widths reportsAt hn hw hW scratch burst e size ordinal bodiesAt rows rowOrder
    paid next built
  exact ⟨patch,result,data,rows,facts⟩

/-- An all-cell bound also supplies the native argument preparation. -/
theorem Published.report_argument_input {args : E → ℕ} (out : Published G p d (ctl+37) H ptr args base)
    (addresses : ∀ i, args (ptr i)=slot i) (alloc : ReportAllocation a.before a.after banks rl reports q)
    (seed : PreparedReportInput pub m reports q description)
    (fit : (f).Fits w mem) (pointer : mem (head+92)=ctl) (words : ∀ j : Fin 37, mem (ctl+j.val)=a.controls j.val)
    (place : a.SparsePlacement head ctl) (gp : SparseGeometry a f offsets ctl)
    (cables : (f).host.count=a.cube.cables) (raw : mem (head+9)≤a.cube.maxRows)
    (cc : mem (head+11)=a.cube.cells) {u v k : ℕ} (limit : a.endAddress w u v k<2^w)
    (outer : (R).Fields mem) (word : mem (head+30)=w) (calls : mem (head+14)=a.before.limit)
    (tasks : mem (head+89)=(R).tasks) (geometry : TaskSourceGeometry a head offsets ctl mem) :
    type_of% (out.owned_report_argument_input (length:=length) G ptr base slot fs r addresses alloc seed fit pointer words place gp
      cables raw cc limit outer word calls tasks (geometry.atTeam team)) :=
  out.owned_report_argument_input (length:=length) G ptr base slot fs r addresses alloc seed fit pointer words place gp
    cables raw cc limit outer word calls tasks (geometry.atTeam team)

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
