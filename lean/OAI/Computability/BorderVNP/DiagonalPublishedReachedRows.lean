import OAI.Computability.BorderVNP.DiagonalSignedPhysicalReachedCells
import OAI.Computability.BorderVNP.DiagonalSignedFragmentDescriptorOrder

/-! # Source packet markers and sparse cells on one signed typed return -/

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
/-- The original packet arrays, their selected sparse rows and the paid typed
source are recovered together on the actual compact builder RAM. -/
theorem Published.reached_report_fields {args : E → ℕ} (out : Published G p d (ctl+37) H ptr args base)
    (addresses : ∀ i, args (ptr i)=slot i) (alloc : ReportAllocation a.before a.after banks rl reports q)
    (seed : PreparedReportInput pub m reports q description)
    (fit : (f).Fits w mem) (pointer : mem (head+92)=ctl)
    (place : a.SparsePlacement head ctl) (gp : SparseGeometry a f offsets ctl)
    (cc : mem (head+11)=a.cube.cells) {u v k : ℕ} (limit : a.endAddress w u v k<2^w)
    (geometry : TaskSourceGeometry a head offsets ctl mem (some team))
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

    (e : SparseEmission a f r.val.2.2 fit cc.symm)
    (size : (R).before (readings e.output) (R).cells=reports.length)
    (ordinal : ∀ j : Fin reports.length, reports[j].number=globalCell (R).toLayout (readings e.output) j.val)
    (bodiesAt : ∀ c : Fin a.cube.cells, (R).owner (readings e.output) c.val=(R).team →
      ∀ i, Sum.inr i∈G.cellBoxes c.castSucc → Delivered (description:=description) mem (slot i) H (fs i))
    {data : ℕ → ℕ → Bool} (rows : (i : Fin ((R).before (readings e.output) (R).cells)) →
      SparseCell a f r.val.2.2 data i.val)
    (rowOrder : ∀ i, (rows i).number.val=globalCell (R).toLayout (readings e.output) i.val)
    (paid : ∀ (hf : pubRoom) (hs : descRoom),
      let places := Terminal.placeAt (signedPlaces (ctl:=ctl) (H:=H) G ptr base slot fs (R) (readings e.output) hf hs)
      let fields := SparseEmission.globalCells (team:=team) (frame:=head) (offsets:=offsets) (ctl:=ctl)
        (live:=live) (ports:=ports) e rows
      ∀ c < (R).cells, (R).owner (readings e.output) c=(R).team →
        let logical := SparseExterior.logicalCell (places c) (seedExtras reports q c) (fields c).field
        (CompactFrame.pack w (Packet.input logical.directory logical.privateWires (fields c).field.bytes)).length ≤
          TeamScales.width length (1/2) ∧ logical.directory.ProfileWidths ∧ SparseExterior.clock w logical.directory
            logical.privateWires (fields c).field≤length^25)
    (next : Returns TypedTaskBuilder.program pub mac e.bank e.output)
    (built : readings next.val.2.2=(R).toLayout.published (readings e.output)) :
    ∃ (hf : pubRoom) (hs : descRoom),
      let pl := signedPlaces (ctl:=ctl) (H:=H) G ptr base slot fs (R) (readings e.output) hf hs
      TypedBatch.SourceShape pl G ∧
      ∃ patch : SparsePatch (w:=w) O (R) (readings e.output),
        patch.built=next.val.2.2 ∧ patch.placed=Terminal.placeAt pl ∧ patch.extra=seedExtras reports q ∧
        ReachedReportCells (n:=length) e patch rows description := by
  have fitDesc : descRoom := out.choose_spec.choose
  have marker : (R).stops+(a.cube.cells+1)≤2^d := stops ▸ fitDesc
  have rank := signed_fragment_descriptor_order alloc seed r e place gp base fromControls physical frameEq
    (R) rfl padded (by rw [sorted]; exact Nat.le_add_right ..)
    (by rwa [sorted,padded]) marker ordered
  obtain ⟨hf,hs,shaped,prepare⟩ := out.signed_reached_cells G ptr base slot fs addresses alloc seed r e place gp fromControls
    physical frameEq sorted padded stops tableRoom ranks controls image fitBefore size ordinal numeric body widths
    reportsAt bodiesAt hn hw hW scratch burst rank
  have taskRoom := e.task_room_owned (team:=team) pointer place geometry limit
  obtain ⟨patch,result,moved,_,extras,sourceRows⟩ := prepare next.val.2.2 built taskRoom
  exact ⟨hf,hs,shaped,patch,result,moved,extras,sourceRows data rows rowOrder (paid hf hs)⟩

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
