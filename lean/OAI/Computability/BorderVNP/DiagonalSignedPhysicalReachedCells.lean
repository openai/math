import OAI.Computability.BorderVNP.DiagonalSignedPhysicalMergeTable
import OAI.Computability.BorderVNP.DiagonalReachedReportCells
import OAI.Computability.BorderVNP.DiagonalProducedArgumentWindows

/-! # Actual reached signed cells from the selected geometric row table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock
open CellSparse CellSparse.Packet CellSparse.Packet.Source SiteWords CellPacket CellPacket.Supplement
open CellPacket.Supplement.Batch TypedTaskBuilder FragmentRows SignedTaskArena DiagonalTallyCellReports DiagonalTallyAllocation

variable {w n p d H description frame ctl offsets : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout}
    {O E : Type} (G : SiteWords.Directory (Fin n) O (a.cube.cells+1)) (ptr : O → E)
    (base : ℕ → ℕ) (slot : O → ℕ) (fs : O → List Factor)
set_option quotPrecheck false
local notation "top" => descriptorBank (ctl+37) p
local notation "pubRoom" => a.cube.cells+1+G.words.length+(a.cube.cells+1)≤2^p
local notation "descRoom" => a.cube.cells+1+(Schema.coords (G.referenceRows ptr).length).length+(a.cube.cells+1)≤2^d

variable {team live ports : ℕ} {source : ℕ → ℕ}
local notation "R" => a.controlRows team frame offsets ctl live ports

variable {pub : Arg → Word w} {m : Memory w} {s : RoutingISA.Bank w} {mac : TeamOpcode.Macros w 8}
    {banks : CellBanks.Layout} {rl : ReportLayout} {reports : List (ReportCell rl)} {q : ReportCursor}

open BorderVNP.RoutingISA.SparseExterior

set_option maxHeartbeats 1400000 in
/-- Construct the sparse patch on the precise task image supplied by the native
builder. The verified placement, original bodies, actual record stream and the
scheduled private quota then describe the same compact row in both directions
of the signed report correspondence. -/
theorem Published.signed_reached_cells {args : E → ℕ} (out : Published G p d (ctl+37) H ptr args base)
    (addresses : ∀ i, args (ptr i)=slot i) (alloc : ReportAllocation a.before a.after banks rl reports q)
    (seed : PreparedReportInput pub m reports q description) (r : Returns prepareCellReports pub mac s m)
    {fit : f.Fits w (readings r.val.2.2)} {cells : a.fragments.cells=f.cells} (e : SparseEmission a f r.val.2.2 fit cells)
    (place : a.SparsePlacement frame ctl) (gp : SparseGeometry a f offsets ctl)
    (fromControls : ∀ z, ctl+37≤z → z<a.cube.header.header → readings m z=base z)
    (physical : banks.bankStart=a.cube.cellBank) (frameEq : rl.frame=frame)
    (sorted : (R).sorted=top) (padded : (R).padded=2^d)
    (stops : (R).stops=a.cube.cells+1+(Schema.coords (G.referenceRows ptr).length).length)
    (tableRoom : top+2*(2^d)≤a.cube.header.header)
    (ranks : ∀ i : Fin (2^d), base (top+(2^d+i.val))<2^d)
    (controls : (R).Room w) (image : readings m=(R).published source) (fitBefore : a.before.limit<2^w)
    (order : (R).before (readings e.output) (R).cells=reports.length)
    (ordinal : ∀ j : Fin reports.length, reports[j].number=globalCell (R).toLayout (readings e.output) j.val)
    (numeric : ∀ u, a.cube.cellBank≤ slot u ∧ slot u+description≤a.cube.stop)
    (body : ∀ u, H+(boxBody (fs u)).length≤description) (widths : ∀ u, (boxBody (fs u)).length<2^H)
    (reportsAt : ∀ c : Fin a.cube.cells, ∃ b, G.reports c.castSucc=countFields b a.before.bound.gadgets a.before.bound.countWidth)
    (bodiesAt : ∀ c : Fin a.cube.cells, (R).owner (readings e.output) c.val=(R).team →
      ∀ u, Sum.inr u∈G.cellBoxes c.castSucc →
      Delivered (description:=description) (readings r.val.2.2) (slot u) H (fs u))
    {length : ℕ} (hn : 1≤length) (hw : 0<w) (hW : w≤length)
    (scratch : SignedTaskArena.scratchWindow length≤a.p.scratchStride)
    (burst : SignedTaskArena.burstWindow length≤a.p.burstStride)
    (rank : ∀ c c' : Fin a.cube.cells, c<c' →
      readings e.output ((R).sorted+(R).padded+((R).stops+c.val)) < readings e.output ((R).sorted+(R).padded+c'.val)) :
    ∃ hf : pubRoom, ∃ hs : descRoom,
    let raw := readings e.output
    let pl := signedPlaces (ctl:=ctl) (H:=H) G ptr base slot fs (R) raw hf hs
    let p := Terminal.placeAt pl
    let geometry := fun c => (p c).publicBase+((prefixParts (p c)).flatMap Part.publicBuffer).length
    let extra := seedExtras reports q
    TypedBatch.SourceShape pl G ∧
    ∀ (next : Memory w), readings next=(R).toLayout.published raw → (R).toLayout.Room raw w →
      ∃ patch : SparsePatch (w:=w) O (R) raw, patch.built=next ∧ patch.placed=p ∧
        patch.geometry=geometry ∧ patch.extra=extra ∧
      ∀ (data : ℕ → ℕ → Bool) (rows : (i : Fin ((R).before raw (R).cells)) → SparseCell a f r.val.2.2 data i.val),
      (∀ i, (rows i).number.val=globalCell (R).toLayout raw i.val) →
      let field := fun c => (SparseEmission.globalCells (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl)
        (live:=live) (ports:=ports) e rows c).field
      (∀ c < (R).cells, (R).owner raw c=(R).team →
        let logical := SparseExterior.logicalCell (p c) (extra c) (field c)
        (CompactFrame.pack w (Packet.input logical.directory logical.privateWires (field c).bytes)).length≤TeamScales.width length (1/2) ∧
        logical.directory.ProfileWidths ∧ SparseExterior.clock w logical.directory logical.privateWires (field c)≤length^25) →
      ReachedReportCells (n:=length) e patch rows description := by
  obtain ⟨hf,hs,shape,span,pubEnd,orig,supp,merged⟩ := out.signed_merge_table G ptr base slot fs addresses alloc seed r e
    place gp fromControls physical frameEq sorted padded stops tableRoom ranks controls image fitBefore order ordinal
    numeric body widths reportsAt bodiesAt
  refine ⟨hf,hs,?_⟩
  intro raw pl p geometry extra
  refine ⟨shape,?_⟩
  intro next built taskRoom
  let patch : SparsePatch (w:=w) O (R) raw := ⟨next,p,geometry,extra,taskRoom,built,span⟩
  refine ⟨patch,rfl,rfl,rfl,rfl,?_⟩
  intro data rows rowOrder field paid
  let os := SparseEmission.globalCells (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl)
    (live:=live) (ports:=ports) e rows
  have budget := produced_call_windows a (R) raw patch.placed patch.geometry patch.extra os hn hw hW scratch burst
    (fun c hc owned => (paid c hc owned).1)
  exact ⟨rowOrder,rank,pubEnd,fun _ _ => rfl,orig,supp,merged patch rfl rfl rfl,budget,paid⟩

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
