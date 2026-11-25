import OAI.Computability.BorderVNP.DiagonalReportArgumentEmission
import OAI.Computability.BorderVNP.DiagonalIssuedCandidateGeometry
import OAI.Computability.BorderVNP.DiagonalPrefixFinishCalibration

/-! # Constructing the private argument from the issued report and sparse emission -/

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


/-- The original packet, observed fragment directory and funded rows on each
real emission produce the private argument input for this sampled report. -/
theorem Published.argument_on_issued_report {args : E → ℕ}
    (out : Published G p d (ctl+37) H ptr args base) (addresses : ∀ i,args (ptr i)=slot i)
    (seed : PreparedReportInput pub m reports q description) (allocation : ReportAllocation a.before a.after banks rl reports q)
    (physical : banks.bankStart=a.cube.cellBank) {source : ℕ → ℕ}
    (issued : SignedPrep.IssuedGeometry a team head offsets ctl live ports w base source (readings m) mem)
    (fr : FragmentDirectoryInput pub r.val.2.2) (rowBound : fr.layout.count≤a.cube.maxRows)
    (cellCount : a.fragments.cells=fr.layout.cells) (cables : fr.layout.host.count=a.cube.cables)
    (layout : SparseGeometry a fr.layout offsets ctl) {u v k : ℕ} (limit : a.endAddress w u v k<2^w)
    (rank : (R).sorted=top ∧ (R).padded=2^d ∧ (R).stops=a.cube.cells+1+(Schema.coords (G.referenceRows ptr).length).length ∧
      top+2*(2^d)≤a.cube.header.header ∧ (∀ j : Fin (2^d), base (top+(2^d+j.val))<2^d) ∧
      DescriptorRanks (a.cube.cells+1) (R).stops d (R).sorted base)
    (room : (R).Room w)
    (originals : ∀ i,(a.cube.cellBank ≤ slot i ∧ slot i+description≤a.cube.stop) ∧
      H+(boxBody (fs i)).length≤description ∧ (boxBody (fs i)).length<2^H)
    (reportsAt : ∀ c : Fin a.cube.cells, ∃ b, G.reports c.castSucc=countFields b a.before.bound.gadgets a.before.bound.countWidth)
    (hn : 1≤length) (hw : 0<w) (hW : w≤length)
    (scratch : scratchWindow length≤a.p.scratchStride) (burst : burstWindow length≤a.p.burstStride)
    (actual : ∀ (e : SparseEmission a f r.val.2.2 (fr.loaded ▸ fr.fit) (fr.loaded ▸ cellCount))
      (first : Returns emitBucket pub mac r.val.2.1 r.val.2.2), e.bank=first.val.2.1 → e.output=first.val.2.2 →
      ReportArgumentEmission (a:=a) (p:=p) (d:=d) (H:=H) (length:=length) (description:=description) (ctl:=ctl)
        (offsets:=offsets) (team:=team) (live:=live) (ports:=ports) G ptr base slot fs reports q r e) :
    Nonempty (SignedPrep.ArgumentInput pub mac r.val.2.1 r.val.2.2) := by
  obtain ⟨sorted,padded,stops,table,ranks,ordered⟩ := rank
  rw [fr.loaded] at rowBound cellCount cables layout
  exact out.owned_report_argument_input G ptr base slot fs r addresses allocation seed (fr.loaded ▸ fr.fit)
    issued.pointer issued.controls issued.placement layout cables rowBound cellCount.symm limit issued.fields
    issued.wordWidth issued.callLimit issued.tasks issued.geometry issued.body physical seed.framePointer.symm
    sorted padded stops table ranks ordered room issued.grouped (a.finish_word_room limit).2.2.2
    (fun j => (originals j).1) (fun j => (originals j).2.1) (fun j => (originals j).2.2) reportsAt hn hw hW
    scratch burst actual

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
