import OAI.Computability.BorderVNP.DiagonalPhysicalClaimFinish
import OAI.Computability.BorderVNP.DiagonalReturnedFinishWindow
import OAI.Computability.BorderVNP.DiagonalTallyGadgetOperands
import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderRoom

/-! # A returning team's signed finish from its own received packet and reports -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks RoutingISA.Evaluator FiniteEvaluator
open TeamContraction TeamContraction.JointHeader TeamContraction.JointHeader.PositiveFields TeamContraction.ProcessorSlots
open Evaluator.ScheduleClock
open DiagonalTallyAllocation DiagonalTallyCellReports DiagonalTallyMaterialize DiagonalTallyRAM

variable {w reserve axes groups cap width : ℕ} (l : Layout) (A : StartupArena)
    (p : PositiveFields reserve axes groups cap l.cube.teams l.dim width)
    (pub : Arg → Word w) (owner : Fin l.cube.header.d → ℕ) (team : Fin l.cube.teams) (demand : ℕ)
    (data : Data l.cube.n l.cube.header.d l.cube.header.blocks l.cube.b l.cube.h l.cube.K l.cube.s)
    {banks : CellBanks.Layout} {rf : ReportLayout} (cs : List (ReportCell rf)) (q : ReportCursor)
    (allocation : ReportAllocation l.before l.after banks rf cs q)
    (mac : TeamOpcode.Macros w 8) (state : Bank w) (mem : Memory w)
local notation3 (prettyPrint := false) "X" => gadgetLookup l pub owner team.val demand data
local notation3 (prettyPrint := false) "raw" => rawAddress A reserve axes groups cap
local notation3 (prettyPrint := false) "suffix" => l.after.suffixFrame (cellOperands cs q).length (X).frame.count rf.zeroAddr rf.parameters
local notation3 (prettyPrint := false) "os" => cellOperands cs q++(suffix).packetOperands rf.frame (l.cube.stop+1)
  (fun i => l.id (((X).visits i).entry demand))
local notation3 (prettyPrint := false) "ar" => l.after.arenaFor (os).length raw l.dim l.cube.teams team.val width
local notation3 (prettyPrint := false) "claims" => fun (i : Fin l.cube.teams) (c : Fin l.dim) =>
  (claimWord (w:=w) (ar).frame p.tallyWords i.val c.val).val

include allocation

/-- On every locally accepting finish, the actual cube table and owned report
arrays first write their complete operand list. These operands and the checked
public header produce a local receipt, fixed output location and measured
write cost before the truth of any other team's private checks is known. -/
theorem localPacketFinish
    (bankStart : banks.bankStart=l.cube.cellBank) (bankCount : banks.cells=l.cube.cells)
    (bankStride : banks.stride=l.cube.cellStride) (zeroAddr : rf.zeroAddr=l.cube.stop)
    (frame : rf.frame=(pub 0).val) (parameter : rf.parameters=l.p.parameters)
    (frameAddr : (pub 0).val=A.frame) (gadget : rf.gadgets=l.p.report.gadgets)
    (header : HeaderSeed l p pub raw team.val mem) (packet : CubePacket.WordPrepared X l.id pub mem)
    (report : supplied mem (cellEnd cs q) q.descriptors (cellOperands cs q))
    (prior : (mem (rf.frame+35)).val=(cellOperands cs q).length)
    (vertices : (X).frame.count≤l.p.report.vertices)
    (digits : argumentWidth l.cube.n l.cube.b l.cube.h l.cube.K l.cube.s≤l.p.report.cubeWidth)
    (idCap : ∀ i, l.id (((X).visits i).entry demand)<rf.gadgets)
    (headerWidth : A.header=PositiveFields.width reserve axes groups cap l.cube.teams l.dim width)
    (placed : A.next≤l.cube.header.header) {u v k : ℕ} (endFit : l.endAddress w u v k<2^w)
    (teamsFit : l.cube.teams<2^w) (widthFit : width≤w) (wpos : 0<w)
    (z : Returns (finishExpansion signedOccurrences) pub mac state mem) :
    ∃ receipt : FinishInput team claims width pub mac state mem p.tallyWords,
      receipt.post=l.after ∧ receipt.raw=raw ∧ receipt.operands=os ∧
      (∀ k < l.after.start, k≠(pub 0).val+35 → receipt.selected k=mem k) ∧
      traceCost receipt.earlier ≤ selectedOperandsTicks (X).frame.count (X).frame.width ∧
      ∀ pubWords powers units, cs.length*(rf.gadgets+rf.gadgets*rf.countWidth) ≤ pubWords →
        teamWeighted cs ≤ powers → 1 ≤ units →
        (X).frame.count ≤ TeamRowClock.physicalCoefficient l.cube.n l.cube.b l.cube.h l.cube.K l.cube.s * units →
        traceCost z.val.1 ≤ cubeCoefficient l.cube.n l.cube.b l.cube.h l.cube.K l.cube.s (X).frame.width*units +
          64*(pubWords+powers+TeamRowClock.physicalCoefficient l.cube.n l.cube.b l.cube.h l.cube.K l.cube.s*units)+
          512*(l.cube.teams+1)*(l.dim+1)*(w+1) := by
  obtain ⟨frameFit,rawLo,rawHi,room,dimFit,localFit,_⟩ := finishSeedRoom l A headerWidth placed endFit
  rw [←frameAddr] at frameFit rawLo
  have fresh : l.after.fresh<2^w := (Nat.le_add_right l.after.fresh (2*l.after.bound.operands)).trans_lt localFit
  obtain ⟨es,s,mt,prepare,cost,_,source,count,fit,sep,kept⟩ :=
    gadgetOperands l pub owner team.val demand data allocation bankStart bankCount bankStride zeroAddr frame.symm
      mac state mem packet report prior (frame ▸ header.seed.words.1) (by rw [frame,parameter]; exact header.parameters)
      vertices digits (frame ▸ frameFit) fresh idCap (by rw [parameter,gadget]; exact dimFit.le)
  obtain ⟨r,post,base,ops,trace,stored⟩ := localFinishOfReturn team l.after pub mac state s mem mt es os p.tallyWords
    prepare header.seed (frame ▸ kept) frameFit rawLo rawHi room teamsFit widthFit wpos source (frame ▸ count)
    fit (frame ▸ sep) header.subtotal p.tallyWords_length p.tallyWords_width z
  refine ⟨r,post,base,ops,?_,trace ▸ cost,?_⟩
  · simpa only [stored,frame] using kept
  · intro pubWords powers units countFields weighted nonempty visited
    exact r.returned_phase cs q _ ops (fun _ => rfl) (trace ▸ cost) countFields weighted widthFit nonempty visited z

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
