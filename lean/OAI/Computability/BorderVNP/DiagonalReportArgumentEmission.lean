import OAI.Computability.BorderVNP.DiagonalPublishedReportArgument
import OAI.Computability.BorderVNP.FiniteEvaluatorReturnedTerminalOperands

/-! # The physical arrays and paid calls of one issued sparse emission -/

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
    {rl : ReportLayout} (reports : List (ReportCell rl)) (q : ReportCursor)
    (r : Returns prepareCellReports pub mac s m) {team live ports : ℕ}
set_option quotPrecheck false
local notation "head" => readings pub 0
local notation "mem" => readings r.val.2.2
local notation "f" => FragmentRows.Layout.fromFrame head mem
local notation "R" => a.controlRows team head offsets ctl live ports
local notation "top" => descriptorBank (ctl+37) p
local notation "pubRoom" => a.cube.cells+1+G.words.length+(a.cube.cells+1)≤2^p
local notation "descRoom" => a.cube.cells+1+(Schema.coords (G.referenceRows ptr).length).length+(a.cube.cells+1)≤2^d


/-- The emitted count and row order, original delivered boxes and interpreted
sparse rows of an actual pre-argument report. The bounds cover every owned
cell in every valid realization of the two published directories. -/
def ReportArgumentEmission {fit : (f).Fits w mem} {cc : a.fragments.cells=(f).cells}
    (e : SparseEmission a f r.val.2.2 fit cc) : Prop :=
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
                SparseExterior.clock w logical.directory logical.privateWires (fields c).field≤length^25

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
