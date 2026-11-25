import OAI.Hierarchy.ProtocolRAMCalendarStripChart
import OAI.Hierarchy.ProtocolRAMCalendarScalarHistory

namespace OAI
/-! # Public ROM of the final paid calendar, with one physical padded port directory -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen StripDirectory StockCommit

variable {z d k q depth : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))

/-- The canonical payload and reserve builders bind the same sampler degree and
depth; they really do share the same candidate and padded port enumeration. -/
def portRows (s : Boards z d k q depth) :=
  PurchaseFrozen.count z d k*PurchaseFrozen.paths z s.sampler.degree depth

def portTable (s : Boards z d k q depth) (base : ℕ) : PortROM.Table 1 :=
  ⟨base,fun _=>portRows s,D,portRows s,fun _=>le_rfl⟩

theorem portTable_linear (s : Boards z d k q depth) (base : ℕ) :
    (portTable s base).stop≤base+(12*((PurchaseFrozen.count z d k*s.sampler.degree^depth)*D)+8)*2^z := by
  have rows : (portTable s base).maxRows≤(PurchaseFrozen.count z d k*s.sampler.degree^depth)*2^z := by
    change PurchaseFrozen.count z d k*(2^z*s.sampler.degree^depth)≤_
    exact (by ac_rfl : PurchaseFrozen.count z d k*(2^z*s.sampler.degree^depth)=_).le
  simpa only [portTable,Nat.one_mul] using (portTable s base).linear z _ rows

/-- Install the concrete price, score, and integral half-bank pointers in both
strip procedures. The directory starts once at the first address after the
global score pages, followed by true scalar price pages. -/
def withPublicROM (s : Boards z d k q depth) (B : JointHeader.Board) (c : Mesh)
    (finish : ℝ) (price : PhasePrice) : Boards z d k q depth :=
  let scores := JointHeader.scores B z N k
  let ports := portTable s (JointHeader.stop B z N k (DeadlineROM.count c))
  let prices := DeadlineROM.table c finish price ports.stop (GlobalTests.kinds N k) scores.stride
  let half := JointHeader.half B z N k
  {s with
    outer := fun p a =>
      let b := s.outer p a
      let x := Attempt.outer p a
      { b with
        repair := {b.repair with halfTable:=half}
        start := ports.base
        price := prices.bank (DeadlineROM.index c x)
        globalTests := DeadlineROM.scorePage c scores z N k x
        half := half }
    inner := fun p a j v =>
      let b := s.inner p a j v
      let x := Attempt.inner p a j v
      { b with
        repair := {b.repair with halfTable:=half}
        start := ports.base
        price := prices.bank (DeadlineROM.index c x)
        globalTests := DeadlineROM.scorePage c scores z N k x
        half := half }}

variable (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

theorem shared_header (s : Boards z d k q depth) (b : JointHeader.Board) (c : Mesh)
    (finish : ℝ) (price : PhasePrice) (a : Attempt) :
    header F (withPublicROM s b c finish price) a =
      (portTable s (JointHeader.stop b z N k (DeadlineROM.count c))).header 0 := by
  cases a <;> simp only [PortROM.Table.header,Fin.val_zero,Nat.zero_mul,Nat.add_zero] <;> rfl

/-- The actual role plan used by the final pinned and stock-recompiled chart. -/
theorem shape_header (s : Boards z d k q depth) (c : Mesh) (arena : Arena) (initial : ℕ) (a : Attempt) :
    let f := formats F c arena initial s a
    f.occurrenceHeader (start s a)=header F s a ∧ f.occurrences=(header F s a).count := by
  cases a <;> exact ⟨rfl,rfl⟩

theorem live_half (s : Boards z d k q depth) (b : JointHeader.Board) (c : Mesh) (arena : Arena)
    (finish : ℝ) (price : PhasePrice) (a : Attempt) :
    ((formats F c arena b.initial (withPublicROM s b c finish price)) a).stockSource.half=
      JointHeader.half b z N k := by cases a <;> rfl

theorem live_board_half (s : Boards z d k q depth) (b : JointHeader.Board) (c : Mesh) (arena : Arena)
    (finish : ℝ) (price : PhasePrice) (a : Attempt) :
    ((formats F c arena b.initial (withPublicROM s b c finish price)) a).board.halfTable=
      JointHeader.half b z N k := by cases a <;> rfl

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
