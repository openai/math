import OAI.Hierarchy.HistorySelectedLeafPacket
import OAI.Hierarchy.TraceReceiverSeedBudget

namespace OAI
/-! # Charging seed rows and locating their disjoint result banks -/

namespace Hierarchy.HistorySelectedSeed
open ThreeFlat Diagonal.TickWorkspace Diagonal.HistoryContraction Diagonal.PhysicalStage
open RAM RAM.HistoryInitialSeed RAM.HistoryStageBody.Physical RAM.NavigationNodeRows
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {F : Type} [Field F] {W u p : ℕ}

omit [Field F] in
/-- Project the work and pair counts of a true initial archive record onto the
three prices used by the native leaf program. -/
theorem paid (tree : Tree F p) (z : Site) (shape : TraceBucketAtom.Layout) (b : Banks)
    (mem : ℕ→ℕ) (work : ℕ) (unit : 0<b.unitWork)
    (read : archiveColumn b mem z.index 0=b.unitWork*work)
    (alive : 1≤work) (treePaid : tree.resources≤work) (ports : p≤2*work)
    (arity : p=z.extPins+2*shape.bank) (cells : tree.compile.cells=z.rows (initial u shape)) :
    1≤archiveColumn b mem z.index 0/b.unitWork ∧
    z.rows (initial u shape)≤archiveColumn b mem z.index 0/b.unitWork ∧
    z.extPins≤2*(archiveColumn b mem z.index 0/b.unitWork) := by
  rw [read,Nat.mul_div_cancel_left _ unit]
  have rows : tree.rows≤tree.resources := by unfold Tree.resources Stage.treeWork; omega
  rw [Tree.compiled_rows] at cells
  exact ⟨alive, cells ▸ rows.trans treePaid,by omega⟩

/-- Once the charged tree and external pin counts fit one per-node reservation,
the numerical addresses of all six results and the selected interval are in
the receiver chart. These bounds hold at arbitrary RAM word widths. -/
theorem physicalBounds (shape : TraceBucketAtom.Layout) (z : Site)
    (order : 2≤volume u) (scratch : volume u+42≤ stride u)
    (endWord : base u 19<2^W)
    (rows : 4*z.rows (initial u shape)≤volume u) (ext : z.extPins≤volume u)
    (arity : z.extPins+2*shape.bank<2^W) (hidden : z.bits (initial u shape)<2^W)
    (stream : base u 12+(z.index+1)*(volume u)^2≤base u 13)
    (results : base u 13+8*z.index+8≤base u 14)
    (bins : 4*z.lane+4≤ stride u) :
    let A:=initial u shape
    Separated A z ∧ A.ctrl+42<2^W ∧ 4<2^W ∧
    (∀ j:Fin 6,z.words A ⟨36+j.val,by omega⟩<2^W) ∧
    A.intervals+4*z.lane+3<2^W ∧ ¬z.writes A (A.intervals+4*z.lane+3) := by
  let A:=initial u shape
  have s5:=apart (u:=u) (by decide:5<12)
  have s12:=apart (u:=u) (by decide:12<13)
  have s13:=apart (u:=u) (by decide:13<14)
  have s14:=apart (u:=u) (by decide:14<19)
  have stridePos : 0< stride u := by unfold stride; positivity
  let V:=volume u
  have alloc : 2*V≤V*V := Nat.mul_le_mul_right _ order
  have upto : z.stream A+V*V≤base u 13 := by
    change base u 12+z.index*(V*V)+V*V≤base u 13
    simpa only [Nat.add_mul,Nat.one_mul,pow_two,Nat.add_assoc] using stream
  have endNode : z.resultBase A+6≤A.ctrl := by
    change base u 13+8*z.index+6≤base u 14+volume u
    omega
  have endPair : z.extBase A+z.extPins≤z.resultBase A := by
    change z.stream A+V+z.extPins≤base u 13+8*z.index
    change z.extPins≤V at ext
    omega
  have sep : Separated A z :=
    ⟨Nat.add_le_add_left rows _, endPair,endNode⟩
  have ctrlWord : A.ctrl+42<2^W := by change base u 14+volume u+42<_;omega
  have sw : z.stream A<2^W := by omega
  have ew : z.extBase A<2^W := by
    change z.stream A+V<2^W
    omega
  have vw : volume u<2^W := by omega
  have rowsWord : z.rows A<2^W := by
    change z.rows (initial u shape) < 2^W
    omega
  have extWord : z.extPins<2^W := by omega
  have binLow : A.intervals+4*z.lane+3<base u 12 := by change base u 5+4*z.lane+3<_;omega
  have lo (x : ℕ) (hx : x<base u 12) : ¬z.writes A x := by
    have rowLo : base u 12≤z.stream A := Nat.le_add_right _ _
    have pinLo : z.stream A≤z.extBase A := Nat.le_add_right _ _
    have resultLo : base u 13≤z.resultBase A := Nat.le_add_right _ _
    have ctrlLo : base u 14≤A.ctrl := Nat.le_add_right _ _
    unfold Site.writes
    omega
  have binWord := binLow.trans (show base u 12 < 2^W by omega)
  refine ⟨sep,ctrlWord,by omega,?_,binWord,lo _ binLow⟩
  intro j
  fin_cases j <;> first | exact sw | exact arity | exact rowsWord | exact hidden | exact ew | exact extWord

end Hierarchy.HistorySelectedSeed

end OAI
