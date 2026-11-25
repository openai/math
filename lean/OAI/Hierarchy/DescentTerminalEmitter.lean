import OAI.Hierarchy.DescentTerminalShapeData
import OAI.Hierarchy.DescentTerminalDataPlane
import OAI.Hierarchy.DescentTerminalScatterBounded
import OAI.Hierarchy.DescentTerminalLocalPortGather
import OAI.Hierarchy.DescentTerminalRouteIssue
import OAI.Hierarchy.DescentTerminalLeafHeap

namespace OAI
/-! # Single executable terminal prefix and its reached memory on every proposed summand -/
namespace Hierarchy.DescentTerminalEmitter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalHeaderScatter
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}
attribute [local irreducible] Procedure.Exec CheapCode

structure Header where
  tapes : DescentTerminalScatterChip.Layout
  output : Bank
  src : ℕ
  events : ℕ
  count : ℕ
  sink : ℕ
  shift : ℕ
  blank : ℕ

namespace Header
variable (h : Header)
def program (w : ℕ) := DescentTerminalScatterChip.boundedProgram h.tapes h.output w h.src h.events h.count h.sink h.shift h.blank
def time := DescentTerminalScatterChip.boundedCost h.tapes h.output h.events h.count h.sink h.shift
def final (m : Memory w) := DescentTerminalScatterChip.heap h.tapes h.output h.src h.events h.count h.sink h.shift h.blank m
structure Room (w : ℕ) : Prop where
  dst : h.output.Fits w h.src
  early : h.tapes.lane.Fits w h.output.base
  compiled : (stage (DescentTerminalScatterChip.put h.tapes h.output h.sink)
    (DescentTerminalScatterChip.datum h.tapes h.shift) h.tapes.lane).Fits w h.src
  count : h.count≤h.output.size
  address : h.src+2*h.events<2^w
def Literal (m : Memory w) := ∀(i:Fin h.events) (j:Fin 2),h.tapes.lane.read m ((field i j).val:Word w)=(j.val:Word w)
theorem run (r : Room h w) (pos : 0<w) (m : Memory w) (lit : Literal h m) :
    (program h w).Exec m (final h m) (time h) ∧ CheapCode (program h w) :=
  DescentTerminalScatterChip.any h.tapes h.output h.src h.events h.count h.sink h.shift h.blank m
    r.dst r.early r.compiled r.count r.address pos lit
end Header



structure Layout where
  plane : DescentTerminalDataPlane.Layout
  exteriorWidths : DescentTerminalDenseHeaderRAM.Layout
  indices : Header
  formats : Header
  book : DescentTerminalLocalPortBook.Gather
  route : DescentTerminalRouteIssue.Layout
  leaf : DescentTerminalLeafFold.Layout
  scratch : ℕ
  scalar : ℕ

variable (S : Shape) (L : Layout)
local notation "P" => DescentTerminalDataPlane.program (w:=w) S.plane L.plane
local notation "E" => DescentTerminalDenseHeaderRAM.program w S.plane.headerRows L.exteriorWidths
local notation "I" => L.indices.program w
local notation "F" => L.formats.program w
local notation "G" => L.book.program w S.rows
local notation "R" => DescentTerminalRouteIssue.program L.route w S.rows
local notation "B" => DescentTerminalLeafFold.program w L.scratch S.pool S.leaves L.scalar L.leaf

def program := ((((((P).seq E).seq I).seq F).seq G).seq R).seq B
def time := DescentTerminalDataPlane.time S.plane L.plane + DescentTerminalDenseHeaderRAM.cost S.plane.headerRows L.exteriorWidths +
  L.indices.time+L.formats.time+(4+S.rows*(2*L.book.load.work+4))+DescentTerminalRouteIssue.clocks L.route S.rows+
  DescentTerminalLeafFold.work L.leaf S.pool S.leaves

def external (m : Memory w) := DescentTerminalDenseHeaderRAM.finalMem L.exteriorWidths S.plane.headerRows
  (DescentTerminalDataPlane.finalMem S.plane L.plane m)
def indexed (m : Memory w) := L.indices.final (external S L m)
def formatted (m : Memory w) := L.formats.final (indexed S L m)
def named (m : Memory w) := L.book.output S.rows (formatted S L m)
def routed (m : Memory w) := DescentTerminalRouteIssue.finalMem L.route S.rows (named S L m)
def result (m : Memory w) := DescentTerminalLeafFold.final L.leaf (routed S L m) S.pool S.leaves L.scratch L.scalar

structure Room (w : ℕ) : Prop where
  plane : DescentTerminalDataPlane.Room S.plane L.plane w
  ext : DescentTerminalDenseHeaderRAM.Fits L.exteriorWidths w S.plane.headerRows
  idx : L.indices.Room w
  fmt : L.formats.Room w
  doc : L.book.load.Fits w L.book.names.base
  endNames : L.book.names.base+S.rows<2^w
  gate : DescentTerminalRouteIssue.Fits L.route w S.rows
  leaf : L.leaf.cells.Fits w L.scratch
  leafSize : S.pool+1≤L.leaf.cells.size
  before : L.leaf.lanes.Fits w L.leaf.cells.base
  fields : (DescentTerminalLeafFold.row L.leaf).Fits w L.scratch
  scalar : (DescentTerminalLeafFold.lookup L.leaf).Fits w L.scalar
  endLeaf : L.scratch+2*S.leaves<2^w
  endScalar : L.scalar+S.pool<2^w

/-- Read-only constants are needed even for malformed selector tapes. The
other inputs to these seven procedures can be arbitrary words. -/
structure Static (m : Memory w) : Prop where
  firstLane : L.indices.Literal (external S L m)
  secondLane : L.formats.Literal (indexed S L m)
  lastLane : ∀(i : Fin S.leaves) (j:Fin 2),L.leaf.lanes.read (routed S L m) ((field i j).val:Word w)=(j.val:Word w)

theorem run (m : Memory w) (positive : 0<w) (room : Room S L w) (literal : Static S L m) :
    (program (w:=w) S L).Exec m (result S L m) (time S L) ∧ CheapCode (program (w:=w) S L) := by
  have p:=DescentTerminalDataPlane.exec_all S.plane L.plane room.plane m
  have e:=DescentTerminalDenseHeaderRAM.exec_any L.exteriorWidths (DescentTerminalDataPlane.finalMem S.plane L.plane m) room.ext
  have i:=L.indices.run room.idx positive (external S L m) literal.firstLane
  have f:=L.formats.run room.fmt positive (indexed S L m) literal.secondLane
  have g:=L.book.run S.rows (formatted S L m) room.doc room.endNames
  have r:=DescentTerminalRouteIssue.run L.route room.gate (named S L m)
  have b:=DescentTerminalLeafFold.any L.leaf (routed S L m) L.scratch L.scalar S.pool S.leaves positive room.leaf
    room.leafSize room.before room.fields room.scalar room.endLeaf room.endScalar literal.lastLane
  unfold program time result
  exact exec_cheap_seq (exec_cheap_seq (exec_cheap_seq (exec_cheap_seq (exec_cheap_seq
    (exec_cheap_seq p e) i) f) g) r) b

end
end Hierarchy.DescentTerminalEmitter

end OAI
