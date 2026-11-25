import OAI.Hierarchy.DescentTerminalBookPublish
import OAI.Hierarchy.DescentTerminalBookRows
import OAI.Hierarchy.DescentTerminalSpanCursor

namespace OAI
/-! # The fixed physical prefix generating terminal allocation and every book row's owner -/
namespace Hierarchy.DescentTerminalRowPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalLocalPortBook DescentTerminalSpanBook
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ}
structure Layout where
  parts : Book.Parts
  books : Bank
  counts : Bank
  countTable : Bank
  boundaries : ℕ
  cursors : Bank
  siteFirst : Bank
  siteLast : Bank
  mark : MarkerBanks
  markedScratch : ℕ
  locate : Cursors

variable (L : Layout) (S n : ℕ)
local notation "pub" => scan w L.books.base S (Book.expression L.parts)
local notation "cnt" => scan w L.counts.base S (countRow L.books L.countTable)
local notation "pos" => DescentTerminalBinPackCheap.program w L.counts.base L.boundaries L.cursors.base S
local notation "heads" => DescentTerminalBinPackCheap.headerProgram w S L.siteFirst.base L.siteLast.base L.cursors L.counts
local notation "marks" => MarkerBanks.program w L.markedScratch n S L.mark
local notation "locs" => L.locate.program w n

def program := (((((pub).seq cnt).seq pos).seq heads).seq marks).seq locs
def time := Book.price L.parts S+(4+28*S)+(4+102*S)+((4+34*S)+(4+22*S))+L.mark.time n S+L.locate.cost n
def printed (m : Memory w) := image L.books.base S (Book.expression L.parts) m
def sized (m : Memory w) := image L.counts.base S (countRow L.books L.countTable) (printed L S m)
def allocated (m : Memory w) := DescentTerminalUniversalWrite.image
  (DescentTerminalBinPackCheap.step w L.counts.base L.boundaries L.cursors.base) L.cursors.base S (sized L S m)
def header (m : Memory w) := DescentTerminalBinPackCheap.headerImage L.siteFirst.base L.siteLast.base L.cursors L.counts (allocated L S m) S
def marked (m : Memory w) := L.mark.result L.markedScratch S n (header L S m)
def result (m : Memory w) := L.locate.final n (marked L S n m)

structure Room (w : ℕ) : Prop where
  book : (Book.expression L.parts).Fits w L.books.base
  bookEnd : L.books.base+S<2^w
  countData : L.books.Fits w L.counts.base
  countROM : L.countTable.Fits w L.counts.base
  countEnd : L.counts.base+S<2^w
  allocation : L.cursors.base+S<2^w
  endData : L.cursors.Fits w L.siteFirst.base
  sizes : L.counts.Fits w L.siteFirst.base
  gap : L.siteFirst.base+S≤L.siteLast.base
  endLast : L.siteLast.base+S<2^w
  marker : L.mark.Room w L.markedScratch n S
  locate : L.locate.Fits w n

private theorem seq_run (P Q : Procedure w) {source middle target : Memory w} {p q : ℕ}
    (left : P.Exec source middle p ∧ CheapCode P) (right : Q.Exec middle target q ∧ CheapCode Q) :
    (P.seq Q).Exec source target (p+q) ∧ CheapCode (P.seq Q) :=
  ⟨@Procedure.Exec.then w P Q source middle target p q left.1 right.1,
    @cheap_seq w P Q left.2 right.2⟩

theorem run (m : Memory w) (room : Room L S n w) (positive : 0<w)
    (static : L.mark.Fixed S (header L S m)) :
    (program (w:=w) L S n).Exec m (result L S n m) (time L S n) ∧ CheapCode (program (w:=w) L S n) := by
  have a : (pub).Exec m (printed L S m) (Book.price L.parts S) ∧ CheapCode (pub) :=
    ⟨@scan_exec w L.books.base S (Book.expression L.parts) m room.book room.bookEnd,
      @scan_cheap w L.books.base S (Book.expression L.parts)⟩
  have b:=scan_cost L.books L.countTable L.counts.base S (printed L S m) room.countData room.countROM room.countEnd
  have c:=DescentTerminalUniversalWrite.safe L.counts.base L.boundaries L.cursors.base (sized L S m) room.allocation
  have d:=DescentTerminalBinPackCheap.header_spec L.siteFirst.base L.siteLast.base L.cursors L.counts
    (allocated L S m) room.endData room.sizes room.gap room.endLast
  have e:=L.mark.any L.markedScratch S n (header L S m) room.marker positive static
  have f:=L.locate.run n (marked L S n m) room.locate
  have ab := seq_run pub cnt a b
  have abc := seq_run ((pub).seq cnt) pos ab c
  have abcd := seq_run (((pub).seq cnt).seq pos) heads abc d
  have abcde := seq_run ((((pub).seq cnt).seq pos).seq heads) marks abcd e
  exact seq_run (((((pub).seq cnt).seq pos).seq heads).seq marks) locs abcde f

theorem tariff : time L S n ≤1024*(S+n+1) := by
  have p := Book.fees L.parts S
  simp only [time,MarkerBanks.time,DescentTerminalHeaderScatter.cost,
    DescentTerminalHeaderScatter.stage,DescentTerminalHeaderScatter.bounded,MarkerBanks.startExpr,
    Cursors.cost,Cursors.covered,Cursors.localOffset,Cursors.site,Cursors.raw,
    DescentTerminalHeaderPrefixRAM.work,Expr.work]
  omega

end
end Hierarchy.DescentTerminalRowPlan

end OAI
