import OAI.Hierarchy.DescentTerminalPriorArena
import OAI.Hierarchy.DescentTerminalCohortRun
import OAI.Hierarchy.DescentTerminalWeightShelf
import OAI.Hierarchy.DescentTerminalBookNative
import OAI.Hierarchy.DescentTerminalCableWidthMachine
import OAI.Hierarchy.DescentTerminalSiteControlBanks
import OAI.Hierarchy.DescentTerminalNativeHeaderField

namespace OAI
/-! # Consecutive physical memory for terminal preprocessing before the fixed private meter -/
namespace Hierarchy.DescentTerminalPreflightSpace
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalPrimitiveArena DescentTerminalRowArena
open DescentTerminalLocalPortBook DescentTerminalGrainProfiles DescentSIMDLookup
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
/-- Public capacities and immutable ABI widths. All new addresses are generated below. -/
structure Spec where
  scalar : Shape
  frozenBits : ℕ
  cohortBits : ℕ
  cohorts : ℕ
  groups : ℕ
  paidLanes : ℕ
  actorLanes : ℕ
  paidBits : ℕ
  externalBits : ℕ
  vertices : ℕ
  «arguments» : ℕ
  binSize : ℕ
  pageBits : ℕ
  degree : ℕ
  cap : ℕ
  signedLanes : ℕ
  cableCellBits : ℕ
  grainsPerCable : ℕ
  signedPositive : 0<signedLanes
  printBits : ℕ
  publicGrains : ℕ
  headerRows : ℕ
  paidRows : ℕ

namespace Spec
variable (x:Spec) (base:ℕ)
def cohortEnd := DescentTerminalCohortArena.stop base x.frozenBits x.cohortBits x.cohorts x.scalar.shops
def census : Bank := ⟨(DescentTerminalCohortArena.order base x.frozenBits x.cohortBits x.cohorts x.scalar.shops).counts,
  Nat.clog 2 x.scalar.shops⟩
def population := DescentTerminalPriorArena.pop x.scalar x.groups x.paidLanes x.paidBits x.externalBits (x.cohortEnd base)
def actors := DescentTerminalPriorArena.actor x.scalar x.groups x.paidLanes x.actorLanes x.paidBits x.externalBits 1 (x.cohortEnd base)
def primitive := DescentTerminalPriorArena.start x.scalar x.groups x.paidLanes x.actorLanes x.paidBits x.externalBits 1 (x.cohortEnd base)
def channels := x.scalar.channels (x.primitive base) (x.population base) (x.scalar.subrow (x.actors base))
def weights := x.scalar.finish (x.primitive base)
def bookBegin := Book.WeightShelf.finish x.vertices x.arguments (x.weights base)
def strips := x.degree+x.scalar.blocks*(2+2*x.cap)
def book (args:Fin x.strips→Expr) : Print.Layout x.strips :=
  ⟨x.bookBegin base,x.scalar.shops,x.printBits,args⟩
def bookEnd := (x.book base (fun _=>.row)).stop
def parts := (x.book base (fun _=>.row)).parts (Book.WeightShelf.banks x.vertices x.arguments (x.weights base))
def controls := DescentTerminalControlProgram.layout (x.bookEnd base) x.scalar.shops 4 x.vertices
  (x.vertices*x.arguments) x.arguments (Book.tokenBits (x.vertices*x.arguments)) x.vertices x.binSize x.pageBits
def directory := DescentTerminalControlProgram.earlyBanks (x.controls base) (x.parts base)
def sockets (peer:Bank) : Counter.Sockets := ⟨(x.controls base).finish,peer⟩
def cables (peer:Bank) (old:Fin x.scalar.blocks→Fin (2*x.cap)→Bank) :
    Counter.Rack x.scalar.blocks x.cap x.groups x.signedLanes :=
  ⟨x.sockets base peer,x.scalar.shops,x.degree,x.cableCellBits,x.grainsPerCable,x.headerRows,old,x.signedPositive⟩
def cableEnd := (x.cables base ⟨0,0⟩ (fun _ _=>⟨0,0⟩)).printer.stop
def publicWidths : DescentTerminalPublicWidthTape.Shape :=
  ⟨x.cableEnd base,2^x.cohortBits,x.scalar.shops,x.headerRows,x.publicGrains,x.census base⟩
def literalBase := (x.publicWidths base).widthLayout.stop
def draftBase := x.literalBase base+4*DescentTerminalHeaderDraft.span x.paidRows
/-- The draft never sorts packets. Its ten cash-register and cursor buffers have exactly
the attained site and paid-row counts, with no repeat reservation for packet sorting. -/
def draft (total modulo homes:Bank) (boundaries:ℕ) : Arena :=
  .make (x.draftBase base) x.scalar.shops x.paidRows 0 (x.parts base) total boundaries modulo homes
def maskBase := DescentTerminalHeaderDraft.stop (x.draft base ⟨0,0⟩ ⟨0,0⟩ ⟨0,0⟩ 0)
def eventInputs (peer:Bank) (old:Fin x.scalar.blocks→Fin (2*x.cap)→Bank) : DescentTerminalHeaderSockets.Layout :=
  ⟨peer,(x.publicWidths base).widthLayout.prefix,(x.cables base peer old).printer.prefix⟩

/-- Neither the address calendar nor its high-water mark inspects field coefficients or
selector values. The three layout expressions below have the same numerical endpoints
for every concrete source row reference. -/
theorem book_end (args:Fin x.strips→Expr) : (x.book base args).stop=x.bookEnd base := rfl
theorem cable_end (peer:Bank) (old:Fin x.scalar.blocks→Fin (2*x.cap)→Bank) :
    (x.cables base peer old).printer.stop=x.cableEnd base := rfl
theorem draft_end (t u v:Bank) (b:ℕ) : DescentTerminalHeaderDraft.stop (x.draft base t u v b)=x.maskBase base := rfl

theorem cohort_le : base≤x.cohortEnd base := by
  change base≤base+_+_+_+_+1+_+_+_+4*x.cohorts+x.scalar.shops+1
  simp only [Nat.add_assoc, Nat.le_add_right]
theorem layers :
    x.cohortEnd base≤x.primitive base ∧ x.primitive base≤x.weights base ∧ x.weights base≤x.bookBegin base ∧
    x.bookBegin base≤x.bookEnd base ∧ x.bookEnd base≤(x.controls base).finish ∧
    (x.controls base).finish≤x.cableEnd base ∧ x.cableEnd base≤x.literalBase base ∧
    x.literalBase base≤x.draftBase base ∧ x.draftBase base≤x.maskBase base := by
  refine ⟨?_,?_,Nat.le_add_right ..,Nat.le_add_right ..,?_,?_,?_,Nat.le_add_right ..,?_⟩
  · unfold primitive DescentTerminalPriorArena.start DescentTerminalPriorArena.actor DescentTerminalPriorArena.actStart
      DescentTerminalPriorArena.pop;omega
  · rw [weights,Shape.exact_end];omega
  · change x.bookEnd base≤x.bookEnd base+_+_+_+_;omega
  · let t:=x.cables base ⟨0,0⟩ (fun _ _=>⟨0,0⟩)
    obtain ⟨lower,rBase,high,last⟩:=t.gaps
    have mid:t.slab≤t.printer.origin:=by change t.slab≤t.slab+_+_;omega
    exact lower.trans (rBase.trans (mid.trans last))
  · change x.cableEnd base≤x.cableEnd base+_+_+_+_+_+1+x.scalar.shops+x.scalar.shops
    omega
  · change x.draftBase base≤x.draftBase base+22*_+3*_;omega

theorem census_end : (x.census base).base+(x.census base).size≤x.cohortEnd base := by
  change base+_+_+2^Nat.clog 2 x.scalar.shops≤base+_+_+2^Nat.clog 2 x.scalar.shops+x.scalar.shops+1+_+_+_+4*x.cohorts+x.scalar.shops+1
  simpa only [Nat.add_assoc] using Nat.le_add_right (base+_+_+2^Nat.clog 2 x.scalar.shops) _

/-- The original frozen counts and all previously published primitive fields precede the
genuine scalar book. Underlying low memory is shared, with addresses unchanged. -/
theorem prior : x.scalar.Prior (x.primitive base) (x.population base) (x.scalar.subrow (x.actors base)) :=
  DescentTerminalPriorArena.prior ..
theorem channel_end (b:Fin x.scalar.blocks) (f:Fin 8) :
    ((x.channels base).primitive b f).base+((x.channels base).primitive b f).size≤x.weights base :=
  x.scalar.live_end _ _ _ (x.prior base) b f

theorem book_banks (j:Fin 6) :
    ((x.parts base j).source.base+((x.parts base j).source).size≤x.bookEnd base) ∧
    ((x.parts base j).weights.base+((x.parts base j).weights).size≤x.bookBegin base) := by
  let P:=x.book base (fun _=>.row)
  constructor
  · have here:=P.end_bank j.val
    have up:=Nat.mul_le_mul_right P.band (show j.val+1≤6 by omega)
    change (P.bank j.val).base+P.padH≤P.origin 6
    rw [here];exact Nat.add_le_add_left up _
  · have e:=Book.WeightShelf.at_next x.vertices x.arguments j
    have cap:=Book.WeightShelf.offset_end x.vertices x.arguments (j.val+1)
    change x.weights base+Book.WeightShelf.offset x.vertices x.arguments j.val+_≤
      x.weights base+Book.WeightShelf.words x.vertices x.arguments
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left (e.ge.trans cap) _

end Spec
end
end Hierarchy.DescentTerminalPreflightSpace

end OAI
