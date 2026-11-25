import OAI.Hierarchy.DescentOrdinaryFinalLaw
import OAI.Hierarchy.DescentPreviousOperandLayout
import OAI.Hierarchy.DescentOperandInputCast
import OAI.Hierarchy.DescentOperandFamilyBook
import OAI.Hierarchy.DescentPackedColumnBatch

namespace OAI
/-! # Native ordinary-date publication of seven persistent operand pages -/
namespace Hierarchy.DescentOrdinaryFinal.Chart
open DescentSIMDLookup DescentPackedZip DescentOperandStateBanks ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (B : DescentOrdinaryFinal.Chart)
def widths : Fin 4→ℕ:=![B.roleBits*B.layout.nodes,B.arityBits*B.layout.nodes,
  B.field*B.layout.nodes,(B.layout.size+4)*5]
theorem widths_le (i : Fin 4) : B.widths i≤B.scalarWidth:=by
  fin_cases i <;> simp [widths,scalarWidth]
def kind (i : Fin B.inputs) : Fin 4 :=
  (B.columns.symm i).elim (fun j=>j.castLE (by decide)) (fun _=>3)

/-- Numeric physical addresses issued before this pass. The three
source pages are role, flattened arity, and the requested original span component. -/
structure Sources where
  keysFloor : ℕ
  spanFloor : ℕ
  «meta» : Fin 2→Fin B.layout.blocks→Bank

def sourceBank (s : B.Sources) (p : Fin B.outputs) (x : Fin B.layout.blocks) (i : Fin B.inputs) : Bank :=
  (B.columns.symm i).elim (fun field=>if small:field.val<2 then s.meta ⟨field.val,small⟩ x
     else DescentDatedPriorOperand.previousBank B.layout s.spanFloor x p)
    (fun k=>
      let job:=B.layout.index (x,B.slots.symm k)
      ⟨B.layout.output (B.layout.slot s.keysFloor job.val),Nat.clog 2 (B.rows+1)⟩)

def raw (s : B.Sources) (p : Fin B.outputs) (x : Fin B.layout.blocks) (i : Fin B.inputs) : Expr :=
  .lookup (B.sourceBank s p x i) .row

def castCode (floor w : ℕ) := DescentOperandInputCast.program B.widths B.scalarWidth B.scalarWidth B.layout.lanes floor w
def castImage {w} (floor : ℕ) (m : Memory w) := DescentOperandInputCast.image B.widths B.scalarWidth B.scalarWidth B.layout.lanes floor m
def castArg (s : B.Sources) (floor : ℕ) (p : Fin B.outputs) (x : Fin B.layout.blocks) (i : Fin B.inputs) :=
  DescentOperandInputCast.expr B.widths B.scalarWidth B.scalarWidth B.layout.lanes floor (B.kind i) (B.raw s p x i)
def lawCode (floor w : ℕ) :=DescentOperandFamilyBook.program B.law B.layout.lanes (B.castEnd floor) w
def mounted {w} (floor : ℕ) (m : Memory w) :=DescentOperandFamilyBook.image B.law B.layout.lanes
  (B.castEnd floor) (B.castImage floor m)
def address := (finProdFinEquiv : Fin B.outputs×Fin B.layout.blocks ≃ Fin B.passes)
def expr (s : B.Sources) (floor z : ℕ) : Expr :=
  if h:z<B.passes then
    let j:=B.address.symm ⟨z,h⟩
    DescentOperandFamilyBook.expr B.law B.layout.lanes (B.castEnd floor) j.1 (B.castArg s floor j.1 j.2)
  else .lit 0
def scans (s : B.Sources) (floor : ℕ) :=
  DescentPackedFlowBatch.passes (B.out floor) B.rows B.rows (B.expr s floor) 0 B.passes
def program (s : B.Sources) (floor w : ℕ) :=
  ((B.castCode floor w).seq (B.lawCode floor w)).seq (ProtocolRAM.program w (B.scans s floor))
def image {w} (s : B.Sources) (floor : ℕ) (m : Memory w) :=
  ProtocolRAM.result (B.scans s floor) (B.mounted floor m)
def ticks (s : B.Sources) (floor : ℕ) :=
  ((4+10*B.castWords)+(4+10*B.tableWords))+ProtocolRAM.clock (B.scans s floor)

def Early (s : B.Sources) (floor w : ℕ) :=
  ∀p x i,(B.sourceBank s p x i).Fits w floor ∧ B.rows≤(B.sourceBank s p x i).size

theorem arg_fits {w} (s : B.Sources) (floor : ℕ) (m : Memory w) (p x i)
    (early : B.Early s floor w) (room : B.endAddress floor<2^w) :
    (B.castArg s floor p x i).Fits w (B.castEnd floor):=by
  have out:=B.order floor
  have castRoom : B.castEnd floor<2^w:=lt_of_le_of_lt
    (out.2.1.trans ((Nat.le_add_right ..).trans out.2.2)) room
  have rawFit : (B.raw s p x i).Fits w floor:=⟨(early p x i).1,trivial⟩
  exact (DescentOperandInputCast.issued (H:=0) (G:=0) B.widths B.scalarWidth B.scalarWidth
    B.layout.lanes floor (B.kind i) (B.raw s p x i) m (fun h=>Fin.elim0 h) B.widths_le rawFit
    (fun r=>Fin.elim0 r.1) castRoom).1

theorem expr_fits {w} (s : B.Sources) (floor : ℕ) (m : Memory w) (early : B.Early s floor w)
    (room : B.endAddress floor<2^w) (j : ℕ) (inside : j<B.passes) : (B.expr s floor j).Fits w (B.out floor):=by
  have top : B.out floor<2^w:=lt_of_le_of_lt ((Nat.le_add_right ..).trans (B.order floor).2.2) room
  let z:=B.address.symm ⟨j,inside⟩
  simp only [expr,dite_eq_left inside]
  apply (DescentOperandFamilyBook.issued (H:=0) (G:=0) B.law B.zero B.layout.lanes (B.castEnd floor)
    z.1 (B.castArg s floor z.1 z.2) (B.castImage floor m) (fun h=>Fin.elim0 h)
    (B.arg_fits s floor m z.1 z.2 · early room) (fun _ r=>Fin.elim0 r.1) top).1

theorem any {w} (s : B.Sources) (floor : ℕ) (m : Memory w) (early : B.Early s floor w)
    (room : B.endAddress floor<2^w) :
    (B.program s floor w).Exec m (B.image s floor m) (B.ticks s floor) ∧
    CheapCode (B.program s floor w) ∧
    (∀i,i<floor ∨ B.endAddress floor≤ i → B.image s floor m i=m i) :=by
  obtain ⟨one,two,three⟩:=B.order floor
  have cap:=(Nat.le_add_right (B.out floor) (B.passes*B.rows)).trans three
  have c:=DescentOperandInputCast.any B.widths B.scalarWidth B.scalarWidth B.layout.lanes floor m B.widths_le
    ((two.trans cap).trans_lt room)
  have l:=DescentOperandFamilyBook.any B.law B.layout.lanes (B.castEnd floor) (B.castImage floor m)
    (cap.trans_lt room)
  have scan:=DescentPackedFlowBatch.execute (B.out floor) B.rows B.rows B.passes (B.expr s floor)
    (B.mounted floor m) (B.expr_fits s floor m early room) (three.trans_lt room) le_rfl
  refine ⟨?_,cheap_seq (cheap_seq c.2.1 l.2.1) (@ProtocolRAM.program_cheap _ _),?_⟩
  · intro P R K machine pc reg pub exit installed dat cfg mem start same
    exact Procedure.Exec.then (Procedure.Exec.then c.1 l.1) scan.1 machine pc reg pub exit installed dat cfg mem start same
  · intro i outside
    have eqn : B.image s floor m i=B.mounted floor m i:=by
      rcases outside with low|high
      · exact scan.2.2 i (low.trans_le (one.trans two))
      · apply DescentPackedFlowBatch.above _ _ _ _ _ _ _ _ le_rfl
        simpa only [Nat.zero_add] using three.trans high
    exact eqn.trans ((l.2.2.1 i (outside.imp (fun h=>h.trans_le one) (fun h=>cap.trans h))).trans
      (c.2.2.1 i (outside.imp_right (fun h=>(two.trans cap).trans h))))

end
end Hierarchy.DescentOrdinaryFinal.Chart

end OAI
