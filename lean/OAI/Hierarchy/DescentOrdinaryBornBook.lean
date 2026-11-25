import OAI.Hierarchy.DescentOrdinaryBornChip
import OAI.Hierarchy.DescentOrdinaryBornChart
import OAI.Hierarchy.DescentOrdinaryBornDigits
import OAI.Hierarchy.DescentOperandFamilyBook
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentPackedColumnBatch

namespace OAI
/-! # A single native lookup family publishes the six newborn operand pages -/
namespace Hierarchy.DescentOrdinaryBorn.Chart
open DescentRawCablePanel DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (B : Chart)
def law (i : Fin B.fields) (u : Fin 1→Cell B.chipBits) : Cell B.bits :=
  let entry:=B.index.symm i
  let donor:=chipDonor B.format (u 0) entry.1.1.1
  component B.bits (pointerAt B.demand B.grain B.scale donor entry.1.1.2 entry.1.2.val) entry.2

theorem zero (i : Fin B.fields) : B.law i (fun _=>0)=0 :=
  component_absent _ (first_zero B.format _) _ _ _ _ _ _ _

def query (old : Bank) : Fin 1→Expr :=fun _=>.lookup old .row
def expr (old : Bank) (floor n : ℕ) : Expr :=
  if ok : n<B.fields then DescentOperandFamilyBook.expr B.law B.lanes floor ⟨n,ok⟩ (query old) else .lit 0
def scans (old : Bank) (floor : ℕ) :=DescentPackedFlowBatch.passes (B.output floor) B.rows B.pitch (B.expr old floor) 0 B.fields
def program (old : Bank) (floor w : ℕ) :=
  (DescentOperandFamilyBook.program B.law B.lanes floor w).seq (ProtocolRAM.program w (B.scans old floor))
def ticks (old : Bank) (floor : ℕ) := (4+10*B.bookWords)+ProtocolRAM.clock (B.scans old floor)
def mounted {w} (floor : ℕ) (m : Memory w) :=DescentOperandFamilyBook.image B.law B.lanes floor m
def image {w} (old : Bank) (floor : ℕ) (m : Memory w) :=ProtocolRAM.result (B.scans old floor) (B.mounted floor m)

theorem fits {w} (old : Bank) (floor : ℕ) (m : Memory w) (early : old.Fits w floor) (room : B.endAddress floor<2^w) :
    ∀i<B.fields,(B.expr old floor i).Fits w (B.output floor) :=by
  intro i hi
  rw [expr,dite_eq_left hi]
  exact (DescentOperandFamilyBook.issued B.law B.zero B.lanes floor ⟨i,hi⟩ (query old) m
    (fun (_ : Fin 0) (_ : Fin 0) (_ : Fin 1)=>0) (fun _=>⟨early,trivial⟩)
    (fun _ p=>Fin.elim0 p.1) ((B.order floor).2.trans_lt room)).1

theorem any {w} (old : Bank) (floor : ℕ) (m : Memory w) (early : old.Fits w floor) (room : B.endAddress floor<2^w) :
    (B.program old floor w).Exec m (B.image old floor m) (B.ticks old floor) ∧ CheapCode (B.program old floor w) ∧
      ∀i,i<floor ∨ B.endAddress floor≤ i → B.image old floor m i=m i :=by
  obtain ⟨first,last⟩:=B.order floor
  have mounted_:=DescentOperandFamilyBook.any B.law B.lanes floor m (last.trans_lt room)
  have recs:=DescentPackedFlowBatch.execute (B.output floor) B.rows B.pitch B.fields (B.expr old floor)
    (B.mounted floor m) (B.fits old floor m early room) room B.seats
  refine ⟨?_,cheap_seq mounted_.2.1 (@ProtocolRAM.program_cheap _ _),?_⟩
  · intro p r k board pc reg pub exit installed advice cfg mem start same
    exact Procedure.Exec.then mounted_.1 recs.1 board pc reg pub exit installed advice cfg mem start same
  · intro i outside
    have at_ : B.image old floor m i=B.mounted floor m i:=by
      rcases outside with h|h
      · exact recs.2.2 i (h.trans_le first)
      · apply DescentPackedFlowBatch.above _ _ _ _ _ _ _ _ B.seats
        simpa only [endAddress,Nat.zero_add] using h
    exact at_.trans (mounted_.2.2.1 i (outside.imp_right (last.trans ·)))

theorem issued {w} (old : Bank) (floor : ℕ) (m : Memory w) (early : old.Fits w floor)
    (v : Fin B.hosts→Fin B.groups→Cell B.chipBits) (oldRows : B.rows≤old.size) (read : Reads old v B.lanes m)
    (room : B.endAddress floor<2^w) (x : Fin B.blocks) (t : Fin B.cap) (j : Fin 6) (a : Fin B.args) (f : Fin 7) :
    Reads (B.bank floor x t j a f) (fun h g=>component B.bits
      (pointerAt B.demand B.grain B.scale (chipDonor B.format (v h g) (finProdFinEquiv (x,t))) j a.val) f)
      B.lanes (B.image old floor m) :=by
  let index_:=B.index (((finProdFinEquiv (x,t),j),a),f)
  have out:=DescentOperandFamilyBook.issued B.law B.zero B.lanes floor index_ (query old) m (fun h g (_:Fin 1)=>v h g)
    (fun _=>⟨early,trivial⟩) (fun _=>source_column old floor early m v oldRows read) ((B.order floor).2.trans_lt room)
  have sent:=DescentPackedFlowBatch.execute (B.output floor) B.rows B.pitch B.fields (B.expr old floor) (B.mounted floor m)
    (B.fits old floor m early room) room B.seats
  intro row_
  have word_:=sent.2.1 index_ (row B.hosts B.groups B.lanes row_)
  simp only [expr,dite_eq_left index_.isLt] at word_
  have native:=word_.trans (out.2 row_)
  simp only [image,scans,bank,index_,law,Equiv.symm_apply_apply] at native ⊢
  exact native

theorem placed {w} (floor : ℕ) (room : B.endAddress floor<2^w) (x : Fin B.blocks) (t : Fin B.cap)
    (j : Fin 6) (a : Fin B.args) (f : Fin 7) :
    (B.bank floor x t j a f).Fits w (B.endAddress floor) ∧ B.rows≤(B.bank floor x t j a f).size:=by
  let i:=B.index (((finProdFinEquiv (x,t),j),a),f)
  have upper:=Nat.mul_le_mul_right B.pitch (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at upper
  have high : (B.bank floor x t j a f).base+(B.bank floor x t j a f).size≤B.endAddress floor :=by
    change B.output floor+i.val*B.pitch+B.pitch≤B.output floor+B.fields*B.pitch
    omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (high.trans_lt room),high⟩,B.seats⟩
end
end Hierarchy.DescentOrdinaryBorn.Chart

end OAI
