import OAI.Hierarchy.DescentOrdinaryPaletteBirthLayout
import OAI.Hierarchy.DescentPackedColumnHardware
import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # The single fixed lookup and sequential output scan used by the newborn palette -/
namespace Hierarchy.DescentOrdinaryPaletteBirth.Native
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryBorn DescentSixParty.Chronology
open DescentStaticWordColumn (names names_seq names_mount)
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {width : ℕ} (B : Chart) (value : Fin (fields B)→Cell B.chipBits→Cell width)
    (dead : ∀j,value j 0=0)
def law (j : Fin (fields B)) (v : Fin 1→Cell B.chipBits) :=value j (v 0)
local notation "L" => law B value
local notation "cols" => fields B
local notation "out" => output B
local notation "ceiling" => roof B
def query (old : Bank) : Fin 1→Expr :=fun _=>.lookup old .row
def expr (old : Bank) (at_ i : ℕ) : Expr :=
  if hi : i<cols then DescentOperandFamilyBook.expr L B.lanes at_ ⟨i,hi⟩ (query old) else .lit 0
local notation "pick" => expr B value
def scans (old : Bank) (at_ : ℕ) :=DescentPackedFlowBatch.passes (out at_) B.rows B.pitch (pick old at_) 0 cols
local notation "jobs" => scans B value
def program (old : Bank) (at_ w : ℕ) :=
  (DescentOperandFamilyBook.program L B.lanes at_ w).seq (ProtocolRAM.program w (jobs old at_))
def ticks (old : Bank) (at_ : ℕ) := 4+10*bookWords B+ProtocolRAM.clock (jobs old at_)
def mounted {w} (at_ : ℕ) (m : Memory w) :=DescentOperandFamilyBook.image L B.lanes at_ m
local notation "mid" => mounted B value
def image {w} (old : Bank) (at_ : ℕ) (m : Memory w) :=ProtocolRAM.result (jobs old at_) (mid at_ m)
def phase (old : Bank) (at_ w : ℕ) : NativePhase w where
  program := program B value old at_ w
  ticks := ticks B value old at_
  image := image B value old at_
  cheap := by
    intro P R K pc reg pub exit j
    exact cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@ProtocolRAM.program_cheap w (jobs old at_)) pc reg pub exit j

include dead in
theorem fits {w} (old : Bank) (at_ : ℕ) (m : Memory w) (early : old.Fits w at_) (room : ceiling at_<2^w) :
    ∀i<cols,(pick old at_ i).Fits w (out at_) :=by
  intro i hi
  rw [expr,dite_eq_left hi]
  exact (DescentOperandFamilyBook.issued L dead B.lanes at_ ⟨i,hi⟩ (query old) m
    (fun (_ : Fin 0) (_ : Fin 0) (_ : Fin 1)=>0) (fun _=>⟨early,trivial⟩)
    (fun _ r=>Fin.elim0 r.1) ((order B at_).2.trans_lt room)).1

include dead in
theorem any {w} (old : Bank) (at_ : ℕ) (m : Memory w) (early : old.Fits w at_) (room : ceiling at_<2^w) :
    let stage:=phase B value old at_ w
    stage.Runs m ∧ ∀a,a<at_ ∨ ceiling at_≤a → stage.image m a=m a :=by
  intro stage
  obtain ⟨first,last⟩:=order B at_
  have ready:=DescentOperandFamilyBook.any L B.lanes at_ m (last.trans_lt room)
  have passes:=DescentPackedFlowBatch.execute (out at_) B.rows B.pitch cols (pick old at_) (mid at_ m)
    (fits B value dead old at_ m early room) room B.seats
  refine ⟨?_,?_⟩
  · intro P R K board pc reg pub exit installed advice cfg mem start same
    exact Procedure.Exec.then ready.1 passes.1 board pc reg pub exit installed advice cfg mem start same
  · intro q avoid
    have saved : stage.image m q=mid at_ m q:=by
      rcases avoid with h|h
      · exact passes.2.2 q (h.trans_le first)
      · apply DescentPackedFlowBatch.above _ _ _ _ _ _ _ _ B.seats
        simpa only [roof,Nat.zero_add] using h
    exact saved.trans (ready.2.2.1 q (avoid.imp_right (fun h=>last.trans h)))

include dead in
theorem posted {w} (old : Bank) (at_ : ℕ) (m : Memory w) (early : old.Fits w at_)
    (v : Fin B.hosts→Fin B.groups→Cell B.chipBits) (oldRows : B.rows≤old.size)
    (read : Reads old v B.lanes m) (room : ceiling at_<2^w) (i : Fin cols) :
    Reads (bank B at_ i) (fun h g=>value i (v h g)) B.lanes
      ((phase B value old at_ w).image m) :=by
  have lookup:=DescentOperandFamilyBook.issued L dead B.lanes at_ i (query old) m
    (fun h g (_:Fin 1)=>v h g) (fun _=>⟨early,trivial⟩)
    (fun _=>source_column old at_ early m v oldRows read) ((order B at_).2.trans_lt room)
  have sent:=DescentPackedFlowBatch.execute (out at_) B.rows B.pitch cols (pick old at_) (mid at_ m)
    (fits B value dead old at_ m early room) room B.seats
  intro row_
  have actual:=sent.2.1 i (row B.hosts B.groups B.lanes row_)
  simp only [expr,dite_eq_left i.isLt] at actual
  exact actual.trans (lookup.2 row_)

theorem placed {w} (at_ : ℕ) (room : ceiling at_<2^w) (i : Fin cols) :
    (bank B at_ i).Fits w (ceiling at_) ∧ B.rows≤(bank B at_ i).size :=by
  have upper:=Nat.mul_le_mul_right B.pitch (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at upper
  have high : (bank B at_ i).base+(bank B at_ i).size≤ceiling at_ :=by
    change out at_+i.val*B.pitch+B.pitch≤out at_+cols*B.pitch
    omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (high.trans_lt room),high⟩,B.seats⟩

theorem expr_price (old : Bank) (at_ i : ℕ) (live : i<cols) : (pick old at_ i).work≤32 :=by
  unfold expr
  rw [dite_eq_left live]
  exact DescentOperandFamilyBook.expr_work L B.lanes at_ _ (query old) 7 (fun _=>le_rfl)

def cpu :=4+10*bookWords B+(4+cols*(4+B.rows*(2*32+4)))
def textCost :=15*(bookWords B+1)+(15+cols*(11+4*32))
theorem price (old : Bank) (at_ w : ℕ) :
    (phase B value old at_ w).ticks≤cpu B ∧ names (phase B value old at_ w).program≤textCost B :=by
  constructor
  · exact Nat.add_le_add_left (DescentPackedFlowBatch.tariff (out at_) B.rows B.pitch cols
      (pick old at_) 32 (expr_price B value old at_)) _
  · have book : names (DescentOperandFamilyBook.program L B.lanes at_ w)=15*(bookWords B+1):=by
      unfold DescentOperandFamilyBook.program Book.install
      simp only [names_mount]
      rfl
    change names ((DescentOperandFamilyBook.program L B.lanes at_ w).seq (ProtocolRAM.program w (jobs old at_)))≤_
    rw [names_seq,book]
    exact Nat.add_le_add le_rfl (DescentOperandVectorArena.names_passes (out at_) B.rows B.pitch w 32
      (pick old at_) 0 cols (fun i _ h=>expr_price B value old at_ i (by omega)))

end
end Hierarchy.DescentOrdinaryPaletteBirth.Native

end OAI
