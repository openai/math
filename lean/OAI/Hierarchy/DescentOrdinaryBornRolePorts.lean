import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentOrdinaryBornRoleNumerals
import OAI.Hierarchy.DescentOrdinaryBornBook
import OAI.Hierarchy.DescentOrdinaryBornTariff

namespace OAI
/-! # The anchor, signed side and original branch at each live newborn operand -/
namespace Hierarchy.DescentOrdinaryBorn.RolePorts
open DescentRawCablePanel DescentSIMDLookup DescentPackedZip DescentPackedColony DescentStaticWordColumn
open DescentPacking.PackedMatch.Local DescentSixParty.Chronology ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

theorem semantic {l a c : ℕ} (B : Spec) (z prof arg bits : ℕ) (j : Fin 6) (d : Donor l a c)
    (first : d.first=true) (supply : ∀e,(d.supplyUnits e).val=(profileDigits B.capacity prof e).val+B.supplyOffset)
    (f : Fin 3) : value bits (pointerAt B.demand B.grain z d j arg) f=
      value bits (mouth B z prof j arg) f :=by
  simp only [pointerAt,first,ite_true]
  rw [funext supply,measured_actual]

variable (B : Chart)
def index : (((Fin B.donors×Fin 6)×Fin B.args)×Fin 3)≃Fin (RolePorts.fields B) :=
  (Equiv.prodCongr ((Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv) (Equiv.refl _)).trans finProdFinEquiv
def bank (base : ℕ) (x : Fin B.blocks) (t : Fin B.cap) (j : Fin 6) (a : Fin B.args) (f : Fin 3) : Bank :=
  ⟨output B base+((index B) (((finProdFinEquiv (x,t),j),a),f)).val*B.pitch,Nat.clog 2 B.rows⟩
theorem order (base : ℕ) : base≤output B base ∧ output B base≤endAddress B base:=
  ⟨Nat.le_add_right ..,Nat.le_add_right ..⟩
theorem affine (base : ℕ) : endAddress B base=base+endAddress B 0:=by simp [endAddress,output,Nat.add_assoc]

def law (i : Fin (RolePorts.fields B)) (u : Fin 1→Cell B.chipBits) : Cell B.bits :=
  let entry:=(index B).symm i
  let donor:=chipDonor B.format (u 0) entry.1.1.1
  value B.bits (pointerAt B.demand B.grain B.scale donor entry.1.1.2 entry.1.2.val) entry.2

theorem zero (i : Fin (RolePorts.fields B)) : law B i (fun _=>0)=0 := by
  unfold law pointerAt
  dsimp only
  erw [first_zero B.format ((index B).symm i).1.1.1]
  rfl
def expr (old : Bank) (floor n : ℕ) : Expr :=
  if ok : n<(RolePorts.fields B) then DescentOperandFamilyBook.expr (law B) B.lanes floor ⟨n,ok⟩ (Chart.query old) else .lit 0
def scans (old : Bank) (floor : ℕ) :=DescentPackedFlowBatch.passes (output B floor) B.rows B.pitch (expr B old floor) 0 (RolePorts.fields B)
def program (old : Bank) (floor w : ℕ) :=
  (DescentOperandFamilyBook.program (law B) B.lanes floor w).seq (ProtocolRAM.program w (scans B old floor))
def ticks (old : Bank) (floor : ℕ) := (4+10*(bookWords B))+ProtocolRAM.clock (scans B old floor)
def mounted {w} (floor : ℕ) (m : Memory w) :=DescentOperandFamilyBook.image (law B) B.lanes floor m
def image {w} (old : Bank) (floor : ℕ) (m : Memory w) :=ProtocolRAM.result (scans B old floor) (mounted B floor m)

theorem fits {w} (old : Bank) (floor : ℕ) (m : Memory w) (early : old.Fits w floor) (room : endAddress B floor<2^w) :
    ∀i<(RolePorts.fields B),(expr B old floor i).Fits w (output B floor) :=by
  intro i hi
  rw [expr,dite_eq_left hi]
  exact (DescentOperandFamilyBook.issued (law B) (zero B) B.lanes floor ⟨i,hi⟩ (Chart.query old) m
    (fun (_ : Fin 0) (_ : Fin 0) (_ : Fin 1)=>0) (fun _=>⟨early,trivial⟩)
    (fun _ p=>Fin.elim0 p.1) ((order B floor).2.trans_lt room)).1

theorem any {w} (old : Bank) (floor : ℕ) (m : Memory w) (early : old.Fits w floor) (room : endAddress B floor<2^w) :
    (program B old floor w).Exec m (image B old floor m) (ticks B old floor) ∧ CheapCode (program B old floor w) ∧
      ∀i,i<floor ∨ endAddress B floor ≤ i → image B old floor m i=m i :=by
  obtain ⟨first,last⟩:=order B floor
  have mounted_:=DescentOperandFamilyBook.any (law B) B.lanes floor m (last.trans_lt room)
  have recs:=DescentPackedFlowBatch.execute (output B floor) B.rows B.pitch (RolePorts.fields B) (expr B old floor)
    (mounted B floor m) (fits B old floor m early room) room B.seats
  refine ⟨?_,cheap_seq mounted_.2.1 (@ProtocolRAM.program_cheap _ _),?_⟩
  · intro p r k board pc reg pub exit installed advice cfg mem start same
    exact Procedure.Exec.then mounted_.1 recs.1 board pc reg pub exit installed advice cfg mem start same
  · intro i outside
    have at_ : image B old floor m i=mounted B floor m i:=by
      rcases outside with h|h
      · exact recs.2.2 i (h.trans_le first)
      · apply DescentPackedFlowBatch.above _ _ _ _ _ _ _ _ B.seats
        simpa only [endAddress,Nat.zero_add] using h
    exact at_.trans (mounted_.2.2.1 i (outside.imp_right (last.trans ·)))

theorem issued {w} (old : Bank) (floor : ℕ) (m : Memory w) (early : old.Fits w floor)
    (v : Fin B.hosts→Fin B.groups→Cell B.chipBits) (oldRows : B.rows≤old.size) (read : Reads old v B.lanes m)
    (room : endAddress B floor<2^w) (x : Fin B.blocks) (t : Fin B.cap) (j : Fin 6) (a : Fin B.args) (f : Fin 3) :
    Reads (bank B floor x t j a f) (fun h g=>value B.bits
      (pointerAt B.demand B.grain B.scale (chipDonor B.format (v h g) (finProdFinEquiv (x,t))) j a.val) f)
      B.lanes (image B old floor m) :=by
  let index_:=(index B) (((finProdFinEquiv (x,t),j),a),f)
  have out:=DescentOperandFamilyBook.issued (law B) (zero B) B.lanes floor index_ (Chart.query old) m (fun h g (_:Fin 1)=>v h g)
    (fun _=>⟨early,trivial⟩) (fun _=>source_column old floor early m v oldRows read) ((order B floor).2.trans_lt room)
  have sent:=DescentPackedFlowBatch.execute (output B floor) B.rows B.pitch (RolePorts.fields B) (expr B old floor) (mounted B floor m)
    (fits B old floor m early room) room B.seats
  intro row_
  have word_:=sent.2.1 index_ (row B.hosts B.groups B.lanes row_)
  simp only [expr,dite_eq_left index_.isLt] at word_
  have native:=word_.trans (out.2 row_)
  simp only [image,scans,bank,index_,law,Equiv.symm_apply_apply] at native ⊢
  exact native

theorem placed {w} (floor : ℕ) (room : endAddress B floor<2^w) (x : Fin B.blocks) (t : Fin B.cap)
    (j : Fin 6) (a : Fin B.args) (f : Fin 3) :
    (bank B floor x t j a f).Fits w (endAddress B floor) ∧ B.rows≤(bank B floor x t j a f).size:=by
  let i:=(index B) (((finProdFinEquiv (x,t),j),a),f)
  have upper:=Nat.mul_le_mul_right B.pitch (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at upper
  have high : (bank B floor x t j a f).base+(bank B floor x t j a f).size≤endAddress B floor :=by
    change output B floor+i.val*B.pitch+B.pitch≤output B floor+(RolePorts.fields B)*B.pitch
    omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (high.trans_lt room),high⟩,B.seats⟩

def phase (old : Bank) (base w : ℕ) : NativePhase w :=
  ⟨program B old base w,ticks B old base,image B old base,cheap_seq
    (DescentStaticWordColumn.cheap w base _ _) (ProtocolRAM.program_cheap w _)⟩

theorem resources (old : Bank) (base w : ℕ) :
    ticks B old base≤B.cpu ∧ names (program B old base w)≤B.textCost ∧ endAddress B base≤B.endAddress base :=by
  have fewer : RolePorts.fields B≤B.fields :=Nat.mul_le_mul_left _ (by decide : 3≤7)
  have table : bookWords B≤B.bookWords:= Nat.mul_le_mul_right _ (Nat.add_le_add_left fewer 1)
  have normal (i : ℕ) (hi : i<RolePorts.fields B) : (expr B old base i).work≤32:=by
    simp only [expr,dite_eq_left hi]
    exact DescentOperandFamilyBook.expr_work (law B) B.lanes base _ (Chart.query old) 7 (fun _=>le_rfl)
  have t:=DescentPackedFlowBatch.tariff (output B base) B.rows B.pitch (RolePorts.fields B) (expr B old base) 32 normal
  have n:=DescentOperandVectorArena.names_passes (output B base) B.rows B.pitch w 32 (expr B old base) 0 (RolePorts.fields B)
    (fun i _ hi=>normal i (by omega))
  have named : names (DescentOperandFamilyBook.program (law B) B.lanes base w)=15*(bookWords B+1):=by
    unfold DescentOperandFamilyBook.program Book.install
    rw [names_mount]
    rfl
  refine ⟨Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 10 table) 4)
    (t.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ fewer) 4)),?_,?_⟩
  · rw [program,names_seq,named]
    exact Nat.add_le_add (Nat.mul_le_mul_left 15 (Nat.add_le_add_right table 1))
      (n.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ fewer) 15))
  · exact Nat.add_le_add (Nat.add_le_add_left table base) (Nat.mul_le_mul_right _ fewer)

end
end Hierarchy.DescentOrdinaryBorn.RolePorts

end OAI
