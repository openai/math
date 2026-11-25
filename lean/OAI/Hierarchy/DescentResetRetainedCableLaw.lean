import OAI.Hierarchy.DescentOperandPriorTicket
import OAI.Hierarchy.DescentOperandFamilyBook

namespace OAI
/-! # Native retained-operand selection on the remixed signed panel and chronological incoming tickets -/
namespace Hierarchy.DescentResetRetainedCableLaw
open DescentSIMDLookup DescentPackedZip DescentOperandStateBanks DescentOperandSignedSearch
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- The input is the four old pointer digits, its original donor plus one, the
hub flag, all signed cells in the same terminal, and the incoming ticket of
each signed slot measured at the opposite relay. -/
structure Shape where
  degree : ℕ
  cap : ℕ
  donors : ℕ
  units : ℕ
  fieldBits : ℕ
  queryBits : ℕ
  lanes : ℕ

namespace Shape
variable (C : Shape)
def strip := C.donors*(2*C.cap)
def inputs := 6+2*C.strip
abbrev Input :=Fin C.inputs→Cell C.fieldBits
abbrev Slot :=Fin (2*C.cap)
abbrev Donor :=Fin C.donors

def header (x : C.Input) (i : Fin 4) : Cell C.fieldBits :=
  x ⟨i.val,by have h:=i.isLt;unfold inputs;omega⟩
def donorCell (x : C.Input) := x ⟨4,by unfold inputs;omega⟩
def hubCell (x : C.Input) := x ⟨5,by unfold inputs;omega⟩
def laneIndex (ticket : Bool) (z : C.Donor) (j : C.Slot) : Fin C.inputs :=
  let n:=finProdFinEquiv (z,j)
  ⟨6+(if ticket then C.strip else 0)+n.val,by
    have h : n.val<C.strip:=n.isLt
    cases ticket <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> unfold inputs <;> omega⟩
def row (x : C.Input) (z : C.Donor) (j : C.Slot) : Cell (DescentSignedCableCodec.width C.degree C.cap) :=
  (x (C.laneIndex false z j)).val
def ticket (x : C.Input) (z : C.Donor) (j : C.Slot) := (x (C.laneIndex true z j)).val
def locate (x : C.Input) (z : C.Donor) (side : Fin 2) :=
  (resultCell C.degree C.cap side (DescentOperandPriorTicket.key C.degree C.cap C.units (C.header x)) (C.row x z)).val

/-- All surviving cables incident to a carried old node have their new source
at its primary terminal. An old loop uses the outgoing stem, consistently
with the ordered trunk splice's source-first case split. -/
def locateDonor (x : C.Input) (z : C.Donor) : Option (Bool×C.Slot) :=
  let left:=C.locate x z 0
  let right:=C.locate x z 1
  if live:0<left ∧ left≤2*C.cap then some (false,⟨left-1,by omega⟩)
  else if live:0<right ∧ right≤2*C.cap then some (true,⟨right-1,by omega⟩)
  else none

def found (x : C.Input) : Option (C.Donor×Bool×C.Slot) :=
  if live:(C.header x 0).val=1 ∧ 0<(C.donorCell x).val ∧ (C.donorCell x).val≤C.donors then
    let z:C.Donor:=⟨(C.donorCell x).val-1,by omega⟩
    (C.locateDonor x z).map (fun p=>(z,p))
  else none

def query (x : C.Input) : Cell C.queryBits :=
  (C.found x).elim 0 fun t=>
    if t.2.1 then (1+2*C.strip : ℕ) else (1+(finProdFinEquiv (t.1,t.2.2)).val : ℕ)

/-- The second and third columns are the cable serial adjustment and the
p-word offset within the emitted child. Other pointer fields add zero here. -/
def correction (f : Fin 2) (x : C.Input) : Cell C.fieldBits :=
  (C.found x).elim 0 fun t=>
    let old:=(C.header x 3).val%C.units
    let coarse:=if t.2.1 then (C.ticket x t.1 t.2.2)*C.units+old else old
    let marked:=t.2.1 && decide ((C.hubCell x).val≠1)
    if f.val=0 then (if marked then coarse/C.units else 0 : ℕ)
    else (if marked then coarse%C.units else coarse : ℕ)

theorem outgoing (x : C.Input) (z : C.Donor) (j : C.Slot) (cable : (C.header x 0).val=1)
    (donor : (C.donorCell x).val=z.val+1) (left : C.locate x z 0=j.val+1) :
    C.found x=some (z,false,j) :=by
  have decoded : (⟨(C.donorCell x).val-1,by rw [donor];omega⟩:C.Donor)=z:=
    Fin.ext (by change (C.donorCell x).val-1=z.val; omega)
  have live : (C.header x 0).val=1 ∧ 0<(C.donorCell x).val ∧ (C.donorCell x).val≤C.donors:=
    ⟨cable,by rw [donor];omega,by rw [donor];exact z.isLt⟩
  simp only [found,dite_eq_left live,decoded,locateDonor,left]
  have yes : 0<j.val+1 ∧ j.val+1≤2*C.cap:=⟨Nat.zero_lt_succ _,j.isLt⟩
  simp [yes]

theorem incoming (x : C.Input) (z : C.Donor) (j : C.Slot) (cable : (C.header x 0).val=1)
    (donor : (C.donorCell x).val=z.val+1) (left : C.locate x z 0=0)
    (right : C.locate x z 1=j.val+1) : C.found x=some (z,true,j) :=by
  have decoded : (⟨(C.donorCell x).val-1,by rw [donor];omega⟩:C.Donor)=z:=
    Fin.ext (by change (C.donorCell x).val-1=z.val; omega)
  have live : (C.header x 0).val=1 ∧ 0<(C.donorCell x).val ∧ (C.donorCell x).val≤C.donors:=
    ⟨cable,by rw [donor];omega,by rw [donor];exact z.isLt⟩
  have yes : 0<j.val+1 ∧ j.val+1≤2*C.cap:=⟨Nat.zero_lt_succ _,j.isLt⟩
  simp [found,live,decoded,locateDonor,left,right,yes]

theorem absent (x : C.Input) (tag : (C.header x 0).val≠1) : C.found x=none := by simp [found,tag]
theorem query_none (x : C.Input) (noneAt : C.found x=none) : C.query x=0 :=by simp [query,noneAt]
theorem charge_none (x : C.Input) (noneAt : C.found x=none) (f : Fin 2) : C.correction f x=0 :=by
  simp [correction,noneAt]

def queryLaw (_ : Fin 1) (x : C.Input) :=C.query x
def prices (f : Fin 2) (x : C.Input) :=C.correction f x
def queryEnd (base : ℕ) :=DescentOperandFamilyBook.endAddress 1 C.inputs C.fieldBits C.lanes base
def endAddress (base : ℕ) :=DescentOperandFamilyBook.endAddress 2 C.inputs C.fieldBits C.lanes (C.queryEnd base)
def program (base w : ℕ) :=(DescentOperandFamilyBook.program C.queryLaw C.lanes base w).seq
  (DescentOperandFamilyBook.program C.prices C.lanes (C.queryEnd base) w)
def first {w : ℕ} (base : ℕ) (m : Memory w) :=DescentOperandFamilyBook.image C.queryLaw C.lanes base m
def image {w : ℕ} (base : ℕ) (m : Memory w) :=DescentOperandFamilyBook.image C.prices C.lanes (C.queryEnd base) (C.first base m)
def ticks :=DescentOperandFamilyBook.ticks 1 C.inputs C.fieldBits C.lanes+
  DescentOperandFamilyBook.ticks 2 C.inputs C.fieldBits C.lanes

theorem order (base : ℕ) : base≤C.queryEnd base ∧ C.queryEnd base≤C.endAddress base:=
  ⟨Nat.le_add_right ..,Nat.le_add_right ..⟩

theorem any {w : ℕ} (base : ℕ) (m : Memory w) (room : C.endAddress base<2^w) :
    (C.program base w).Exec m (C.image base m) C.ticks ∧ CheapCode (C.program base w) ∧
    ∀a,a<base ∨ C.endAddress base≤a → C.image base m a=m a :=by
  obtain ⟨a,b⟩:=C.order base
  have one:=DescentOperandFamilyBook.any C.queryLaw C.lanes base m (b.trans_lt room)
  have two:=DescentOperandFamilyBook.any C.prices C.lanes (C.queryEnd base) (C.first base m) room
  refine ⟨Procedure.Exec.then one.1 two.1,cheap_seq one.2.1 two.2.1,?_⟩
  intro i hi
  exact (two.2.2.1 i (hi.imp_left (·.trans_le a))).trans (one.2.2.1 i (hi.imp_right (b.trans ·)))

end Shape
end
end Hierarchy.DescentResetRetainedCableLaw

end OAI
