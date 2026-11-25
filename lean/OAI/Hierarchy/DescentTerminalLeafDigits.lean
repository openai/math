import OAI.Hierarchy.DescentTerminalFieldCoordinates
import OAI.Hierarchy.DescentTerminalPrintedFieldsRAM
import OAI.Hierarchy.DescentTerminalDenseHeaderRAM

namespace OAI
/-! # Sparse local digit addresses of the ordered rows in one scalar book -/
namespace Hierarchy.DescentTerminalLeafDigits
open DescentTerminalPrintedFields
open scoped Classical BigOperators
noncomputable section

variable {q t V H N A w : ℕ}
local notation "u" => capacity q t H N A w V
local notation "s" => DescentTerminalPrintedFieldsRAM.strides u

def place : Coord V H N A→ℕ :=
  Sum.elim (fun _=>(s).a) (Sum.elim
    (fun i=>(s).b*((H+1)*(N+1))^i.val*(N+1)) (Sum.elim
    (fun i=>(s).b*((H+1)*(N+1))^i.val) (Sum.elim
    (fun z=>(s).c*((w+1)^H)^z.1.val*(w+1)^z.2.val) (Sum.elim
    (fun z=>(s).d*((t+1)^N)^z.1.val*(t+1)^z.2.val) (Sum.elim
    (fun z=>(s).e*((A+1)^N)^z.1.val*(A+1)^z.2.val)
    (fun z=>(s).f*(((q+H+1)^A)^N)^z.1.val*((q+H+1)^A)^z.2.1.val*(q+H+1)^z.2.2.val))))))

theorem serial_digits (f : Fields q t H N A w V) :
    (serial u (digits f)).val=∑i,(digit f i).val*place (q:=q) (t:=t) (w:=w) i := by
  rw [DescentTerminalPrintedFieldsRAM.serial_val]
  simp only [digits,finFunctionFinEquiv_apply,finProdFinEquiv,Equiv.coe_fn_mk,
    Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_unique,digit,place,Sum.elim_inl,Sum.elim_inr,
    Finset.sum_add_distrib,Finset.sum_mul,Nat.add_mul,Nat.mul_add]
  ring_nf
  have sizeWeight (x : Fin V) := Nat.mul_comm (f.sizes x).2.val (s).b
  have widthWeight (x : Fin V) (y : Fin H) := Nat.mul_comm (f.width x y).val (s).c
  have roleWeight (x : Fin V) (y : Fin N) := Nat.mul_comm (f.role x y).val (s).d
  have arityWeight (x : Fin V) (y : Fin N) := Nat.mul_comm (f.arity x y).val (s).e
  have operandWeight (x : Fin V) (y : Fin N) (z : Fin A) := Nat.mul_comm (f.operand x y z).val (s).f
  simp only [sizeWeight,widthWeight,roleWeight,arityWeight,operandWeight]
  omega

/-- The sparse code reserves exactly one address per possible nonzero
value of a local coordinate. No slot is needed for the implicit zeros. -/
abbrev Event (q t V H N A w : ℕ) := (i : Coord V H N A) × Fin (radix q t V H N A w i-1)

def weight (e : Event q t V H N A w) := (e.2.val+1)*place (q:=q) (t:=t) (w:=w) e.1

def token (f : Fields q t H N A w V) (i : Coord V H N A) (live : (digit f i).val≠0) :
    Event q t V H N A w := ⟨i,⟨(digit f i).val-1,by have:=(digit f i).isLt;omega⟩⟩
theorem token_weight (f : Fields q t H N A w V) (i : Coord V H N A) (h : (digit f i).val≠0) :
    weight (token f i h)=(digit f i).val*place (q:=q) (t:=t) (w:=w) i := by
  rw [weight,token,show (digit f i).val-1+1=(digit f i).val by omega]

theorem sparse_digits (f : Fields q t H N A w V) :
    (serial u (digits f)).val=∑j : {i : Coord V H N A // (digit f i).val≠0},weight (token f j.val j.property) := by
  rw [serial_digits]
  simp_rw [token_weight]
  rw [←Finset.sum_subtype (p:=fun i : Coord V H N A=>(digit f i).val≠0)
    (Finset.univ.filter (fun i : Coord V H N A=>(digit f i).val≠0))
    (by intro i; simp only [Finset.mem_filter,Finset.mem_univ,true_and])
    (fun i=>(digit f i).val*place (q:=q) (t:=t) (w:=w) i)]
  symm
  apply Finset.sum_subset (Finset.filter_subset ..)
  intro j _ off
  have zero : (digit f j).val=0 := by simpa using off
  simp [zero]

abbrev tokenCount (q t V H N A w : ℕ) := ∑i : Coord V H N A,(radix q t V H N A w i-1)
def eventOrder : Event q t V H N A w≃Fin (tokenCount q t V H N A w) :=
  ProtocolRAMPortRanks.enumerate (fun i=>radix q t V H N A w i-1) (fun i=>(fieldsOrder V H N A i).val)
    (fun _ _ e=>(fieldsOrder V H N A).injective (Fin.ext e))

theorem event_address (e : Event q t V H N A w) : (eventOrder e).val=
    (∑i ∈ Finset.univ.filter (fun i=>(fieldsOrder V H N A i).val<(fieldsOrder V H N A e.1).val),
      (radix q t V H N A w i-1))+e.2.val := rfl

theorem radix_pos (i : Coord V H N A) : 0<radix q t V H N A w i := by
  rcases i with _|(_|(_|(_|(_|(_|_))))) <;> simp [radix]

theorem event_room : tokenCount q t V H N A w+1 ≤ (u).total := by
  let r:=radix q t V H N A w
  have bound (z : Finset (Coord V H N A)) : (∑i∈z,(r i-1))+1 ≤ ∏i∈z,r i := by
    induction z using Finset.induction_on with
    | empty=>simp
    | @insert i z off ih=>
      rw [Finset.sum_insert off,Finset.prod_insert off]
      have positive : 0<r i:=radix_pos i
      have slack : (∑j∈z,(r j-1)) ≤ (r i)*(∑j∈z,(r j-1)) := Nat.le_mul_of_pos_left _ positive
      have upper:=Nat.mul_le_mul_left (r i) ih
      rw [Nat.mul_add,Nat.mul_one] at upper
      omega
  have equal : (∏i,r i)=(u).total := by
    simp only [r,radix,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.prod_const,Finset.card_univ,
      Fintype.card_unit,Fintype.card_prod,Fintype.card_fin,capacity,Six.total,Nat.mul_pow]
    ring
  rw [←equal]
  exact bound Finset.univ

def dictionary : List ℕ :=
  List.ofFn (fun j : Fin (tokenCount q t V H N A w+1)=>Fin.cases 0 (fun i=>weight (eventOrder.symm i)) j)

theorem dictionary_token (e : Event q t V H N A w) :
    (dictionary (q:=q) (t:=t) (V:=V) (H:=H) (N:=N) (A:=A) (w:=w))[(eventOrder e).succ.val]'
      (by simpa only [dictionary,List.length_ofFn] using (eventOrder e).succ.isLt)=weight e := by
  simp only [dictionary,List.getElem_ofFn,Fin.eta,Fin.cases_succ,Equiv.symm_apply_apply]

end
end Hierarchy.DescentTerminalLeafDigits

end OAI
