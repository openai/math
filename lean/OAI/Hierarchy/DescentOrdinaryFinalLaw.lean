import OAI.Hierarchy.DescentOrdinaryFinalChart
import OAI.Hierarchy.DescentOperandStateCodec
import OAI.Hierarchy.DescentLocalPrivateNames

namespace OAI
/-! # Resolve first occurrences among active ordinary operands and retain their spans -/
namespace Hierarchy.DescentOrdinaryFinal.Chart
open DescentSIMDLookup DescentPackedOperand DescentOperandStateBanks DescentLocalPrivateNames
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable (B : DescentOrdinaryFinal.Chart)
abbrev Input := Fin B.inputs→Cell B.scalarWidth
def columns := (finSumFinEquiv : Fin 3⊕Fin B.keys ≃ Fin B.inputs)
def slots := (finProdFinEquiv : (Fin B.layout.nodes×Fin B.layout.operands) ≃ Fin B.keys)
def pages := (finProdFinEquiv : (Fin 7×Fin B.layout.operands) ≃ Fin B.outputs)
def stamp (x : B.Input) (slot : Fin B.keys) := (x (B.columns (.inr slot))).val
def role (x : B.Input) (node : Fin B.layout.nodes) := digit B.roleBits node.val (x (B.columns (.inl 0))).val
def arity (x : B.Input) (node : Fin B.layout.nodes) := digit B.arityBits node.val (x (B.columns (.inl 1))).val
def live (x : B.Input) (slot : Fin B.keys) : Prop :=
  let mouth:=B.slots.symm slot
  mouth.2.val < B.arity x mouth.1

/-- A live private key is marked before comparing encoded keys. This includes
the all-zero five-field key representing the first donor and its first private word. -/
def marked (x : B.Input) (slot : Fin B.keys) : Cell (B.scalarWidth+1) :=
  if B.live x slot ∧ digit (B.layout.size+4) 0 (B.stamp x slot)<3 then
    ⟨1+B.stamp x slot,by
      have h:=(x (B.columns (.inr slot))).isLt
      have p:=Nat.two_pow_pos B.scalarWidth
      rw [pow_succ]
      dsimp [stamp];omega⟩
  else 0

def lane (p : Fin B.outputs) (x : B.Input) (n : Fin B.layout.nodes) : Cell B.field :=
  let field:= (B.pages.symm p).1
  let slot:=B.slots (n,(B.pages.symm p).2)
  let key:=B.stamp x slot
  let d:=digit (B.layout.size+4)
  if h:field.val<4 then
    if B.live x slot then
      ((component (d 0 key) (d 2 key) (d 3 key) (d 4 key)
        (renameDigit (B.marked x) slot) ⟨field.val,h⟩:ℕ):Cell B.field)
    else 0
  else ((digit B.field n.val (x (B.columns (.inl 2))).val:ℕ):Cell B.field)

def law (p : Fin B.outputs) (x : B.Input) : Cell (B.field*B.layout.nodes) :=
  encode B.field B.layout.nodes (B.lane p x)

theorem zero (p : Fin B.outputs) : B.law p (fun _=>0)=0 :=by
  have dead (n : Fin B.layout.nodes) : B.lane p (fun _=>0) n=0:=by
    dsimp only [lane]
    split <;> simp [live,arity,digit]
  apply Fin.ext
  change (finFunctionFinEquiv (B.lane p (fun _=>0))).val=0
  simp [dead]

theorem read (p : Fin B.outputs) (x : B.Input) (n : Fin B.layout.nodes) :
    digit B.field n.val (B.law p x).val=(B.lane p x n).val :=digit_encode _ _

theorem marked_key (x : B.Input) (slot : Fin B.keys) (valid : B.live x slot)
    (priv : digit (B.layout.size+4) 0 (B.stamp x slot)<3) :
    (B.marked x slot).val=1+B.stamp x slot:=by simp [marked,valid,priv]

theorem header (f : Fin 4) (a : Fin B.layout.operands) (n : Fin B.layout.nodes) (x : B.Input)
    (active : B.live x (B.slots (n,a))) (v : Fragment B.layout.size)
    (issue : B.stamp x (B.slots (n,a))=(word v).val)
    (fit : (Pointer.ofKey (renameDigit (B.marked x) (B.slots (n,a))-1) (resolve v)).header f<2^B.field) :
    digit B.field n.val (B.law (B.pages (f.castLE (by decide),a)) x).val=
      (Pointer.ofKey (renameDigit (B.marked x) (B.slots (n,a))-1) (resolve v)).header f :=by
  refine (B.read (B.pages (f.castLE (by decide),a)) x n).trans ?_
  simp only [lane,Equiv.symm_apply_apply,active,ite_true,Fin.val_castLE,f.isLt,
    dite_eq_left,issue]
  have a0 : digit (B.layout.size+4) 0 (word v).val=(resolve v).fields 0:=word_read v 0
  have a2 : digit (B.layout.size+4) 2 (word v).val=(resolve v).fields 2:=word_read v 2
  have a3 : digit (B.layout.size+4) 3 (word v).val=(resolve v).fields 3:=word_read v 3
  have a4 : digit (B.layout.size+4) 4 (word v).val=(resolve v).fields 4:=word_read v 4
  change component (digit _ 0 _) (digit _ 2 _) (digit _ 3 _) (digit _ 4 _) _ f % _=_
  rw [a0,a2,a3,a4,component_key,Nat.mod_eq_of_lt fit]

/-- All three range components come from the gathered record at this node. -/
theorem span_all (f : Fin 7) (hf : 4≤f.val) (a : Fin B.layout.operands) (n : Fin B.layout.nodes) (x : B.Input) :
    digit B.field n.val (B.law (B.pages (f,a)) x).val=
      digit B.field n.val (x (B.columns (.inl 2))).val:=by
  refine (B.read (B.pages (f,a)) x n).trans ?_
  simp only [lane,Equiv.symm_apply_apply,
    dite_eq_right (Nat.not_lt.mpr hf),Fin.val_natCast]
  apply Nat.mod_eq_of_lt
  simp only [digit,Nat.mul_add,Nat.mul_one,pow_add,Nat.mod_mul_right_div_self]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem span (f : Fin 7) (hf : 4≤f.val) (a : Fin B.layout.operands) (n : Fin B.layout.nodes) (x : B.Input)
    (_active : B.live x (B.slots (n,a))) :
    digit B.field n.val (B.law (B.pages (f,a)) x).val=
      digit B.field n.val (x (B.columns (.inl 2))).val:= B.span_all f hf a n x

theorem live_of_arity (x : B.Input) (n : Fin B.layout.nodes) (a : Fin B.layout.operands)
    (argument : a.val < B.arity x n) : B.live x (B.slots (n,a)):=by
  simpa only [live,Equiv.symm_apply_apply] using argument

end
end Hierarchy.DescentOrdinaryFinal.Chart

end OAI
