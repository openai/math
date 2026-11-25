import OAI.ThreeFlat.RAM.TraceAddressReader
import OAI.ThreeFlat.RAM.TraceTemplateProgram

namespace OAI
/-! # A fixed ROM that generates every physical record of a universal trace

The eleven public words specify the two table locations and the physical
network sizes. The gate table and the port records are stored consecutively
within their respective source intervals.
-/

namespace ThreeFlat.RAM.FixedTraceProgram

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM DescriptorExpr GuardedDescriptor BitLayout Diagonal.TraceAddressRecord
open scoped Fin.CommRing
variable {w : ℕ}

abbrev P := 2+(5+11)
def extra (i : Fin 11) : Fin P := Fin.natAdd 2 (Fin.natAdd 5 i)
def arg (i : Fin 10) : Term w P 1 :=
  ![.result 0,.parameter (extra 0),.parameter (extra 1),.parameter (extra 2),.parameter (extra 3),
    .parameter (extra 4),.parameter (extra 5),.parameter (extra 6),.parameter (extra 7),.parameter (extra 8)] i
def names : Inputs (Fin 10) := ⟨0,1,2,3,4,5,6,7,8,9⟩

def copy : Term w P 13 :=
  .load (.binary .add (.binary .add (.parameter (extra 9))
    (.binary .mul (.literal 11) (.result 1))) (.result 0))
def port : Term w P 12 :=
  TraceAddressReader.lookup (.result 1) (.result 0) (.parameter (extra 10))

def lookups : Lookups w P 10 := ⟨copy,port,.literal 0,.literal 0⟩
def program (w : ℕ) : Term w P 1 := bindParams names lookups arg

theorem size (w : ℕ) : (program w).binds ≤ 430 := by
  have pa : ∑ j : Fin 10, (arg (w:=w) j).binds = 9 := by simp [Fin.sum_univ_succ,arg,Term.parameter,Term.binds]
  rw [program,binds_bindParams,binds_compile,pa]
  simp [lookups,copy,port,Term.load,Term.binary,Term.parameter,Term.literal,Term.binds,
    TraceAddressReader.lookup_binds]

variable {F : Type*} [CommSemiring F] {q t b p : ℕ}

def publicWords (N : BitNetwork F q) (code : FieldCode F w) (p b base gateBase portBase : ℕ) :
    Fin 11 → Word w :=
  ![(base : Word w), (q : Word w), (N.cells : Word w), (N.internal : Word w), 0,
    (p : Word w), (b : Word w), code.encode 0, code.encode 1, (gateBase : Word w), (portBase : Word w)]


def operands (words : Fin P → Word w) (mem : Memory w) (a : ℕ) : Fin 10 → Word w :=
  fun ix => (arg ix).eval words mem (fun _ => (a : Word w))

def interpret (L : Lookups w P 10) (words : Fin P → Word w) (mem : Memory w) (vs : Fin 10 → Word w) : Readers w where
  copy row i col := L.copy.eval words mem (Fin.cons col (Fin.cons i (Fin.cons row vs)))
  pin row i := L.pin.eval words mem (Fin.cons i (Fin.cons row vs))
  left row i := L.left.eval words mem (Fin.cons i (Fin.cons row vs))
  right row i := L.right.eval words mem (Fin.cons i (Fin.cons row vs))

private theorem eval_generic (L : Lookups w P 10) (words : Fin P → Word w) (mem : Memory w) (a : ℕ) :
    let vs := operands words mem a
    let R := interpret L words mem vs
    (bindParams names L arg).eval words mem (fun _ => (a : Word w)) =
      word (names.map vs) R.copy R.pin R.left R.right := by
  dsimp only
  simp only [bindParams,Term.eval_instantiate,eval_compile,interpret]
  rfl

private theorem eval_program (words : Fin P → Word w) (mem : Memory w) (a : ℕ) :
    let vs := operands words mem a
    let R := interpret lookups words mem vs
    (program w).eval words mem (fun _ => (a : Word w)) =
      word (names.map vs) R.copy R.pin R.left R.right :=
  eval_generic lookups words mem a

private theorem keys_eq (N : BitNetwork F q) (code : FieldCode F w) (p b base gateBase portBase a : ℕ)
    (words : Fin P → Word w) (m : Memory w)
    (pub : ∀ i, words (extra i) = publicWords N code p b base gateBase portBase i) :
    names.map (operands words m a) = recordInputs N code p b 0 base a := by
  change Inputs.mk (a : Word w) (words (extra 0)) (words (extra 1)) (words (extra 2))
    (words (extra 3)) (words (extra 4)) (words (extra 5)) (words (extra 6))
    (words (extra 7)) (words (extra 8)) = _
  simp only [pub]
  rfl

private theorem valid (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (input : Fin t → Fin q → BitSource b p) (base gateBase portBase : ℕ) (words : Fin P → Word w)
    (mem : Memory w) (vs : Fin 10 → Word w)
    (pub : ∀ i, words (extra i) = publicWords N code p b base gateBase portBase i)
    (gate : ∀ (i : Fin N.cells) (j : Fin 11), mem (gateBase+11*i.val+j.val) = record N code i j)
    (fields : ∀ (a : Fin q) j, mem (TraceAddressReader.address portBase a.val j) =
      (TraceAddressReader.fields (R a) j : Word w))
    (gateFit : gateBase+11*N.cells ≤ 2^w) (portFit : portBase+11*q ≤ 2^w)
    (safe : ∀ (v : Fin t) j, (R j).Fits w v.val)
    (addr : ∀ (v : Fin t) j, (R j).eval v.val = sourceAddress (input v j))
    (hw : 0<w) : Reads (interpret lookups words mem vs) N input TraceTemplate.empty TraceTemplate.empty code := by
  constructor
  · intro i z j
    have hi : gateBase+11*z.val+j.val < 2^w := by have := z.isLt; have := j.isLt; omega
    simp only [interpret,lookups,copy,Term.eval_load,Term.eval_binary,Term.eval_parameter,Term.eval_literal,
      Term.eval,Fin.cons_zero,Fin.cons_one,BinaryOp.eval]
    change mem (((words (extra 9))+11*(z.val : Word w)+(j.val : Word w)).val) = _
    rw [pub]
    change mem (((gateBase : Word w)+11*(z.val : Word w)+(j.val : Word w)).val) = _
    have h : (gateBase : Word w)+11*(z.val : Word w)+(j.val : Word w) =
        ((gateBase+11*z.val+j.val : ℕ) : Word w) := by push_cast; rfl
    rw [h,Fin.val_cast_of_lt hi,gate]
  · intro i z
    have hz : portBase+11*z.val+10 < 2^w := by have := z.isLt; omega
    have hb : words (extra 10)=(portBase : Word w) := (pub 10).trans rfl
    have ans := TraceAddressReader.lookup_eval
      (.result (1 : Fin 12)) (.result (0 : Fin 12)) (.parameter (extra 10)) (R z) i.val z.val portBase
      hw (safe i z) hz words mem (Fin.cons (z.val : Word w) (Fin.cons (i.val : Word w) vs))
      rfl rfl hb (fields z)
    simp only [interpret,lookups,port]
    exact ans.trans (congrArg (fun n : ℕ => (n : Word w)) (addr i z))
  · exact fun _ j => j.elim0
  · exact fun _ j => j.elim0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 900000 in
theorem row (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (input : Fin t → Fin q → BitSource b p) (base gateBase portBase : ℕ)
    (words : Fin P → Word w) (mem : Memory w)
    (pub : ∀ i, words (extra i) = publicWords N code p b base gateBase portBase i)
    (gate : ∀ (i : Fin N.cells) (j : Fin 11), mem (gateBase+11*i.val+j.val) = record N code i j)
    (fields : ∀ (a : Fin q) j, mem (TraceAddressReader.address portBase a.val j) =
      (TraceAddressReader.fields (R a) j : Word w))
    (gateFit : gateBase+11*N.cells ≤ 2^w) (portFit : portBase+11*q ≤ 2^w)
    (safe : ∀ (v : Fin t) j, (R j).Fits w v.val)
    (addr : ∀ (v : Fin t) j, (R j).eval v.val = sourceAddress (input v j))
    (sourceFit : 2+q+N.internal < 2^w) (widthFit : N.cells < 2^w) (eleven : 11 < 2^w)
    (v : Fin t) (u : Fin N.cells) (j : Fin 11)
    (fit : recordAddress base N.cells 0 v.val u.val j.val < 2^w) :
    let a := recordAddress base N.cells 0 v.val u.val j.val
    (program w).eval words mem (fun _ => (a : Word w)) =
      record (Diagonal.GuardedNetwork.network N input TraceTemplate.empty TraceTemplate.empty)
        code (finProdFinEquiv (v,u)) j := by
  dsimp only
  rw [eval_program,keys_eq N code p b base gateBase portBase _ words mem pub]
  have hw : 0<w := by
    by_contra! z
    have e : w=0 := by omega
    simp [e] at eleven
  exact word_record N input TraceTemplate.empty TraceTemplate.empty code _
    (valid N code R input base gateBase portBase words mem _ pub gate fields gateFit portFit safe addr hw)
    base v u j sourceFit widthFit eleven fit

end ThreeFlat.RAM.FixedTraceProgram

end OAI
