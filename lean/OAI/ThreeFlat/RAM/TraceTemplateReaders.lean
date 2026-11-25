import OAI.ThreeFlat.RAM.TraceAddressExpr
import OAI.ThreeFlat.RAM.GuardedDescriptorRecord

namespace OAI
/-! # Two ROM readers for every copy of a fixed local trace gate table -/

namespace ThreeFlat.RAM.TraceTemplate

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr GuardedDescriptor BitLayout Diagonal.TraceAddressRecord
open scoped Fin.CommRing
variable {F : Type*} [CommSemiring F] {w k q n t b p : ℕ}

/-- Eleven consecutive words per local cell, with arbitrary indices outside
the public template set to zero. -/
def localWord (N : BitNetwork F q) (code : FieldCode F w) (a : ℕ) : Word w :=
  if h : a/11 < N.cells then record N code ⟨_,h⟩ ⟨a%11,Nat.mod_lt _ (by decide)⟩ else 0

omit [CommSemiring F] in
theorem localWord_at (N : BitNetwork F q) (code : FieldCode F w) (u : Fin N.cells) (j : Fin 11) :
    localWord N code (11*u.val+j.val) = record N code u j := by
  have eq : (11*u.val+j.val)/11 = u.val := by
    simp [Nat.mul_add_div (by decide : 0<11),Nat.div_eq_of_lt j.isLt]
  have rem : (11*u.val+j.val)%11 = j.val := by simp [Nat.mod_eq_of_lt j.isLt]
  simp [localWord,eq,rem,u.isLt]

/-- The compiler supplies the column then the local cell at the front of
the callback environment. The local gate table has no row-number argument. -/
def copy (N : BitNetwork F q) (code : FieldCode F w) : Term w k (n+3) :=
  LiteralTable.atIndex (localWord N code) (11*N.cells)
    (.binary .add (.binary .mul (.literal 11) (.result 1)) (.result 0))

def getRecord (R : Fin q → Record) (a : ℕ) : Record :=
  if h : a<q then R ⟨a,h⟩ else {}

/-- Each alternative has at most forty lets, regardless of the number of
physical rows. Input zero selects the local port and input one is the row. -/
def pin (R : Fin q → Record) : Term w k (n+2) :=
  LiteralTable.dispatch 0 (fun a => (TraceAddressExpr.program (getRecord R a)).rename (fun _ => 1)) q

def callbacks (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record) :
    Lookups w k n := ⟨copy N code,pin R,.literal 0,.literal 0⟩

omit [CommSemiring F] in
theorem copy_binds (N : BitNetwork F q) (code : FieldCode F w) :
    (copy (n:=n) (k:=k) N code).binds = 33*N.cells+4 := by
  simp [copy,Term.literal,Term.binary,Term.binds]
  omega

theorem pin_binds (R : Fin q → Record) : (pin (n:=n) (w:=w) (k:=k) R).binds ≤ 42*q+1 := by
  exact LiteralTable.dispatch_binds _ _ _ 40 (fun a _ => by
    simp only [Term.binds_rename]; exact TraceAddressExpr.program_binds _)

def readers (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin n → Word w) : Readers w where
  copy := fun v i j => (copy N code).eval words mem (Fin.cons j (Fin.cons i (Fin.cons v vs)))
  pin := fun v i => (pin R).eval words mem (Fin.cons i (Fin.cons v vs))
  left := fun _ _ => 0
  right := fun _ _ => 0

def empty (_i : Fin t) : Fin 0 → BitSource b p := Fin.elim0

omit [CommSemiring F] in
theorem reads (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (input : Fin t → Fin q → BitSource b p) (hw : 0<w) (small : 11*N.cells ≤ 2^w)
    (ports : q≤2^w) (fit : ∀ (i : Fin t) j, (R j).Fits w i.val)
    (addr : ∀ (i : Fin t) j, (R j).eval i.val = sourceAddress (input i j))
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin n → Word w) :
    Reads (readers N code R words mem vs) N input empty empty code := by
  constructor
  · intro i u j
    change (copy N code).eval _ _ _ = _
    rw [copy,LiteralTable.atIndex_eval (i:=11*u.val+j.val)]
    · exact localWord_at _ _ _ _
    · have h := u.isLt
      have hj := j.isLt
      omega
    · exact small
    · simp [Term.eval,BinaryOp.eval]
  · intro i j
    change (pin R).eval _ _ _ = _
    rw [pin, LiteralTable.dispatch_eval (x:=j.val) (hx:=j.isLt) (hs:=ports) (arg:=by simp)]
    simp only [Term.eval_rename,getRecord,j.isLt,↓reduceDIte]
    rw [TraceAddressExpr.program_eval _ hw (fit i j) _ _ _ (by simp), addr]
  · exact fun _ j => j.elim0
  · exact fun _ j => j.elim0

end ThreeFlat.RAM.TraceTemplate

end OAI
