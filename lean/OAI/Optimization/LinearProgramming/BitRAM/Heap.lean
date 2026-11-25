import OAI.Optimization.LinearProgramming.RAM.Loops
import OAI.Optimization.LinearProgramming.OracleSpec.Machine
import Lean.Elab.Tactic.Omega

/-! Linked binary stacks in the address bank of the ordinary RAM. Nodes are immutable.
Odd storage addresses let a numeric subroutine run in the even register frame. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

variable {K : Type*}

open RAM OracleSpec

def nilReg := 31
def freeReg := 33
def bufferReg := 35
def bufferLenReg := 37
def stateReg := 39
def askReg := 41
def sendBaseReg := 43
def recvBaseReg := 47
def recvLenReg := 49

abbrev Slot (p : BitProgram) := Option (Fin p.stackCount)

def headReg {n : Nat} : Option (Fin n) → Nat
  | none => bufferReg
  | some i => 65+2*i.val

def heapStart (p : BitProgram) := 65+2*p.stackCount

def bitNat (b : Bool) := if b then 1 else 0

def bitScalar [Zero K] [One K] (b : Bool) : K := if b then 1 else 0

def topTag : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

def pcCode {n : Nat} (pc : Option (Fin n)) := pc.elim n Fin.val

def contents {p : BitProgram} (c : p.Config) : Slot p → Word
  | none => c.bufferRev
  | some i => c.store i

theorem headReg_injective {n : Nat} : Function.Injective (@headReg n) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => change 35 = 65+2*j.val at h; omega
  | some i =>
    cases j with
    | none => simp [headReg,bufferReg] at h; omega
    | some j => congr 1; apply Fin.ext; simp [headReg] at h; omega

theorem headReg_range (p : BitProgram) (slot : Slot p) :
    35 ≤ headReg slot ∧ headReg slot < heapStart p ∧ headReg slot % 2 = 1 := by
  cases slot with
  | none => simp [headReg,bufferReg,heapStart]; omega
  | some i => simp [headReg,heapStart]; omega

/-- A word is an actual linked path, including the empty pointer and both physical fields.
`lo` is above the static stack heads; `[lo, hi)` covers allocated cells. -/
inductive Chain (addr : Nat → Nat) (lo hi : Nat) : Nat → Word → Prop where
  | nil : Chain addr lo hi 0 []
  | cons {ptr b bs} : lo ≤ ptr → ptr+2 < hi → ptr % 2 = 1 → addr (ptr+2) = bitNat b →
      Chain addr lo hi (addr ptr) bs → Chain addr lo hi ptr (b::bs)

namespace Chain

/-- Replacing address memory outside old node fields and enlarging the heap preserves all words. -/
theorem transport {a a' : Nat → Nat} {lo hi hi' ptr : Nat} {w : Word} (h : Chain a lo hi ptr w)
    (lim : hi ≤ hi') (same : ∀ i, lo ≤ i → i < hi → i%2=1 → a' i = a i) :
    Chain a' lo hi' ptr w := by
  induction h with
  | nil => exact .nil
  | @cons p b bs hlow hhigh hodd hb ht ih =>
    refine .cons hlow (hhigh.trans_le lim) hodd ?_ ?_
    · exact (same (p+2) (by omega) hhigh (by omega)).trans hb
    · rw [same p hlow (by omega) hodd]; exact ih

theorem empty_iff {a : Nat → Nat} {lo hi ptr : Nat} {w : Word} (h : Chain a lo hi ptr w)
    : ptr = 0 ↔ w = [] := by
  cases h with
  | nil => simp
  | cons hlow _ _ _ _ => simp; omega

theorem top {a : Nat→Nat} {lo hi ptr : Nat} {w : Word} (h : Chain a lo hi ptr w)
    : topTag w.head? = if ptr = 0 then 0 else a (ptr+2) + 1 := by
  cases h with
  | nil => rfl
  | @cons p b bs hlow _ _ hb _ =>
    have hp : ptr ≠ 0 := by omega
    cases b <;> simp [topTag,hp,hb,bitNat]

theorem tail {a : Nat→Nat} {lo hi ptr : Nat} {w : Word} (h : Chain a lo hi ptr w)
    : Chain a lo hi (if ptr=0 then 0 else a ptr) w.tail := by
  cases h with
  | nil => exact .nil
  | @cons p b bs hlow _ _ _ ht => simpa [show ptr ≠ 0 by omega] using ht

end Chain

/-- The finite binary stacks include the reverse pending output buffer at slot `none`. -/
structure HeapRep (p : BitProgram) (w : Slot p → Word) (m : Memory K) : Prop where
  nilValue : m.index nilReg = 0
  freeLower : heapStart p ≤ m.index freeReg
  freeOdd : m.index freeReg % 2 = 1
  chain : ∀ slot, Chain m.index (heapStart p) (m.index freeReg) (m.index (headReg slot)) (w slot)

/-- At an instruction boundary the pending request has its actual bit length. The transcript
is ghost state shared with the oracle and is inaccessible to the simulated controller. -/
structure Rep (p : BitProgram) (c : p.Config) (m : Memory K) : Prop where
  heap : HeapRep p (contents c) m
  bufferLength : m.index bufferLenReg = c.bufferRev.length
  stateCode : m.index stateReg = pcCode c.pc
  askReady : m.index askReg = 0

namespace HeapRep

theorem of_odd_eq {p : BitProgram} {w : Slot p → Word} {m t : Memory K} (h : HeapRep p w m)
    (eqv : ∀ i, 31 ≤ i → i%2=1 → t.index i=m.index i) : HeapRep p w t := by
  have hf := eqv freeReg (by decide) (by decide)
  refine ⟨(eqv nilReg (by decide) (by decide)).trans h.nilValue,hf ▸ h.freeLower,hf ▸ h.freeOdd,?_⟩
  intro s
  have hs := headReg_range p s
  rw [hf,eqv _ (by omega) hs.2.2]
  apply (h.chain s).transport le_rfl
  intro j low _ odd
  exact eqv j (by unfold heapStart at low; omega) odd

theorem putScratch {p : BitProgram} {w : Slot p → Word} {m : Memory K} (h : HeapRep p w m)
    {i : Nat} (hi : i < 31) (v : Nat) : HeapRep p w (m.putIndex i v) := by
  apply h.of_odd_eq
  intro j hj _
  exact Function.update_of_ne (by omega) _ _

/-- Header and scratch updates leave the heap alone if they change neither a head nor allocator. -/
theorem putOther {p : BitProgram} {w : Slot p → Word} {m : Memory K} (h : HeapRep p w m)
    (i val : Nat) (low : i < heapStart p) (hn : i ≠ nilReg) (hf : i ≠ freeReg)
    (hs : ∀ s : Slot p, i ≠ headReg s) : HeapRep p w (m.putIndex i val) := by
  have free : (m.putIndex i val).index freeReg = m.index freeReg := Function.update_of_ne hf.symm _ _
  refine ⟨(Function.update_of_ne hn.symm _ _).trans h.nilValue,free ▸ h.freeLower,free ▸ h.freeOdd,?_⟩
  intro s
  rw [free,Memory.putIndex_ne _ (hs s).symm]
  apply (h.chain s).transport le_rfl
  intro j hj _ _
  exact Function.update_of_ne (by omega) _ _

end HeapRep

namespace Rep

theorem of_odd_eq {p : BitProgram} {c : p.Config} {m t : Memory K} (h : Rep p c m)
    (eqv : ∀ i, 31 ≤ i → i%2=1 → t.index i=m.index i) : Rep p c t :=
  ⟨h.heap.of_odd_eq eqv,(eqv _ (by decide) (by decide)).trans h.bufferLength,
    (eqv _ (by decide) (by decide)).trans h.stateCode,(eqv _ (by decide) (by decide)).trans h.askReady⟩

theorem putScratch {p : BitProgram} {c : p.Config} {m : Memory K} (h : Rep p c m)
    {i : Nat} (hi : i < 31) (v : Nat) : Rep p c (m.putIndex i v) := by
  apply h.of_odd_eq
  intro j hj _
  exact Function.update_of_ne (by omega) _ _

end Rep
end BitRAM
end LinearProgramming
end Optimization
end OAI
