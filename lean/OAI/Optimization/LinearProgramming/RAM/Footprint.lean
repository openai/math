import OAI.Optimization.LinearProgramming.RAM.Execution
import Mathlib.Algebra.Order.BigOperators.Group.List
import Lean.Elab.Tactic.Omega

/-! Quantitative finite memory bound for simulating or calling a scalar RAM program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

variable {K : Type*}

/-- Bounds all direct register addresses, jump destinations and address literals in an
instruction. Scalar literals are stored in the scalar bank and are never used as addresses. -/
def Instr.addressBudget : Instr → Nat
  | .const d _ => d
  | .copy d a | .load d a | .store d a | .addrConst d a | .addrCopy d a |
    .incr d a | .decr d a | .addrLoad d a | .addrStore d a => d+a
  | .add d a b | .sub d a b | .mul d a b | .div d a b => d+a+b
  | .branchLT a b y n | .branchAddrLT a b y n => a+b+y+n
  | .jump j | .halt j => j

def addressBudget (p : Program) : Nat := (p.map Instr.addressBudget).sum

/-- All accessible address values are bounded and both register files vanish outside the
finite memory window. -/
structure Footprint [Zero K] (B : Nat) (s : State K) : Prop where
  address : ∀ i, s.index i ≤ B
  data_zero : ∀ i, B < i → s.data i = 0
  index_zero : ∀ i, B < i → s.index i = 0

namespace Footprint

variable [Zero K] {s : State K} {B C : Nat}

theorem mono (h : Footprint B s) (hBC : B ≤ C) : Footprint C s :=
  ⟨fun i => (h.address i).trans hBC, fun i hi => h.data_zero i (hBC.trans_lt hi),
    fun i hi => h.index_zero i (hBC.trans_lt hi)⟩

theorem data_write (h : Footprint B s) {d : Nat} (hd : d ≤ B) (x : K) :
    Footprint B (s.putData d x) := by
  refine ⟨h.address, ?_, h.index_zero⟩
  intro j hj
  exact (Function.update_of_ne (by omega : j ≠ d) x s.data).trans (h.data_zero j hj)

theorem index_write (h : Footprint B s) {d x : Nat} (hd : d ≤ B) (hx : x ≤ B) :
    Footprint B (s.putIndex d x) := by
  refine ⟨?_, h.data_zero, ?_⟩
  · intro i
    by_cases hi : i = d
    · subst i
      simpa [State.putIndex] using hx
    · simpa [State.putIndex, Function.update_of_ne hi] using h.address i
  · intro i hi
    exact (Function.update_of_ne (by omega : i ≠ d) x s.index).trans (h.index_zero i hi)

theorem initial (dims : List Nat) (input : List K) (hi : input.length ≤ B)
    (hd : dims.length ≤ B) (hv : ∀ a ∈ dims, a ≤ B) : Footprint B (start dims input) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [start]
    cases e : dims[i]? with
    | none => exact Nat.zero_le _
    | some a => exact hv a (List.mem_of_getElem? e)
  · intro i h
    simp [start, List.getElem?_eq_none (by omega : input.length ≤ i)]
  · intro i h
    simp [start, List.getElem?_eq_none (by omega : dims.length ≤ i)]

end Footprint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem instr_footprint {i : Instr} {s t : State K} {B : Nat}
    (h : Footprint B s) (hi : i.addressBudget ≤ B) (ht : execInstr i s = some t) :
    Footprint (B+1) t := by
  have h' := h.mono (Nat.le_succ B)
  cases i with
  | const d q | copy d q | add d q _ | sub d q _ | mul d q _ | load d q =>
    simp only [execInstr, Option.some.injEq] at ht
    subst t
    apply h'.data_write
    simp only [Instr.addressBudget] at hi
    omega
  | div d a b =>
    by_cases hb : s.data b = 0
    · simp [execInstr, hb] at ht
    · simp [execInstr, hb] at ht
      subst t
      apply h'.data_write
      simp only [Instr.addressBudget] at hi
      omega
  | store a d =>
    simp only [execInstr, Option.some.injEq] at ht
    subst t
    exact h'.data_write (h'.address a) _
  | addrConst d n | addrCopy d n | incr d n | decr d n | addrLoad d n =>
    simp only [execInstr, Option.some.injEq] at ht
    subst t
    apply h'.index_write
    · simp only [Instr.addressBudget] at hi
      omega
    · first | exact h'.address _ | exact Nat.succ_le_succ (h.address n) |
        exact (Nat.sub_le _ _).trans (h'.address n) | (simp only [Instr.addressBudget] at hi; omega)
  | addrStore a d =>
    simp only [execInstr, Option.some.injEq] at ht
    subst t
    exact h'.index_write (h'.address a) (h'.address d)
  | branchLT a b y n | branchAddrLT a b y n | jump _ | halt _ =>
    simp only [execInstr, Option.some.injEq] at ht
    subst t
    exact ⟨h'.address, h'.data_zero, h'.index_zero⟩

/-- Indirect addressing cannot select an arbitrary location from a scalar. During a valid
step the maximum occupied address and the maximum address-register value grow by at most
one beyond the program and input bounds. -/
theorem step_footprint {p : Program} {s t : State K} {B : Nat} (hp : addressBudget p ≤ B)
    (hs : Footprint B s) (ht : step p s = some t) : Footprint (B+1) t := by
  cases he : s.output with
  | some tag => simp [step, he] at ht
  | none =>
    cases hi : p[s.pc]? with
    | none => simp [step, he, hi] at ht
    | some i =>
      have mem : i.addressBudget ∈ p.map Instr.addressBudget := List.mem_map.mpr
        ⟨i, List.mem_of_getElem? hi, rfl⟩
      obtain hsmall := List.le_sum_of_mem mem
      exact instr_footprint hs (le_trans hsmall hp) (by simpa [step, he, hi] using ht)

/-- After `i` instructions both register files fit in the first `B+i+1` cells. -/
theorem trace_footprint {p : Program} {s : State K} {B k : Nat} {t : Fin (k+1) → State K}
    (hp : addressBudget p ≤ B) (hs : Footprint B s) (ht : Trace p s k t) (i : Fin (k+1)) :
    Footprint (B+i.val) (t i) := by
  induction i using Fin.induction with
  | zero => simpa [ht.1] using hs
  | succ j ih =>
    exact step_footprint (hp.trans (Nat.le_add_right _ _)) ih (ht.2 j)

end RAM
end LinearProgramming
end Optimization
end OAI
