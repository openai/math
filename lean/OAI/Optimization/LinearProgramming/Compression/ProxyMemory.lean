import OAI.Optimization.LinearProgramming.Compression.ProxyRegisterBits
import OAI.Optimization.LinearProgramming.Compression.ProxyRelocation

/-! Transfer a bound for a small scalar bank to a caller with arbitrarily large cached
scalars. Indirect stores may target any scalar. Only the sources of reads are restricted. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ProxyMemory

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

variable {K : Type*}

/-- `a` executes with the original caller bank; `b` executes with the high bank
cleared. A modified cell agrees with the small execution, while an untouched cell
can still hold its original caller value. -/
structure Agrees (D : ℕ) (initial : ℕ → K) (a b : State K) : Prop where
  pc : a.pc = b.pc
  output : a.output = b.output
  index : a.index = b.index
  low : ∀ i < D, a.data i = b.data i
  values : ∀ i, a.data i = b.data i ∨ a.data i = initial i

def mask [Zero K] (D : ℕ) (s : State K) : State K :=
  {s with data := fun i => if i < D then s.data i else 0}

theorem mask_agrees [Zero K] (D : ℕ) (s : State K) : Agrees D s.data s (mask D s) :=
  ⟨rfl,rfl,rfl,fun i hi => by simp [mask,hi],fun _ => Or.inr rfl⟩

variable {D : ℕ} {initial : ℕ → K} {a b : State K}

private theorem Agrees.putData (h : Agrees D initial a b) (d : ℕ) (v : K) :
    Agrees D initial (a.putData d v) (b.putData d v) where
  pc := congrArg (·+1) h.pc
  output := h.output
  index := h.index
  low i hi := by
    by_cases he : i = d
    · simp [State.putData,he]
    · simpa [State.putData,Function.update_of_ne he] using h.low i hi
  values i := by
    by_cases he : i = d
    · simp [State.putData,he]
    · simpa [State.putData,Function.update_of_ne he] using h.values i

private theorem Agrees.putIndex (h : Agrees D initial a b) (d v : ℕ) :
    Agrees D initial (a.putIndex d v) (b.putIndex d v) :=
  ⟨congrArg (·+1) h.pc,h.output,by
    change Function.update a.index d v = Function.update b.index d v
    rw [h.index],h.low,h.values⟩

private theorem Agrees.setPC (h : Agrees D initial a b) (n : ℕ) :
    Agrees D initial {a with pc := n} {b with pc := n} := ⟨rfl,h.output,h.index,h.low,h.values⟩

private theorem Agrees.setTag (h : Agrees D initial a b) (n : ℕ) :
    Agrees D initial {a with output := some n} {b with output := some n} :=
  ⟨h.pc,rfl,h.index,h.low,h.values⟩

/-- All scalar operands read by the instruction are in the designated low bank. -/
def ReadsBelow (cap : ℕ) (index : ℕ → ℕ) : Instr → Prop
  | .copy _ a | .store _ a => a < cap
  | .add _ a b | .sub _ a b | .mul _ a b | .div _ a b | .branchLT a b _ _ => a < cap ∧ b < cap
  | .load _ addr => index addr < cap
  | _ => True

/-- A computable check for the directly addressed part of the read contract. -/
def directReadsBelow (cap : ℕ) : Instr → Bool
  | .copy _ a | .store _ a => decide (a < cap)
  | .add _ a b | .sub _ a b | .mul _ a b | .div _ a b | .branchLT a b _ _ =>
      decide (a < cap ∧ b < cap)
  | _ => true

theorem readsBelow_of_direct {cap : ℕ} (hle : cap ≤ D) (op : Instr) (ix : ℕ → ℕ)
    (h : directReadsBelow cap op = true)
    (hl : ∀ d a, op = .load d a → ix a < D) : ReadsBelow D ix op := by
  cases op <;> simp only [directReadsBelow,decide_eq_true_eq] at h <;> simp only [ReadsBelow]
  all_goals first | trivial | omega | exact hl _ _ rfl

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem exec_agrees (h : Agrees D initial a b) (op : Instr) (hr : ReadsBelow D a.index op)
    {t : State K} (ht : execInstr op a = some t) :
    ∃ v, execInstr op b = some v ∧ Agrees D initial t v := by
  cases op with
  | const d q => cases ht; exact ⟨_,rfl,h.putData d (q:K)⟩
  | copy d r =>
    cases ht
    exact ⟨_,rfl,by simpa only [h.low r hr] using h.putData d (b.data r)⟩
  | add d r s =>
    cases ht
    exact ⟨_,rfl,by simpa only [h.low r hr.1,h.low s hr.2] using h.putData d (b.data r+b.data s)⟩
  | sub d r s =>
    cases ht
    exact ⟨_,rfl,by simpa only [h.low r hr.1,h.low s hr.2] using h.putData d (b.data r-b.data s)⟩
  | mul d r s =>
    cases ht
    exact ⟨_,rfl,by simpa only [h.low r hr.1,h.low s hr.2] using h.putData d (b.data r*b.data s)⟩
  | div d r s =>
    by_cases hz : a.data s = 0
    · simp [execInstr,hz] at ht
    · have hz' : b.data s ≠ 0 := (h.low s hr.2) ▸ hz
      simp only [execInstr,ite_eq_right hz,Option.some.injEq] at ht
      subst t
      refine ⟨b.putData d (b.data r/b.data s),by simp [execInstr,hz'],?_⟩
      simpa only [h.low r hr.1,h.low s hr.2] using h.putData d (b.data r/b.data s)
  | load d r =>
    cases ht
    have he : a.data (a.index r) = b.data (b.index r) :=
      (h.low _ hr).trans (congrArg b.data (congrFun h.index r))
    exact ⟨_,rfl,by simpa only [he] using h.putData d (b.data (b.index r))⟩
  | store r d =>
    cases ht
    exact ⟨_,rfl,by simpa only [h.low d hr,h.index] using h.putData (b.index r) (b.data d)⟩
  | addrConst d n => cases ht; exact ⟨_,rfl,h.putIndex d n⟩
  | addrCopy d r =>
    cases ht
    exact ⟨_,rfl,by simpa only [h.index] using h.putIndex d (b.index r)⟩
  | incr d r =>
    cases ht
    exact ⟨_,rfl,by simpa only [h.index] using h.putIndex d (b.index r+1)⟩
  | decr d r =>
    cases ht
    exact ⟨_,rfl,by simpa only [h.index] using h.putIndex d (b.index r-1)⟩
  | addrLoad d r =>
    cases ht
    exact ⟨_,rfl,by simpa only [h.index] using h.putIndex d (b.index (b.index r))⟩
  | addrStore r d =>
    cases ht
    exact ⟨_,rfl,by simpa only [h.index] using h.putIndex (b.index r) (b.index d)⟩
  | branchLT r s yes no =>
    cases ht
    refine ⟨_,rfl,?_⟩
    simpa only [h.low r hr.1,h.low s hr.2] using h.setPC (if b.data r < b.data s then yes else no)
  | branchAddrLT r s yes no =>
    cases ht
    exact ⟨_,rfl,by simpa only [h.index] using h.setPC (if b.index r < b.index s then yes else no)⟩
  | jump n => cases ht; exact ⟨_,rfl,h.setPC n⟩
  | halt n => cases ht; exact ⟨_,rfl,h.setTag n⟩

/-- Every execution prefix can be matched by a same-length execution from the masked
bank, including its address registers, control flow, and all computed scalar cells. -/
theorem run_agrees {p : Program} (h : Agrees D initial a b)
    (safe : ∀ j u, runExactly p a j = some u → ∀ op, p[u.pc]? = some op → ReadsBelow D u.index op)
    {n : ℕ} {t : State K} (ht : runExactly p a n = some t) :
    ∃ v, runExactly p b n = some v ∧ Agrees D initial t v := by
  induction n generalizing t with
  | zero => change some a = some t at ht; cases ht; exact ⟨b,rfl,h⟩
  | succ n ih =>
    change (runExactly p a n).bind (step p) = some t at ht
    cases hu : runExactly p a n with
    | none => simp [hu] at ht
    | some u =>
      have hs : step p u = some t := by simpa [hu] using ht
      obtain ⟨v,hv,huv⟩ := ih hu
      cases ho : u.output with
      | some tag => simp [step,ho] at hs
      | none =>
        cases hop : p[u.pc]? with
        | none => simp [step,ho,hop] at hs
        | some op =>
          have hex : execInstr op u = some t := by simpa [step,ho,hop] using hs
          obtain ⟨w,hw,hrel⟩ := exec_agrees huv op (safe n u hu op hop) hex
          refine ⟨w,?_,hrel⟩
          change (runExactly p b n).bind (step p) = some w
          rw [hv,Option.bind_some]
          simpa [step,← huv.output,ho,← huv.pc,hop] using hw

/-- A new write has the size bound of the masked execution; a surviving initial
value remains within its original caller bound. This maximum stays stable under repeated
subroutine calls with a cleared low bank. -/
theorem transfer_bound {p : Program} {D B H C : ℕ} (s : State ℚ) (hB : 3 ≤ B)
    (hlow : ∀ i < D, ratBits (s.data i) ≤ B) (hglobal : scalarBound H s)
    (safe : ∀ j u, runExactly p s j = some u → ∀ op, p[u.pc]? = some op → ReadsBelow D u.index op)
    (bound : scalarBound B (mask D s) →
      ∀ j u, runExactly p (mask D s) j = some u → scalarBound C u)
    {n : ℕ} {t : State ℚ} (ht : runExactly p s n = some t) : scalarBound (max H C) t := by
  have hb : scalarBound B (mask D s) := by
    intro i
    by_cases hi : i < D
    · simpa [mask,hi] using hlow i hi
    · simpa [mask,hi,show ratBits 0 = 3 by decide] using hB
  obtain ⟨v,hv,hrel⟩ := run_agrees (mask_agrees D s) safe ht
  intro j
  rcases hrel.values j with he | he
  · rw [he]
    exact (bound hb n v hv j).trans (le_max_right _ _)
  · rw [he]
    exact (hglobal j).trans (le_max_left _ _)

end ProxyMemory
end Compression
end LinearProgramming
end Optimization
end OAI
