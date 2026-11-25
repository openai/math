import OAI.Optimization.LinearProgramming.RAM.CallableLPBoot
import OAI.Optimization.LinearProgramming.RAM.CallableDecision
import OAI.Optimization.LinearProgramming.RAM.CallableScopedRun

/-! Ordinary two-dimensional input to a decision-running fragment. The bootstrap, relocatable body,
final test, and data-dependent halt execute as one fixed native ROM. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Polynomial

/-- The final guard can inspect its own two physical registers, even when the body
never reads either one. Code addresses have no bearing on this finite memory floor. -/
def publicOperandBound (f : Fragment) (c : Cond) : ℕ := max f.localBudget c.accessBudget

def publicDecision (len : Tape.AddressTerm 2) (f : Fragment) (c : Cond) (yes no C E : ℕ) : Program :=
  let target := lpTimeFloor (publicOperandBound f c) C E
  (Fragment.seq (Fragment.ofBlock (twoDimBoot len target)) f).decisionProgram c yes no

noncomputable def publicDecisionTime (len : Tape.AddressTerm 2) (f : Fragment) (c : Cond) (coef exp : ℕ) : Polynomial ℕ :=
  twoDimBootPolynomial len (lpTimeFloor (publicOperandBound f c) coef exp) +
    Polynomial.C coef*(X+1)^exp+2

/-- The LP packet contains a row-major matrix followed by the right-hand side. -/
def publicLPDecision (f : Fragment) (c : Cond) (yes no C E : ℕ) : Program :=
  publicDecision lpLength f c yes no C E

noncomputable def publicLPDecisionTime (f : Fragment) (c : Cond) (coef exp : ℕ) : Polynomial ℕ :=
  publicDecisionTime lpLength f c coef exp

private theorem guard_trim {K : Type*} [LT K] [DecidableLT K] (c : Cond) (out : Memory K) {cap : ℕ}
    (h : c.accessBudget≤cap) : c.test (trimMemory cap out)=c.test out := by
  cases c with
  | scalarLT a b => rfl
  | addrLT a b =>
    change a+b≤cap at h
    simp [Cond.test,trimMemory,show a≤cap by omega,show b≤cap by omega]

/-- A relocatable logical solver with a polynomial running time gives a conventional
finite-input native program with the exact same decision and the entire final scalar
register file. All scalar intermediates in the initializer and body satisfy `P`. -/
theorem publicDecision_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (len : Tape.AddressTerm 2) (f : Fragment) [Fragment.FixedAccess f] (c : Cond) (yes no C E m d : ℕ) (xs : List K)
    (P : K → Prop) (out : Memory K) (hlen : xs.length=len.value (dimensions m d))
    (hs : ((start [m,d] xs).memory).AllData P) (hz : P 0)
    (run : f.Run P (Odd.memory (start [] ([] : List K)).memory (start [m,d] xs).memory)
      (polyBound C E (m+d)) out) :
    ∃ k≤(publicDecisionTime len f c C E).eval (m+d), ∃ tr : Fin (k+1) → State K,
      Trace (publicDecision len f c yes no C E) (start [m,d] xs) k tr ∧
      (tr (Fin.last k)).output=some (if c.test out then yes else no) ∧
      (tr (Fin.last k)).data=out.data ∧ ∀i j,P ((tr i).data j) := by
  let B := publicOperandBound f c
  let floor := lpTimeFloor B C E
  let cap := twoDimCap len floor m d
  let base := max B (2*(m+d)+1)
  let init := Odd.memory (start [] ([] : List K)).memory (start [m,d] xs).memory
  have bound : base+(polyBound C E (m+d)+2)≤cap := by
    have h := (twoDimCap_bounds len (lpTimeFloor B C E) m d).1
    rw [lpTimeFloor_value] at h
    dsimp only [base,cap,floor]
    omega
  have hi (j : ℕ) : init.index j≤base := by
    have h := Odd.initial_index_bound [] [m,d] ([] : List K) xs j
    apply le_trans _ (le_max_right B _)
    simpa [init] using h
  have scope : f.Scoped base := (Fragment.scoped_localBudget f).mono
    ((le_max_left _ _).trans (le_max_left B _))
  have clipped := run.trim scope hi (by omega : base+polyBound C E (m+d)≤cap)
  obtain ⟨l,hl,boot⟩ := twoDimBoot_correct len floor P m d xs hlen hs hz
  have packed : (start (Odd.finiteDims cap [] [m,d]) (Odd.finiteScalars [] xs)).memory=trimMemory cap init :=
    congrArg State.memory (Odd.start_finite cap [] [m,d] ([] : List K) xs)
  have prefixRun := (Fragment.Run.ofBlock boot).mono hl
  change (Fragment.ofBlock (twoDimBoot len floor)).Run P (start [m,d] xs).memory _
    (start (Odd.finiteDims cap [] [m,d]) (Odd.finiteScalars [] xs)).memory at prefixRun
  rw [packed] at prefixRun
  obtain ⟨k,hk,tr,ht,ho,hm,safe⟩ := Fragment.run_decision (prefixRun.seq clipped) c yes no
  have hg : c.accessBudget≤cap := (le_max_right _ _).trans ((le_max_left B _).trans (by omega : base≤cap))
  rw [guard_trim c out hg] at ho
  refine ⟨k,?_,tr,ht,ho,congrArg Memory.data hm,safe⟩
  simpa only [publicDecisionTime,eval_add,eval_mul,eval_C,eval_pow,eval_X,eval_one,eval_ofNat,polyBound] using hk


/-- Specialize the uniform two-dimensional entry theorem to ordinary LP inputs. -/
theorem publicLPDecision_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Fragment) [Fragment.FixedAccess f] (c : Cond) (yes no C E m d : ℕ) (xs : List K)
    (P : K → Prop) (out : Memory K) (hlen : xs.length=m*d+m)
    (hs : ((start [m,d] xs).memory).AllData P) (hz : P 0)
    (run : f.Run P (Odd.memory (start [] ([] : List K)).memory (start [m,d] xs).memory)
      (polyBound C E (m+d)) out) :
    ∃ k≤(publicLPDecisionTime f c C E).eval (m+d), ∃ tr : Fin (k+1) → State K,
      Trace (publicLPDecision f c yes no C E) (start [m,d] xs) k tr ∧
      (tr (Fin.last k)).output=some (if c.test out then yes else no) ∧
      (tr (Fin.last k)).data=out.data ∧ ∀i j,P ((tr i).data j) := by
  exact publicDecision_correct lpLength f c yes no C E m d xs P out
    (by simpa only [lpLength_value] using hlen) hs hz run

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
