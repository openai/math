import OAI.Optimization.LinearProgramming.RAM.CallableControl
import OAI.Optimization.LinearProgramming.NormalSubspace.OuterHeader
import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf
import OAI.Optimization.LinearProgramming.RAM.CallablePrepare
import OAI.Optimization.LinearProgramming.RAM.CallableTwoBoot
import OAI.Optimization.LinearProgramming.RAM.CallableLocalRun
import OAI.Optimization.LinearProgramming.Recovery.NumericCall

/-! Install a second finite subspace frame and retain the outer VM's original
input. Each copy and both register-bank crossings are ordinary RAM operations. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

open RAM RAM.Callable RAM.Tape Polynomial

/-- The caller holds the source arrays on odd registers. After staging their
ordinary copy on even registers, run the complete finite two-dimensional boot
as a normal numerical subroutine of that caller. -/
def outerStage (floor : AddressTerm 2) : Fragment :=
  .seq (Odd.leaf outerHeader) (.seq (.ofBlock prepareInputs)
    (Recovery.PackedPCG.numericCall (.ofBlock (Boot.twoDimBoot subspaceLength floor))))

noncomputable def outerStageTime (floor : AddressTerm 2) : Polynomial ℕ :=
  4*outerHeaderTime+19*(X^2+3)+225+2*(Boot.twoDimBootPolynomial subspaceLength floor+1)+2

theorem subspaceLength_value (r c : ℕ) :
    subspaceLength.value (Boot.dimensions r c)=(r+c)^2 := by
  change (r+c)*(r+c)=(r+c)^2
  rw [pow_two]

/-- The inner address bank equals its finite implementation on return. The
retained VM data and its bound on *all* address registers are independent of
which finite floor the caller selected for the inner computation. -/
theorem outerStage_run {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (floor : AddressTerm 2) (r c : ℕ) (xs : List K) (P : K→Prop)
    (length : xs.length=(r+c)^2) (safe : (start [r,c] xs).memory.AllData P) (zeroSafe : P 0) :
    let raw := (start [r,c] xs).memory
    let zero := (start [] ([]:List K)).memory
    let cap := Boot.twoDimCap subspaceLength floor r c
    ∃ vm, (outerStage floor).Run P (Odd.memory zero raw) ((outerStageTime floor).eval (r+c))
      (Odd.memory (trimMemory cap (Odd.memory zero raw)) vm) ∧ vm.data=raw.data ∧
      vm.index 43=3 ∧ vm.index 45=0 ∧ vm.index 50=r+c ∧ vm.index 51=0 ∧ vm.index 52=3 ∧
      ∀ j,vm.index j≤outerVMAddresses.eval (r+c) := by
  let raw := (start [r,c] xs).memory
  let zero := (start [] ([]:List K)).memory
  let cap := Boot.twoDimCap subspaceLength floor r c
  let B := (r+c)^2+3
  have empty : zero.AllData P := fun i => by simpa [zero,start,State.memory] using zeroSafe
  have foot : Footprint 0 (start [] ([]:List K)) := Footprint.initial _ _ (by simp) (by simp) (by simp)
  obtain ⟨u,k,header,headerTime,data,ptr,addresses⟩ := outerHeader_correct r c xs P safe
  have first := Odd.leaf_run P zero empty header
  obtain ⟨l,prepTime,prepare⟩ := prepareInputs_native (start [] ([]:List K)) u 0 0 0 B xs [r,c]
    (ptr.rawTapes data length) header.safe_end empty zeroSafe foot (by dsimp [B];omega)
    (by dsimp [B];omega) (by change 2≤(r+c)^2+3;omega)
  obtain ⟨b,bootTime,boot⟩ := Boot.twoDimBoot_correct subspaceLength floor P r c xs
    (length.trans (subspaceLength_value r c).symm) safe zeroSafe
  have target : (start (Odd.finiteDims cap [] [r,c]) (Odd.finiteScalars [] xs)).memory=
      trimMemory cap (Odd.memory zero raw) :=
    congrArg State.memory (Odd.start_finite cap [] [r,c] [] xs)
  have inner : (Fragment.ofBlock (Boot.twoDimBoot subspaceLength floor)).Run P raw b
      (trimMemory cap (Odd.memory zero raw)) := by
    rw [←target];exact Fragment.Run.ofBlock boot
  have finish := Recovery.PackedPCG.numericCall_run inner u header.safe_end
  refine ⟨u.putIndex 1 0,?_,data,?_,?_,?_,?_,?_,?_⟩
  · apply (first.seq ((Fragment.Run.ofBlock prepare).seq finish)).mono
    simp only [outerStageTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    dsimp only [B] at prepTime
    omega
  · simpa using ptr.node
  · simpa using ptr.first
  · simpa using ptr.dimension
  · simpa using ptr.offset
  · simpa using ptr.root
  · intro j
    by_cases eq : j=1
    · subst j;simp
    · simpa [Memory.putIndex,eq] using addresses j

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
