import OAI.Optimization.LinearProgramming.Recovery.OddBoundary
import OAI.Optimization.LinearProgramming.BitRAM.NativePriceEpoch
import OAI.Optimization.LinearProgramming.BitRAM.IndexScript

/-! Restarting clears the learner and rebuilds the exact polynomial-length input
word while leaving every scalar and address of the numerical service untouched. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG

open RAM RAM.Callable OracleSpec BitRAM

structure Ports {n : ℕ} (anchor : Fin n) (wordBase : ℕ) {K : Type*} (m : Memory K) : Prop where
  send : 3 ≤ m.index sendBaseReg
  columns : m.index 50=n
  index : m.index 51=anchor.val
  packet : m.index 52=wordBase

protected theorem Ports.preserve {n wordBase : ℕ} {anchor : Fin n} {K : Type*} {a t : Memory K}
    (source : Ports anchor wordBase a) (frame : StableHeaders a t) : Ports anchor wordBase t :=
  ⟨(frame sendBaseReg (by decide) (by decide)).symm ▸ source.send,
    (frame 50 (by decide) (by decide)).trans source.columns,
    (frame 51 (by decide) (by decide)).trans source.index,
    (frame 52 (by decide) (by decide)).trans source.packet⟩

private def ops : List Instr := [.addrCopy 72 50,.addrCopy 74 51,.addrCopy 76 52,.addrConst statusReg 0]

noncomputable def resetEpoch (p : BitProgram) (B : Polynomial ℕ) : Fragment :=
  Odd.leaf (.seq (.straight ops) (PriceEpoch.initializeEpoch p B))

noncomputable def resetTime (p : BitProgram) (B : Polynomial ℕ) (n : ℕ) := 4*(4+(PriceEpoch.epochPolynomial p B).eval n)

theorem resetEpoch_run {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K→Prop}
    (p : BitProgram) (B : Polynomial ℕ) {n wordBase : ℕ} (anchor : Fin n) (native vm : Memory K)
    (ports : Ports anchor wordBase vm) (base : 3 ≤ wordBase) (good : native.AllData P)
    (safe : vm.AllData P) (zero : P 0) (one : P 1) :
    ∃ t,(resetEpoch p B).Run P (Odd.memory native vm) (resetTime p B n) (Odd.memory native t) ∧
      Rep p (p.initial (priceInput (2^(1+B.eval n)) anchor)) t ∧ Ports anchor wordBase t ∧ t.index statusReg=0 := by
  let a : Memory K:=⟨vm.data,IndexScript.run ops vm.index⟩
  have pre : Block.Eval (Memory.AllData P) (.straight ops) vm 4 a :=
    IndexScript.correct ops (by simp [ops,IndexScript.allowed]) vm safe
  have m72 : a.index 72=n := ports.columns
  have m74 : a.index 74=anchor.val := ports.index
  have m76 : a.index 76=wordBase := ports.packet
  have policy : RAM.Tape.Good P = Memory.AllData P := rfl
  have ready : RAM.Tape.Good P a := (congrFun policy a).mpr pre.safe_end
  obtain ⟨k,hk,t,boot,rep,effect⟩:=PriceEpoch.initializeEpoch_correct p B anchor a ready zero one m72 m74 (m76.symm ▸ base)
  have bootRun : Block.Eval (Memory.AllData P) (PriceEpoch.initializeEpoch p B) a k t :=
    Eq.mp (congrArg (fun Q : Memory K→Prop => Block.Eval Q (PriceEpoch.initializeEpoch p B) a k t) policy) boot
  have preserved (i : ℕ) (lo : 43 ≤ i) (hi : i < 65) (ne : i≠recvLenReg) (other : i≠recvBaseReg) : t.index i=a.index i :=
    (effect.headers i lo hi ne).trans (Memory.putIndex_ne _ other _)
  have stable : Ports anchor wordBase t := by
    refine ⟨?_,(preserved 50 (by decide) (by decide) (by decide) (by decide)).trans ports.columns,
      (preserved 51 (by decide) (by decide) (by decide) (by decide)).trans ports.index,
      (preserved 52 (by decide) (by decide) (by decide) (by decide)).trans ports.packet⟩
    rw [preserved sendBaseReg (by decide) (by decide) (by decide) (by decide)]
    exact ports.send
  have tag : t.index statusReg=0 := (preserved statusReg (by decide) (by decide) (by decide) (by decide)).trans rfl
  exact ⟨t,(Odd.leaf_run P native good (pre.seq bootRun)).mono (by unfold resetTime;omega),rep,stable,tag⟩

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
