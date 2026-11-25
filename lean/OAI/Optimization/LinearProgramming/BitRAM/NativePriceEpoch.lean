import OAI.Optimization.LinearProgramming.BitRAM.NativePriceFields
import OAI.Optimization.LinearProgramming.BitRAM.AddressHorner
import OAI.Optimization.LinearProgramming.Compression.MetadataFinish
import OAI.Optimization.LinearProgramming.BitRAM.NativeInstall

/-! Start or restart the LP price-game bit machine from the dimension, current anchor,
and scratch-window pointer supplied by the outer arithmetic RAM. The exponent polynomial
is evaluated natively. Its power of two is emitted directly in binary. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace PriceEpoch
open RAM RAM.Block RAM.Tape OracleSpec Compression Compression.Inner.Metadata Polynomial

/-- Given the receive base already in 47, write the precise three-field epoch packet. -/
noncomputable def packetEncoder (B : Polynomial Nat) : Block := .seq (AddressHorner.block 72 B)
  (.seq initializeBlock fields)

noncomputable def packetPolynomial (B : Polynomial Nat) : Polynomial Nat := AddressHorner.timePolynomial B + 6 +
  (2*((X+1)*(5*X+25)+5)+10*B+18)

theorem packetPolynomial_eval (B : Polynomial Nat) (n : Nat) : (packetPolynomial B).eval n=
    (AddressHorner.timePolynomial B).eval n+6+fieldsTime n (B.eval n) := by
  simp [packetPolynomial,fieldsTime]

/-- Caller-owned even addresses 72, 74, and 76 hold `N`, the anchor and the selected
scalar window; the application can choose a new address or anchor at every epoch. -/
noncomputable def initializeEpoch (p : BitProgram) (B : Polynomial Nat) : Block :=
  .seq (.op (.addrCopy 47 76)) (installControlInput p (packetEncoder B))

noncomputable def epochPolynomial (p : BitProgram) (B : Polynomial Nat) : Polynomial Nat :=
  1+packetPolynomial B+(18*(4*X+2*B+7)+C p.stackCount+12)

theorem epochPolynomial_eval (p : BitProgram) (B : Polynomial Nat) (n : Nat) : (epochPolynomial p B).eval n=
    1+(packetPolynomial B).eval n+(18*(4*n+2*B.eval n+7)+p.stackCount+12) := by
  simp [epochPolynomial]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K→Prop}

theorem packetEncoder_correct (B : Polynomial Nat) {n : Nat} (anchor : Fin n) (s : Memory K) (safe : Good P s)
    (zero : P 0) (one : P 1) (dim : s.index 72=n) (mark : s.index 74=anchor.val) (base : 3≤s.index 47) :
    ∃ t k, Eval (Good P) (packetEncoder B) s k t ∧ k≤(packetPolynomial B).eval n ∧
      MetadataEffect s t (priceInput (2^(1+B.eval n)) anchor) := by
  obtain ⟨j,a,poly,jb,bval,ad,ah⟩ := AddressHorner.block_eval 72 B n s safe dim
  obtain ⟨u,init,started⟩ := initialize_correct a poly.safe_end zero one (by rw [ah _ (by decide)]; exact base)
  have un : u.index 72=n := (started.frame _ (by decide) (by decide) (by decide) (by decide)).trans ((ah _ (by decide)).trans dim)
  have ua : u.index 74=anchor.val := (started.frame _ (by decide) (by decide) (by decide) (by decide)).trans ((ah _ (by decide)).trans mark)
  have ub : u.index 8=B.eval n := (started.frame _ (by decide) (by decide) (by decide) (by decide)).trans bval
  obtain ⟨t,k,emit,kb,ef⟩ := fields_correct anchor _ u init.safe_end started.ready un ua ub
  have fx := started.finish ef
  have loc : a.index recvBaseReg=s.index recvBaseReg := ah _ (by decide)
  refine ⟨t,_,poly.seq (init.seq emit),?_,⟨?_,fx.length,?_,?_,?_⟩⟩
  · rw [packetPolynomial_eval]; omega
  · rw [←loc]; exact fx.packet
  · intro i low high ne
    exact (fx.headers i low high ne).trans (ah i (by omega))
  · intro i low ev
    exact (fx.even i low ev).trans (ah i (by omega))
  · intro i low away
    exact (fx.data i low (by simpa only [loc] using away)).trans (congrFun ad i)

/-- Normal-entry and restart theorem. The saved numerical state receives the same
protected-index and scalar outside-window guarantees as the metadata encoder. -/
theorem initializeEpoch_correct (p : BitProgram) (B : Polynomial Nat) {n : Nat} (anchor : Fin n) (s : Memory K)
    (safe : Good P s) (zero : P 0) (one : P 1) (dim : s.index 72=n) (mark : s.index 74=anchor.val)
    (base : 3≤s.index 76) :
    ∃ k≤(epochPolynomial p B).eval n, ∃ t, Eval (Good P) (initializeEpoch p B) s k t ∧
      Rep p (p.initial (priceInput (2^(1+B.eval n)) anchor)) t ∧
      MetadataEffect (s.putIndex 47 (s.index 76)) t (priceInput (2^(1+B.eval n)) anchor) := by
  let a := s.putIndex 47 (s.index 76)
  have setBase : Eval (Good P) (.op (.addrCopy 47 76)) s 1 a := eval_copyI s safe 47 76
  have abase : 3≤a.index 47 := by simp [a,base]
  obtain ⟨u,j,write,jb,effect⟩ := packetEncoder_correct B anchor a setBase.safe_end zero one
    (by simpa [a] using dim) (by simpa [a] using mark) abase
  obtain ⟨t,load,rep,final⟩ := installControlInput_correct (p:=p) write effect zero abase
  have length := word_length anchor (B.eval n)
  refine ⟨_,?_,t,setBase.seq load,rep,final⟩
  rw [epochPolynomial_eval]; omega

/-- Specialization to the explicit dimension polynomial of the proved online service. -/
noncomputable def initializeOnlineEpoch (p : BitProgram) : Block := initializeEpoch p onlineMinorBitPolynomial

theorem initializeOnlineEpoch_correct (p : BitProgram) {n : Nat} (anchor : Fin n) (s : Memory K)
    (safe : Good P s) (zero : P 0) (one : P 1) (dim : s.index 72=n) (mark : s.index 74=anchor.val)
    (base : 3≤s.index 76) :
    ∃ k≤(epochPolynomial p onlineMinorBitPolynomial).eval n, ∃ t, Eval (Good P) (initializeOnlineEpoch p) s k t ∧
      Rep p (p.initial (priceInput (2^(1+onlineMinorBitFormula n)) anchor)) t ∧
      MetadataEffect (s.putIndex 47 (s.index 76)) t (priceInput (2^(1+onlineMinorBitFormula n)) anchor) := by
  simpa only [initializeOnlineEpoch,onlineMinorBitPolynomial_eval] using
    initializeEpoch_correct p onlineMinorBitPolynomial anchor s safe zero one dim mark base

end PriceEpoch
end BitRAM
end LinearProgramming
end Optimization
end OAI
