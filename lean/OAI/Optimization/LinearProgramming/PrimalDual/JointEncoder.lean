import OAI.Optimization.LinearProgramming.PrimalDual.JointTraversal
import OAI.Optimization.LinearProgramming.PrimalDual.RAMBudget
import OAI.Optimization.LinearProgramming.PrimalDual.Bits
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial

/-! The fixed, dimension-uniform arithmetic RAM block which constructs the joint LP. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace JointRAM

open RAM RAM.Tape RAM.Block Polynomial

private def rowTerm : AddressTerm 9 :=
  let m : AddressTerm 9 := .reg 0
  let d : AddressTerm 9 := .reg 1
  (m+m)+(d+d)+1

private def colTerm : AddressTerm 9 := AddressTerm.reg 1 + .reg 0

private def setIndex (dst : Nat) (e : AddressTerm 9) : Block :=
  .seq (e.code 12) (.op (.addrCopy dst 12))

/-- Initialize the two output dimensions, the output cursor, and the scalar zero register. -/
def prepare : Block :=
  .seq (setIndex 6 rowTerm) (.seq (setIndex 7 colTerm)
    (.seq (.op (.addrCopy 8 3)) (.op (.const 1 0))))

/-- Emit the canonical matrix and RHS from disjoint source and destination tape windows. -/
def encode : Block := .seq prepare traverse

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

private theorem setIndex_correct (dst : Nat) (e : AddressTerm 9) (s : Memory K) (hs : Good P s) :
    let v : Env := fun i => s.index i
    ∃ t k, Eval (Good P) (setIndex dst e) s k t ∧ k ≤ e.cost v + 1 ∧ t.data = s.data ∧
      (∀ i < 12, i ≠ dst → t.index i = s.index i) ∧ t.index dst = e.value v := by
  let v : Env := fun i => s.index i
  obtain ⟨k,t,he,hk,hd,hf,hv⟩ := e.correct v 12 s (by decide) (fun _ => rfl) hs
  refine ⟨_,_,.seq he (eval_copyI t he.safe_end dst 12), Nat.add_le_add_right hk 1,
    hd, fun i hi hne => (getPutDifferent _ hne).trans (hf i hi),?_⟩
  simpa using hv

private theorem prepare_correct (b : Layout K) (s : Memory K) (hs : Good P s) (h0 : P 0)
    (hsrc : 2 ≤ b.src) (hm : s.index 0 = b.m) (hd : s.index 1 = b.d)
    (hi : s.index 2 = b.src) (ho : s.index 3 = b.dst)
    (input : ∀ j < b.inputLength, s.data (b.src+j) = b.sourceWord j) :
    ∃ t k, Eval (Good P) prepare s k t ∧ k ≤ 30+16*(b.m+b.d) ∧ b.Written P 0 t s.data := by
  obtain ⟨u,k,hr,hk,hud,hu,hrow⟩ := setIndex_correct 6 rowTerm s hs
  obtain ⟨v,l,hc,hl,hvd,hv,hcol⟩ := setIndex_correct 7 colTerm u hr.safe_end
  have hu0 := (hu 0 (by decide) (by decide)).trans hm
  have hu1 := (hu 1 (by decide) (by decide)).trans hd
  have rr : u.index 6 = b.rows := by
    change u.index 6 = s.index 0+s.index 0+(s.index 1+s.index 1)+1 at hrow
    unfold Layout.rows; omega
  have cc : v.index 7 = b.cols := by
    change v.index 7 = u.index 1+u.index 0 at hcol
    simpa [Layout.cols,hu0,hu1] using hcol
  have rowBudget : rowTerm.cost (fun i : Fin 9 => s.index i)+1 = 18+4*b.m+12*b.d := by
    change ((1+(1+(2+4*s.index 0)))+((1+(1+(2+4*s.index 1)))+(2+4*(s.index 1+s.index 1))))+
      (1+(2+4*1))+1 = _
    omega
  have colBudget : colTerm.cost (fun i : Fin 9 => u.index i)+1 = 5+4*b.m := by
    change 1+(1+(2+4*u.index 0))+1 = _
    omega
  let z := v.putIndex 8 (v.index 3)
  let t := z.putData 1 0
  have gz : Good P z := hc.safe_end
  have hsafe : Good P t := by
    intro j
    by_cases hj : j=1
    · simpa [t,Memory.putData,hj] using h0
    · simpa [t,Memory.putData,hj] using gz j
  have op : Eval (Good P) (.op (.const 1 0)) z 1 t := by
    apply Eval.op gz hsafe
    intro pc; simp [execInstr,Memory.atPC,Memory.putData,State.putData,t]
  have frame (j : Nat) (hj : j<6) : v.index j = s.index j :=
    (hv j (by omega) (by omega)).trans (hu j (by omega) (by omega))
  refine ⟨t,_,.seq hr (.seq hc (.seq (eval_copyI v hc.safe_end 8 3) op)),?_,?_⟩
  · rw [rowBudget] at hk; rw [colBudget] at hl
    omega
  · refine ⟨hsafe,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [t,Memory.putData]
    · simpa [t,z,Memory.putData,Memory.putIndex] using (frame 0 (by decide)).trans hm
    · simpa [t,z,Memory.putData,Memory.putIndex] using (frame 1 (by decide)).trans hd
    · simpa [t,z,Memory.putData,Memory.putIndex] using (frame 2 (by decide)).trans hi
    · simpa [t,z,Memory.putData,Memory.putIndex] using (frame 3 (by decide)).trans ho
    · simpa [t,z,Memory.putData,Memory.putIndex] using (hv 6 (by decide) (by decide)).trans rr
    · simpa [t,z,Memory.putData,Memory.putIndex] using cc
    · simpa [t,z,Memory.putData,Memory.putIndex] using (frame 3 (by decide)).trans ho
    · intro j hj
      change Function.update v.data 1 0 (b.src+j) = _
      rw [Function.update_of_ne (by omega : b.src+j ≠ 1),hvd,hud,input j hj]
    · intro i hi; omega
    · intro i hi _
      change Function.update v.data 1 0 i = _
      rw [Function.update_of_ne (by omega : i ≠ 1),hvd,hud]

/-- An explicit time polynomial in the total number of input rows and columns. -/
noncomputable def encoderPolynomial : Polynomial Nat :=
  let r : Polynomial Nat := 2*X+1
  let c := cellPolynomial
  (30+16*X) + ((r*(X*(c+3)+5)+2)+(1+(r*(c+3)+2)))

/-- Counted execution of the finite instruction block. The source window and all output
words are verified, and `P` holds of every scalar register at every intermediate state. -/
theorem encode_correct (b : Layout K) (s : Memory K) (hs : Good P s) (h0 : P 0) (h1 : P (-1))
    (hneg : ∀ q, P q → P (-q)) (hsrc : 2 ≤ b.src) (hsep : b.src+b.inputLength ≤ b.dst)
    (hm : s.index 0 = b.m) (hd : s.index 1 = b.d) (hi : s.index 2 = b.src)
    (ho : s.index 3 = b.dst) (input : ∀ j < b.inputLength, s.data (b.src+j) = b.sourceWord j) :
    ∃ t k, Eval (Good P) encode s k t ∧ k ≤ encoderPolynomial.eval (b.m+b.d) ∧
      b.Written P (b.rows*b.cols+b.rows) t s.data := by
  obtain ⟨u,k,init,hk,hw⟩ := prepare_correct b s hs h0 hsrc hm hd hi ho input
  have budget : b.BoundedEntries (cellPolynomial.eval (b.m+b.d)) := by
    intro e he0 he1 hrow hcol
    have hr : e 4 < 2*e 0+2*e 1+1 := by unfold Layout.rows at hrow; omega
    have hc : e 5 ≤ e 1+e 0 := by simpa only [he0,he1,Layout.cols] using hcol
    simpa only [he0,he1] using cell_cost e hr hc
  obtain ⟨t,l,hl,run,ho'⟩ := traverse_correct b _ budget P h0 h1 hneg hsrc hsep u hw
  have hr : b.rows = 2*(b.m+b.d)+1 := by unfold Layout.rows; omega
  have hc : b.cols = b.m+b.d := Nat.add_comm _ _
  exact ⟨t,_,.seq init run,by simpa [encoderPolynomial,hr,hc] using Nat.add_le_add hk hl,ho'⟩

/-- The actual instructions inside an enclosing program preserve the global scalar bit bound.
The time coefficient and exponent are fixed before either dimension or any entry is supplied. -/
theorem encode_execution (b : Layout ℚ) (s : Memory ℚ) (B : Nat) (hB : 3 ≤ B)
    (hs : Good (fun q => ratBits q ≤ B) s) (hsrc : 2 ≤ b.src)
    (hsep : b.src+b.inputLength ≤ b.dst) (hm : s.index 0 = b.m) (hd : s.index 1 = b.d)
    (hi : s.index 2 = b.src) (ho : s.index 3 = b.dst)
    (input : ∀ j < b.inputLength, s.data (b.src+j) = b.sourceWord j)
    {program : Program} {pc : Nat} (included : CodeAt program pc (encode.compile pc)) :
    ∃ (t : Memory ℚ) (k : Nat), Execution program (scalarBound B) (s.atPC pc) k (t.atPC (pc+encode.size)) ∧
      k ≤ polyBound (encoderPolynomial.eval 1) encoderPolynomial.natDegree (b.m+b.d) ∧
      t.index 6 = b.rows ∧ t.index 7 = b.cols ∧
      (∀ j < b.inputLength, t.data (b.src+j) = b.sourceWord j) ∧
      (∀ j < b.destination.length, t.data (b.dst+j) = b.word j) ∧
      ∀ j, 1 < j → (j < b.dst ∨ b.dst+b.rows*b.cols+b.rows ≤ j) → t.data j = s.data j := by
  obtain ⟨t,k,he,hk,w⟩ := encode_correct b s hs hB hB
    (fun q hq => by simpa only [ratBits_neg] using hq) hsrc hsep hm hd hi ho input
  refine ⟨t,k,he.compile_correct included,hk.trans (polynomial_eval_le_polyBound _ _),
    w.rowsReg,w.colsReg,w.input,?_,?_⟩
  · intro j hj
    apply w.output
    simpa only [Layout.destination, lpInput_length, Layout.rows, Layout.cols] using hj
  · intro j hj hreg
    exact w.outside j hj (by simpa only [Nat.add_assoc] using hreg)

end JointRAM
end PrimalDual
end LinearProgramming
end Optimization
end OAI
