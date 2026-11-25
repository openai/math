import OAI.Optimization.LinearProgramming.RAM.CallableRawTapes
import OAI.Optimization.LinearProgramming.Recovery.PrimalTableCode
import OAI.Optimization.LinearProgramming.Recovery.PrimalHeader
import OAI.Optimization.LinearProgramming.Recovery.InitialPairCopy
import OAI.Optimization.LinearProgramming.Recovery.DenseEncoding
import OAI.Optimization.LinearProgramming.Recovery.SlackRAM
import OAI.Optimization.LinearProgramming.PrimalDual.PassesRAM
import OAI.Optimization.LinearProgramming.Elimination.Augmented

/-! Assemble the numerical tape `[b−tail w; Aᵀ]` for the final primal solve. The
subtraction uses the original right side, and the transposition takes its coefficients
from the protected original inequality matrix. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PrimalOutput
open RAM RAM.Callable Geometry Matrix PrimalDual
open scoped Matrix

theorem assemble_run {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ) (w : Fin (m+1)→ℚ)
    (s : Memory ℚ) (raw atW cap B H : ℕ) («meta» : Header m d raw atW cap s) (origin : SlackRAM.InputAt s raw A b)
    (wdata : ∀j : Fin (m+1),s.data (atW+j.val)=w j) (high : 7 ≤ raw) (sep : raw+(m*d+m) ≤ atW)
    (safe : s.AllData (fun z=>ratBits z ≤ H)) (hb : ∀i,ratBits (b i) ≤ B) (hw : ∀j,ratBits (w j) ≤ B)
    (width : differenceWidth B ≤ H) (three : 3 ≤ H) :
    ∃ t k,k ≤ assembleTime m d ∧ Block.Eval (Memory.AllData (fun z=>ratBits z ≤ H)) assemble s k t ∧
      RawTapes t (tableauBase atW m) 208 cap (encodedGramInput (Elimination.augmentedRows A (b-Fin.tail w))) [d+1,m] ∧
      t.index 210=pointBase atW m d ∧ t.index 211=d := by
  let base:=tableauBase atW m
  have br : Holds s (raw+m*d) b:=fun i=>by simpa only [Nat.add_assoc] using origin.2 i
  have wr : Holds s (atW+1) (Fin.tail w):=by
    intro i
    rw [show atW+1+i.val=atW+i.succ.val by change atW+1+i.val=atW+(i.val+1);omega]
    exact wdata i.succ
  obtain ⟨u,diff,rhs,df,di⟩:=differencePass b (Fin.tail w) (raw+m*d) (atW+1) base 220 221 222 28 s safe
    (by decide) (by decide) (by decide) (by decide) «meta».bSource «meta».wSource «meta».rhsBase «meta».originalRows
    (by omega) (by omega) (by dsimp [base,tableauBase];omega) (Or.inr (Or.inl (by dsimp [base,tableauBase];omega)))
    (Or.inr (Or.inl (by dsimp [base,tableauBase];omega))) br wr hb (fun j=>hw j.succ) width three
  have original : uniformRect m d raw u=A:=by
    ext i j
    have v:=Nat.mul_le_mul_right d (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at v
    have below : raw+i.val*d+j.val < base:=by dsimp [base,tableauBase];omega
    have kept:=df _ (by omega) (Or.inl below)
    exact kept.trans (by simpa only [Nat.add_assoc] using origin.1 i j)
  obtain ⟨t,k,hk,transpose,rect,tf,ti⟩:=InitialPair.copy_to_spec (fun z=>ratBits z ≤ H) u raw (base+m) d m high
    (by dsimp [base,tableauBase];omega) diff.safe_end ((di 31 (by decide)).trans «meta».rows) ((di 33 (by decide)).trans «meta».columns)
    ((di 35 (by decide)).trans «meta».transpose) ((di 40 (by decide)).trans «meta».matrix) ((di 41 (by decide)).trans «meta».stride)
  rw [original] at rect
  have table : uniformRect (d+1) m base t=Elimination.augmentedRows A (b-Fin.tail w):=by
    ext j i
    refine Fin.cases ?_ (fun a=>?_) j
    · change t.data (base+0*m+i.val)=(b-Fin.tail w) i
      rw [Nat.zero_mul,Nat.add_zero]
      exact (tf _ (by dsimp [base,tableauBase];omega) (Or.inl (by omega))).trans (rhs i)
    · change t.data (base+(a.val+1)*m+i.val)=A i a
      have eq:=congrFun (congrFun rect a) i
      change t.data (base+m+a.val*m+i.val)=A i a at eq
      rw [show base+(a.val+1)*m+i.val=base+m+a.val*m+i.val by ring]
      exact eq
  have keep (j : ℕ) (lo : 50 ≤ j) : t.index j=s.index j := (ti j (by
    unfold InitialPair.CopyIndex;omega)).trans (di j (by omega))
  have rawTape : RawTapes t base 208 cap (encodedGramInput (Elimination.augmentedRows A (b-Fin.tail w))) [d+1,m] := by
    refine ⟨(keep 55 (by decide)).trans «meta».array,by simpa using (keep 56 (by decide)).trans «meta».words,
      (keep 57 (by decide)).trans «meta».dimensionArray,(keep 58 (by decide)).trans «meta».dimensionWords,
      (keep 60 (by decide)).trans «meta».capacity,PairBuilder.dense_encoded t _ table,?_⟩
    intro j hj
    have two : j < 2:=by simpa using hj
    interval_cases j <;> first | exact (keep 208 (by decide)).trans «meta».solverRows | exact (keep 209 (by decide)).trans «meta».solverColumns
  exact ⟨t,_,Nat.add_le_add_left hk _,diff.seq transpose,rawTape,(keep 210 (by decide)).trans «meta».destination,(keep 211 (by decide)).trans «meta».objectiveWidth⟩

end PrimalOutput
end Recovery
end LinearProgramming
end Optimization
end OAI
