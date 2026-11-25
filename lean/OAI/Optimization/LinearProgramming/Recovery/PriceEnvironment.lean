import OAI.Optimization.LinearProgramming.Recovery.PriceMatrices
import OAI.Optimization.LinearProgramming.NativePrice.PacketRAM
import OAI.Optimization.LinearProgramming.BitRAM.IndexScript

/-! Persistent matrix buffers of a single marked subspace problem. Every new price
request rebuilds the public geometric header from the entries proved to survive the
previous call. The decoder consumes only its disposable input and price windows. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PriceLayout

open RAM Geometry
variable {r s n : ℕ}

theorem fromHeader {K : Type} {x : LabelInput.Buffers r s n} {D : Matrix (Fin r) (Fin n) K}
    {E : Matrix (Fin s) (Fin n) K} {q : Fin n→K} {i : Fin n} {m : Memory K}
    (h : LabelInput.Header x D E q i m) : Matrices x D E m :=
  ⟨h.batch.height,h.batch.width,h.batch.sourceAddr,h.batch.priceAddr,h.batch.tripleAddr,h.batch.pivotAddr,
    h.dualAddr,h.dualRank,h.batch.matrixData,h.dual⟩

private theorem offset_lt {a n : ℕ} (i : Fin a) (j : Fin n) : i.val*n+j.val < a*n := by
  have first:=Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at first
  omega

theorem Matrices.retain {K : Type*} {x : LabelInput.Buffers r s n} {D : Matrix (Fin r) (Fin n) K}
    {E : Matrix (Fin s) (Fin n) K} {m t : Memory K} (h : Matrices x D E m)
    (hi : ∀ a,129 ≤ a → a ≤ 149 → a≠135 → a≠137 → a≠139 → t.index a=m.index a)
    (hd : ∀ a,x.dual ≤ a → a < x.price → t.data a=m.data a) : Matrices x D E t := by
  have du:=x.dualEnd
  have pr:=x.primalEnd
  refine ⟨(hi 129 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.rank,
    (hi 130 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.columns,
    (hi 131 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.primalBase,
    (hi 132 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.priceBase,
    (hi 133 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.freeBase,
    (hi 136 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.indexBase,
    (hi 147 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.dualBase,
    (hi 148 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.dualRank,?_,?_⟩
  · intro i j
    have ofs:=offset_lt i j
    exact (hd _ (by omega) (by omega)).trans (h.primal i j)
  · intro i j
    have ofs:=offset_lt i j
    exact (hd _ (by omega) (by omega)).trans (h.dual i j)

private def decoderOps : List Instr := [.addrCopy 0 130,.addrCopy 9 132]
private def callOps : List Instr := [.addrCopy 200 147,.addrCopy 201 136,.addrCopy 202 129,
  .addrCopy 203 148,.addrCopy 204 130,.addrCopy 205 14,.addrCopy 206 131,.addrCopy 207 132,.addrCopy 208 133]

def decoderHeader : Block := .straight decoderOps
def callHeader : Block := .straight callOps

private def after {K : Type*} (m : Memory K) (ops : List Instr) : Memory K := ⟨m.data,BitRAM.IndexScript.run ops m.index⟩

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem decoderHeader_run (P : K→Prop) {m : Memory K} (safe : m.AllData P) :
    Block.Eval (Memory.AllData P) decoderHeader m 2 (after m decoderOps) :=
  BitRAM.IndexScript.correct decoderOps (by simp [decoderOps,BitRAM.IndexScript.allowed]) m safe

private theorem callHeader_run (P : K→Prop) {m : Memory K} (safe : m.AllData P) :
    Block.Eval (Memory.AllData P) callHeader m 9 (after m callOps) :=
  BitRAM.IndexScript.correct callOps (by simp [callOps,BitRAM.IndexScript.allowed]) m safe

def parseAndPrepare : Block := .seq decoderHeader (.seq NativePrice.packetBlock callHeader)

/-- The numeric parser need not convert any input matrix coefficient to binary.
It reads a canonical word already charged by the finite bit-program clock. -/
theorem parseAndPrepare_run (P : K→Prop) (x : LabelInput.Buffers r s n) (D : Matrix (Fin r) (Fin n) K)
    (E : Matrix (Fin s) (Fin n) K) (i : Fin n) (prices : Fin n→ℚ) (m : Memory K)
    (mat : Matrices x D E m) (safe : m.AllData P) (word : BitRAM.ScalarPacket m 256 (OracleSpec.priceQuery i prices))
    (len : m.index 37=(OracleSpec.priceQuery i prices).length) (base : m.index 43=256)
    (room : 256+(OracleSpec.priceQuery i prices).length ≤ x.dual) (vals : NativePrice.Values P i prices) :
    ∃ t k,k ≤ NativePrice.packetTime n (OracleSpec.priceQuery i prices).length+11 ∧
      Block.Eval (Memory.AllData P) parseAndPrepare m k t ∧
      LabelInput.Inputs x D E (fun j => ((prices j):K)) i t := by
  let a:=after m decoderOps
  have aMat : Matrices x D E a := mat.retain (fun j hj _ _ _ _ => by
    change BitRAM.IndexScript.run decoderOps m.index j=m.index j
    simp [decoderOps,BitRAM.IndexScript.run,BitRAM.IndexScript.update,Function.update,show j≠9 by omega,show j≠0 by omega]) (fun _ _ _=>rfl)
  have loc : NativePrice.Header i prices a 256 x.price := by
    refine ⟨mat.columns,mat.priceBase,len,base,by decide,?_,Or.inr ?_⟩ <;>
      have := x.primalEnd <;> have := x.dualEnd <;> have := x.dualHigh <;> omega
  obtain ⟨b,k,hk,parse,out⟩:=NativePrice.packetBlock_exchange P i prices a 256 x.price loc word safe vals
  have high:=x.dualHigh
  have bMat : Matrices x D E b := aMat.retain
    (fun j hj _ _ _ _=>out.index j (Or.inr (Or.inr (Or.inr (by omega)))))
    (fun j hj hx=>out.data j (Or.inr (by omega)) (Or.inl hx))
  let t:=after b callOps
  refine ⟨t,2+(k+9),by omega,(decoderHeader_run P safe).seq (parse.seq (callHeader_run P parse.safe_end)),?_⟩
  exact ⟨bMat.dualBase,bMat.indexBase,bMat.rank,bMat.dualRank,bMat.columns,out.designation,bMat.primalBase,
    bMat.priceBase,bMat.freeBase,bMat.primal,bMat.dual,out.prices⟩

end PriceLayout
end Recovery
end LinearProgramming
end Optimization
end OAI
