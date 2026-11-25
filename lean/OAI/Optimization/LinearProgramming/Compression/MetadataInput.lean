import OAI.Optimization.LinearProgramming.Compression.MetadataFinish
import OAI.Optimization.LinearProgramming.Compression.MetadataNat
import OAI.Optimization.LinearProgramming.Compression.MetadataRepeat
import OAI.Optimization.LinearProgramming.Compression.InnerWire
import Mathlib.Tactic.Ring

/-! The actual native metadata word handed to the two-LLL compression service.
Only bounded natural address values are tested. Every emitted value is a scalar zero or one. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
namespace Metadata

open RAM BitRAM OracleSpec

/-- A unary string uses one `true,true` pair per coordinate and one terminating `false`. -/
def unary (header : Nat) : Block := .seq (repeatPairFrom header true) (emit false)

private theorem unary_word (n : Nat) :
    (List.replicate n [true,true]).flatten ++ [false] = frame (List.replicate n true) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have cons (w : Word) : frame (true :: w) = true :: true :: frame w := rfl
    simp only [List.replicate_succ,List.flatten_cons,List.cons_append,List.nil_append,cons,ih]

def writeInputBlock : Block := initializeBlock.seq <| (unary 57).seq <| (unary 59).seq <|
  (emitFromBit 61).seq (writeNatFrom 63)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem unary_correct (s : Memory K) (header n : Nat) (hs : s.AllData P) (ready : Ready s)
    (count : s.index header=n) :
    ∃ t k, Block.Eval (Memory.AllData P) (unary header) s k t ∧ k ≤ 10*n+6 ∧
      Effect s t (frame (List.replicate n true)) := by
  obtain ⟨a,k,wr,hk,one⟩ := repeatPairFrom_correct header true n s hs ready count
  obtain ⟨t,terminator,last,_⟩ := emit_correct a false wr.safe_end (ready.after one)
  exact ⟨t,k+3,wr.seq terminator,by omega,by simpa only [unary_word] using one.append last⟩

/-- Write the exact input of the native compression service and restore its complete
caller-facing memory frame, including every maintained cache address. The trace bound uses
only n and g, including when a requested rank is zero or when there are no generators. -/
theorem writeInputBlock_correct (s : Memory K) (n g : Nat) (member : Bool) (rank : Nat)
    (hs : s.AllData P) (hz : P 0) (ho : P 1) (base : 3 ≤ s.index 47)
    (hn : s.index 57=n) (hg : s.index 59=g) (hm : s.index 61=member.toNat)
    (hr : s.index 63=rank) (hgr : rank ≤ g) :
    ∃ t k, Block.Eval (Memory.AllData P) writeInputBlock s k t ∧ k ≤ 200*(n+g+1)^2+50 ∧
      MetadataEffect s t (inputWord n g member rank) := by
  obtain ⟨a,init,start⟩ := initialize_correct s hs hz ho base
  have header (i : Nat) (lo : 57 ≤ i) (hi : i ≤ 63) : a.index i=s.index i :=
    start.frame i (by omega) (by omega) (by omega) (by omega)
  have prior {u v : Memory K} {bs : Word} (ef : Effect u v bs) (i : Nat) (lo : 57 ≤ i) (hi : i ≤ 63) :
      v.index i=u.index i := ef.frame i (by omega) (by omega) (by omega) (by omega)
  obtain ⟨b,kn,wrn,bn,en⟩ := unary_correct a 57 n init.safe_end start.ready ((header 57 (by decide) (by decide)).trans hn)
  obtain ⟨c,kg,wrg,bg,eg⟩ := unary_correct b 59 g wrn.safe_end (start.ready.after en)
    ((prior en 59 (by decide) (by decide)).trans ((header 59 (by decide) (by decide)).trans hg))
  have firstTwo := en.append eg
  obtain ⟨d,km,wrm,bm,em⟩ := emitFromBit_correct c 61 member wrg.safe_end (start.ready.after firstTwo)
    ((prior firstTwo 61 (by decide) (by decide)).trans ((header 61 (by decide) (by decide)).trans hm))
  have throughFlag := firstTwo.append em
  obtain ⟨t,kr,wrr,br,er⟩ := writeNatFrom_correct d 63 rank wrm.safe_end (start.ready.after throughFlag)
    ((prior throughFlag 63 (by decide) (by decide)).trans ((header 63 (by decide) (by decide)).trans hr))
  refine ⟨t,_,init.seq (wrn.seq (wrg.seq (wrm.seq wrr))),?_,?_⟩
  · have rbound : (rank+1)*(5*rank+25) ≤ (g+1)*(5*g+25) := Nat.mul_le_mul (by omega) (by omega)
    have cap : 6+(10*n+6)+(10*g+6)+5+((g+1)*(5*g+25)+5) ≤ 200*(n+g+1)^2+50 := by
      ring_nf; omega
    omega
  · apply start.finish
    simpa only [inputWord,List.append_assoc] using throughFlag.append er

end Metadata
end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
