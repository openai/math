import OAI.Optimization.LinearProgramming.Compression.ServiceCopy
import OAI.Optimization.LinearProgramming.Compression.UniformIndex
import OAI.Optimization.LinearProgramming.RAM.NatCast
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

/-! Uniform initialization from the matrix input of the online minor service. The seven
low scalar registers are freed before writing the persistent header. Address-register
contents may then be overwritten by the caller's next request. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- All original values will be moved to address `7+i`. Save the second dimension, and
calculate the source and destination endpoints from the supplied column count. -/
private def prepareMove : Block :=
  .seq (.op (.addrCopy 14 1)) (.seq (.op (.addrConst 10 0)) (.seq (.op (.addrConst 15 7))
    (.seq (cellAddress 11 8 9 10 2 2 10) (cellAddress 1 8 9 15 2 2 10))))

private def movePreparationCost (n : ℕ) := 3 + 2*(n*(4*n+5)+5)

private theorem prepareMove_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (n : ℕ) (hn : s.index 2=n) (hs : ∀ i, P (s.data i)) :
    ∃ t, Block.Eval (fun m => ∀ i, P (m.data i)) prepareMove s (movePreparationCost n) t ∧
      t.data=s.data ∧ t.index 0=s.index 0 ∧ t.index 14=s.index 1 ∧ t.index 2=n ∧
      t.index 11=n*n ∧ t.index 1=n*n+7 := by
  let safe := fun m : Memory K => ∀ i, P (m.data i)
  let a := s.putIndex 14 (s.index 1)
  let b := a.putIndex 10 0
  let c := b.putIndex 15 7
  have ea : Block.Eval safe (.op (.addrCopy 14 1)) s 1 a := Block.Eval.op_addrCopy _ _ _ hs hs
  have eb : Block.Eval safe (.op (.addrConst 10 0)) a 1 b := Block.Eval.op_addrConst _ _ _ hs hs
  have ec : Block.Eval safe (.op (.addrConst 15 7)) b 1 c := Block.Eval.op_addrConst _ _ _ hs hs
  obtain ⟨u, eu, hud, hui, hsz⟩ := cellAddress_spec (K := K) (fun v : ℕ → K => ∀ i, P (v i)) c (show ∀ i, P (c.data i) from hs)
    11 8 9 10 2 2 10 (by simp [CellScratchOK])
  have cu (i : ℕ) (h₁ : i ≠ 11) (h₂ : i ≠ 8) (h₃ : i ≠ 9) : u.index i = c.index i :=
    hui _ h₁ h₂ h₃
  obtain ⟨t, et, htd, hti, hend⟩ := cellAddress_spec (K := K) (fun v : ℕ → K => ∀ i, P (v i)) u eu.safe_end
    1 8 9 15 2 2 10 (by simp [CellScratchOK])
  have c2 : c.index 2=n := by simp [c,b,a,hn]
  have c10 : c.index 10=0 := by simp [c,b]
  have u2 : u.index 2=n := (cu _ (by decide) (by decide) (by decide)).trans c2
  have u10 : u.index 10=0 := (cu _ (by decide) (by decide) (by decide)).trans c10
  have u15 : u.index 15=7 := (cu _ (by decide) (by decide) (by decide)).trans (by simp [c])
  refine ⟨t, ?_, htd.trans hud, ?_, ?_, ?_, ?_, ?_⟩
  · unfold prepareMove movePreparationCost
    have run := ea.seq (eb.seq (ec.seq (eu.seq et)))
    simp only [c2,c10,u2,u10,Nat.mul_zero,Nat.add_zero] at run
    convert run using 1
    omega
  · rw [hti 0 (by decide) (by decide) (by decide), cu 0 (by decide) (by decide) (by decide)]
    simp [c,b,a]
  · rw [hti 14 (by decide) (by decide) (by decide), cu 14 (by decide) (by decide) (by decide)]
    simp [c,b,a]
  · exact (hti _ (by decide) (by decide) (by decide)).trans u2
  · rw [hti 11 (by decide) (by decide) (by decide), hsz,c10,c2]
    omega
  · simpa only [u15,u2,u10,Nat.add_zero,Nat.add_comm 7] using hend

/-- Store first row count, second row count, total column count, and size zero of the
initial generator set in scalar registers 1, 2, 3 and 4, respectively. -/
private def writeServiceHeader : Block :=
  .seq (natCastBlock 1 6 12 0) (.seq (natCastBlock 2 6 12 14)
    (.seq (natCastBlock 3 6 12 2) (.op (.const 4 0))))

private theorem writeServiceHeader_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (d e n : ℕ)
    (hd : s.index 0=d) (he : s.index 14=e) (hn : s.index 2=n)
    (hdn : d ≤ n) (hen : e ≤ n) (hs : ∀ i, P (s.data i))
    (h1 : P 1) (hv : ∀ i ≤ n, P (i : K)) :
    ∃ t, Block.Eval (fun m => ∀ i, P (m.data i)) writeServiceHeader s
      ((4*d+4)+(4*e+4)+(4*n+4)+1) t ∧
      t.data 1=d ∧ t.data 2=e ∧ t.data 3=n ∧ t.data 4=0 ∧
      ∀ i, 7 ≤ i → t.data i=s.data i := by
  obtain ⟨a,ea,a1,_,_,afi,afd⟩ := natCastBlock_correct P s 1 6 12 0 d
    (by decide) (by decide) hd hs h1 (fun j hj => hv j (hj.trans hdn))
  have a14 := (afi 14 (by decide)).trans he
  obtain ⟨b,eb,b2,_,_,bfi,bfd⟩ := natCastBlock_correct P a 2 6 12 14 e
    (by decide) (by decide) a14 ea.safe_end h1 (fun j hj => hv j (hj.trans hen))
  have bI2 := (bfi 2 (by decide)).trans ((afi 2 (by decide)).trans hn)
  obtain ⟨c,ec,c3,_,_,_,cfd⟩ := natCastBlock_correct P b 3 6 12 2 n
    (by decide) (by decide) bI2 eb.safe_end h1 hv
  let t := c.putData 4 (0 : K)
  have ht (i : ℕ) : P (t.data i) := by
    by_cases hi : i=4
    · simpa [t,hi] using hv 0 (Nat.zero_le _)
    · simpa [t,hi] using ec.safe_end i
  have et : Block.Eval (fun m => ∀ i, P (m.data i)) (.op (.const 4 0)) c 1 t := by
    have hs0 : ∀ i, P ((c.putData 4 ((0:ℚ):K)).data i) := by simpa [t] using ht
    simpa [t] using Block.Eval.op_const (safe := fun m => ∀ i, P (m.data i)) c 4 0 ec.safe_end hs0
  refine ⟨t, by simpa [writeServiceHeader,Nat.add_assoc] using ea.seq (eb.seq (ec.seq et)), ?_, ?_, ?_, ?_, ?_⟩
  · simpa [t] using (cfd 1 (by decide) (by decide)).trans ((bfd 1 (by decide) (by decide)).trans a1)
  · simpa [t] using (cfd 2 (by decide) (by decide)).trans b2
  · simpa [t] using c3
  · simp [t]
  · intro i hi
    have h4 : i ≠ 4 := by omega
    simpa [t,h4] using (cfd i (by omega) (by omega)).trans
      ((bfd i (by omega) (by omega)).trans (afd i (by omega) (by omega)))

def minorServiceInitBlock : Block := .seq prepareMove (.seq moveServiceInput writeServiceHeader)

def minorServiceInitCost (d e n : ℕ) :=
  movePreparationCost n + (6*(n*n-1)+7) + ((4*d+4)+(4*e+4)+(4*n+4)+1)

theorem minorServiceInitCost_le {d e n : ℕ} (hn : d+e=n) :
    minorServiceInitCost d e n + 1 ≤ 50*(n+1)^2 := by
  unfold minorServiceInitCost movePreparationCost
  have hsub : n*n-1 ≤ n*n := Nat.sub_le _ _
  nlinarith

theorem minorServiceInitBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (flat : List K) (d e n : ℕ) (hrows : d+e=n)
    (hs : ∀ i : ℕ, P (flat[i]?.getD 0)) (h1 : P 1) (hv : ∀ i ≤ n, P (i : K)) :
    ∃ t, Block.Eval (fun m => ∀ i, P (m.data i)) minorServiceInitBlock
      (start [d,e,n] flat).memory (minorServiceInitCost d e n) t ∧
      t.data 1=d ∧ t.data 2=e ∧ t.data 3=n ∧ t.data 4=0 ∧
      ∀ i < n*n, t.data (7+i)=flat[i]?.getD 0 := by
  let s := (start [d,e,n] flat).memory
  obtain ⟨a,ea,adat,a0,a14,a2,a11,a1⟩ := prepareMove_spec P s n rfl hs
  obtain ⟨b,eb,bcop,bidx⟩ := moveServiceInput_spec P a (n*n) a11 a1 ea.safe_end
  obtain ⟨t,et,t1,t2,t3,t4,tailEq⟩ := writeServiceHeader_spec P b d e n
    ((bidx 0 (by decide) (by decide) (by decide)).trans a0)
    ((bidx 14 (by decide) (by decide) (by decide)).trans a14)
    ((bidx 2 (by decide) (by decide) (by decide)).trans a2)
    (by omega) (by omega) eb.safe_end h1 hv
  refine ⟨t, by simpa [minorServiceInitBlock, minorServiceInitCost,Nat.add_assoc] using ea.seq (eb.seq et),
    t1,t2,t3,t4, fun i hi => ?_⟩
  exact (tailEq (7+i) (by omega)).trans ((bcop i hi).trans (congrFun adat i))

end Compression
end LinearProgramming
end Optimization
end OAI
