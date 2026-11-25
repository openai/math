import OAI.Optimization.LinearProgramming.RAM.CallableBootOps
import Mathlib.Tactic.IntervalCases

/-! Restore the six borrowed odd address registers from their staged values and reset
the even control registers. The high backup cells are erased as they are read. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Block

def restoreFrom (dst : ℕ) : ℕ → Block
  | 0 => .skip
  | n+1 => .seq (program [.incr 0 0,.load dst 0,.store 0 2]) (restoreFrom (dst+2) n)

private def finalOps : List AddressOp := [.set 0 0,.set 4 0,.set 6 0,.set 8 0,.set 10 0]
def restoreBlock : Block := .seq (.op (.addrConst 2 0)) (.seq (restoreFrom 1 6) (program finalOps))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem restoreFrom_spec (P : K→Prop) (dst n p : ℕ) (s : Memory K) (hs : s.AllData P)
    (h0 : s.index 0=p) (h2 : s.index 2=0) (hodd : dst%2=1) (hsep : dst+2*n ≤ p) :
    ∃ t, Eval (Memory.AllData P) (restoreFrom dst n) s (3*n) t ∧ t.data=s.data ∧
      t.index 0=p+n ∧
      (∀ j < n, t.index (dst+2*j)=s.index (p+1+j) ∧ t.index (p+1+j)=0) ∧
      ∀ r, r≠0 → (∀ j < n, r≠dst+2*j ∧ r≠p+1+j) → t.index r=s.index r := by
  induction n generalizing dst p s with
  | zero => exact ⟨s,.skip hs,rfl,h0,fun j h => (Nat.not_lt_zero _ h).elim,fun _ _ _ => rfl⟩
  | succ n ih =>
    let ops : List AddressOp := [.incr 0 0,.load dst 0,.store 0 2]
    let u := applyOps ops s
    have one := ops_spec P ops s hs
    have ptr : u.index 0=p+1 := by
      simp (disch := omega) [u,ops,applyOps,AddressOp.apply,h0,h2]
    have zero : u.index 2=0 := by
      simp (disch := omega) [u,ops,applyOps,AddressOp.apply,h0,h2]
    have word : u.index dst=s.index (p+1) := by
      simp (disch := omega) [u,ops,applyOps,AddressOp.apply,h0,h2]
    have erased : u.index (p+1)=0 := by
      simp (disch := omega) [u,ops,applyOps,AddressOp.apply,h0,h2]
    have uf (r : ℕ) (hr : r≠0) (hd : r≠dst) (hp : r≠p+1) : u.index r=s.index r := by
      simp (disch := omega) [u,ops,applyOps,AddressOp.apply,h0,h2]
    obtain ⟨t,rest,dt,pt,wr,fr⟩ := ih (dst+2) (p+1) u one.safe_end ptr zero (by omega) (by omega)
    refine ⟨t,?_,dt.trans (ops_data ..),by omega,?_,?_⟩
    · change Eval _ (.seq (program ops) _) _ _ _
      rw [show 3*(n+1)=3+3*n by omega]
      exact one.seq rest
    · rintro (_|j) hj
      · simp only [Nat.mul_zero,Nat.add_zero]
        exact ⟨(fr _ (by omega) (fun l hl => by constructor <;> omega)).trans word,
          (fr _ (by omega) (fun l hl => by constructor <;> omega)).trans erased⟩
      · obtain ⟨a,b⟩ := wr j (by omega)
        have e := uf (p+1+1+j) (by omega) (by omega) (by omega)
        simpa only [show dst+2+2*j=dst+2*(j+1) by omega,
          show p+1+1+j=p+1+(j+1) by omega] using And.intro (a.trans e) b
    · intro r hr miss
      have cut := miss 0 (by omega)
      have tailMiss (l : ℕ) (hl : l < n) : r≠dst+2+2*l ∧ r≠p+1+1+l := by
        have h := miss (l+1) (by omega)
        constructor <;> omega
      exact (fr r hr tailMiss).trans (uf r hr (by simpa using cut.1) (by simpa using cut.2))

theorem restoreBlock_spec (P : K→Prop) (s : Memory K) (cap : ℕ) (hs : s.AllData P)
    (hc : 64 ≤ cap) (h0 : s.index 0=cap) :
    ∃ t, Eval (Memory.AllData P) restoreBlock s 24 t ∧ t.data=s.data ∧
      (∀ i < 6, t.index (2*i+1)=s.index (cap+1+i) ∧ t.index (cap+1+i)=0) ∧
      (∀ i < 6, t.index (2*i)=0) ∧
      ∀ r, 11 < r → (r < cap+1 ∨ cap+1+6 ≤ r) → t.index r=s.index r := by
  let a := s.putIndex 2 0
  have one := Eval.op_addrConst (safe:=Memory.AllData P) s 2 0 hs hs
  obtain ⟨u,run,ud,_,wr,fr⟩ := restoreFrom_spec P 1 6 cap a hs (by simpa [a] using h0)
    (by simp [a]) (by decide) (by omega)
  let t := applyOps finalOps u
  have done := ops_spec P finalOps u run.safe_end
  have keep (r : ℕ) (h0 : r≠0) (h4 : r≠4) (h6 : r≠6) (h8 : r≠8) (h10 : r≠10) :
      t.index r=u.index r := by simp [t,finalOps,applyOps,AddressOp.apply,h0,h4,h6,h8,h10]
  refine ⟨t,one.seq (run.seq done),(ops_data ..).trans ud,?_,?_,?_⟩
  · intro i hi
    obtain ⟨a',b'⟩ := wr i hi
    have h := keep (2*i+1) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hh := keep (cap+1+i) (by omega) (by omega) (by omega) (by omega) (by omega)
    exact ⟨h.trans (by simpa (disch := omega) [a,Nat.add_comm 1] using a'),hh.trans b'⟩
  · intro i hi
    have z := fr 2 (by decide) (by intro j hj; constructor <;> omega)
    have z2 : u.index 2=0 := z
    interval_cases i <;> simp [t,finalOps,applyOps,AddressOp.apply,z2]
  · intro r hr bound
    have h := keep r (by omega) (by omega) (by omega) (by omega) (by omega)
    have g := fr r (by omega) (fun j hj => by constructor <;> omega)
    exact h.trans (g.trans (Memory.putIndex_ne s (by omega) _))

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
