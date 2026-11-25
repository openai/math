import OAI.Optimization.LinearProgramming.RAM.RAMCount

/-! Indexed arithmetic used to locate entries of the dense LP matrices. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Tape

open Block
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {P : K → Prop}

/-- Add or subtract the adjacent two index registers, leaving the result in the first. -/
def addSub (plus : Bool) (a : Nat) : Block :=
  .seq (.op (.addrConst (a+2) 0)) (countLoop plus a (a+1) (a+2))

theorem addSub_correct (plus : Bool) (a : Nat) (m : Memory K) (hm : Good P m) :
    ∃ k t, Eval (Good P) (addSub plus a) m k t ∧ k ≤ 2+4*m.index (a+1) ∧
      t.data = m.data ∧ (∀ i < a, t.index i = m.index i) ∧
      t.index a = (if plus then m.index a + m.index (a+1) else m.index a - m.index (a+1)) := by
  let s := m.putIndex (a+2) 0
  have hc := eval_constI m hm (a+2) 0
  obtain ⟨k,t,h,hk,hd,hf,_,hv⟩ := countLoop_correct plus a (a+1) (a+2)
    (by omega) (by omega) (by omega) s hm (by simp [s])
  have hr : s.index (a+1) = m.index (a+1) := getPutDifferent _ (by omega)
  have ha : s.index a = m.index a := getPutDifferent _ (by omega)
  refine ⟨_, t, .seq hc h, by rw [hr] at hk; omega, hd, ?_, by simpa only [ha,hr] using hv⟩
  intro i hi
  exact (hf i (by omega) (by omega)).trans (getPutDifferent _ (by omega))

/-- Repeated addition consumes the multiplier and never reads scalar data. -/
def multiply (a : Nat) : Block :=
  .seq (.op (.addrConst (a+4) 0)) (.seq (.op (.addrConst (a+2) 0))
    (.seq (.loop (.addrLT (a+4) (a+1))
      (.seq (.op (.addrCopy (a+3) a))
        (.seq (countLoop true (a+2) (a+3) (a+4)) (.op (.decr (a+1) (a+1))))))
      (.op (.addrCopy a (a+2)))))

theorem multiply_correct (a : Nat) (m : Memory K) (hm : Good P m) :
    ∃ k t, Eval (Good P) (multiply a) m k t ∧ k ≤ 4+(5+4*m.index a)*m.index (a+1) ∧
      t.data = m.data ∧ (∀ i < a, t.index i = m.index i) ∧
      t.index a = m.index a * m.index (a+1) := by
  let A := m.index a
  let B := m.index (a+1)
  let I := fun (n : Nat) (s : Memory K) =>
    s.data = m.data ∧ (∀ i < a, s.index i = m.index i) ∧ s.index a = A ∧
      s.index (a+1) = n ∧ s.index (a+2) = A*(B-n) ∧ s.index (a+4) = 0 ∧ n ≤ B
  have step (n : Nat) (s : Memory K) (hs : I (n+1) s) :
      ∃ k t, Eval (Good P) (.seq (.op (.addrCopy (a+3) a))
        (.seq (countLoop true (a+2) (a+3) (a+4)) (.op (.decr (a+1) (a+1))))) s k t ∧
        k ≤ 3+4*A ∧ I n t := by
    obtain ⟨hd,hf,ha,hr,hc,hz,hn⟩ := hs
    have hsafe : Good P s := fun i => by simpa only [hd] using hm i
    let s' := s.putIndex (a+3) (s.index a)
    have copy := eval_copyI s hsafe (a+3) a
    obtain ⟨k,t,h,hk,hd',hf',_,hv⟩ := countLoop_correct true (a+2) (a+3) (a+4)
      (by omega) (by omega) (by omega) s' hsafe (by simpa [s'] using hz)
    have htmp : s'.index (a+3) = A := by simpa [s'] using ha
    have hc' : s'.index (a+2) = A*(B-(n+1)) := (getPutDifferent _ (by omega)).trans hc
    have front (i : Nat) (hi : i < a+2 ∨ i = a+4) : t.index i = s.index i :=
      (hf' i (by omega) (by omega)).trans (getPutDifferent _ (by omega))
    let out := t.putIndex (a+1) (t.index (a+1)-1)
    have outindex (i : Nat) (hi : i ≠ a+1) : out.index i = t.index i := getPutDifferent _ hi
    refine ⟨_,out,.seq copy (.seq h (eval_decr t h.safe_end (a+1) (a+1))), ?_, hd'.trans hd,
      fun i hi => (outindex i (by omega)).trans ((front i (by omega)).trans (hf i hi)),
      (outindex _ (by omega)).trans ((front _ (by omega)).trans ha), ?_, ?_,
      (outindex _ (by omega)).trans ((front _ (by omega)).trans hz), by omega⟩
    · rw [htmp] at hk; omega
    · simp [out, front (a+1) (by omega), hr]
    · rw [outindex _ (by omega), hv, hc', htmp]
      have hnB : B-n = (B-(n+1))+1 := by omega
      simp [hnB, Nat.mul_succ]
  let s := (m.putIndex (a+4) 0).putIndex (a+2) 0
  have init : I B s := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, le_rfl⟩
    · intro i hi; simp [s, getPutDifferent _ (show i ≠ a+2 by omega), getPutDifferent _ (show i ≠ a+4 by omega)]
    · simp [s,A]
    · simp [s,B]
    · simp [s]
    · simp [s]
  obtain ⟨k,t,h,hk,hd,hf,_,_,hc,_,_⟩ := loop_down (.addrLT (a+4) (a+1)) _ I (3+4*A)
    (fun s hs i => by simpa only [hs.1] using hm i)
    (fun s hs => by simp [Cond.test, hs.2.2.2.2.2.1, hs.2.2.2.1])
    (fun n s hs => by simp [Cond.test, hs.2.2.2.2.2.1, hs.2.2.2.1]) step B s init
  refine ⟨_,_,.seq (eval_constI m hm (a+4) 0) (.seq (eval_constI (m.putIndex (a+4) 0) (show Good P (m.putIndex (a+4) 0) from hm) (a+2) 0)
    (.seq h (eval_copyI t h.safe_end a (a+2)))), ?_, hd, ?_, ?_⟩
  · change 1+(1+(k+1)) ≤ 4+(5+4*A)*B
    rw [show 2+(3+4*A) = 5+4*A by omega] at hk
    omega
  · intro i hi
    exact (getPutDifferent _ (by omega)).trans (hf i hi)
  · simpa using hc

end Tape
end RAM
end LinearProgramming
end Optimization
end OAI
