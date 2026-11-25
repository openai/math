import OAI.Optimization.LinearProgramming.RAM.Code

/-! Address-register arithmetic built from unit-cost RAM increments and decrements. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Tape

open Block
variable {K : Type*}

def Good (P : K → Prop) (m : Memory K) : Prop := ∀ i, P (m.data i)

@[simp] theorem getPutSame (m : Memory K) (i x : Nat) : (m.putIndex i x).index i = x := by
  simp [Memory.putIndex]

@[simp] theorem getPutDifferent (m : Memory K) {i j x : Nat} (h : j ≠ i) :
    (m.putIndex i x).index j = m.index j := Function.update_of_ne h _ _

@[simp] theorem good_putIndex {P : K → Prop} (m : Memory K) (i x : Nat) :
    Good P (m.putIndex i x) ↔ Good P m := Iff.rfl

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem eval_constI (m : Memory K) (hm : Good P m) (i n : Nat) :
    Eval (Good P) (.op (.addrConst i n)) m 1 (m.putIndex i n) := .op hm hm (fun _ => rfl)

theorem eval_copyI (m : Memory K) (hm : Good P m) (i j : Nat) :
    Eval (Good P) (.op (.addrCopy i j)) m 1 (m.putIndex i (m.index j)) := .op hm hm (fun _ => rfl)

theorem eval_incr (m : Memory K) (hm : Good P m) (i j : Nat) :
    Eval (Good P) (.op (.incr i j)) m 1 (m.putIndex i (m.index j + 1)) := .op hm hm (fun _ => rfl)

theorem eval_decr (m : Memory K) (hm : Good P m) (i j : Nat) :
    Eval (Good P) (.op (.decr i j)) m 1 (m.putIndex i (m.index j - 1)) := .op hm hm (fun _ => rfl)

/-- A reusable finite iteration rule with a cost bound for the real branch-and-jump loop. -/
theorem loop_down {safe : Memory K → Prop} (c : Cond) (body : Block) (I : Nat → Memory K → Prop)
    (cost : Nat) (hs : ∀ m, I 0 m → safe m)
    (hz : ∀ m, I 0 m → c.test m = false)
    (hn : ∀ n m, I (n+1) m → c.test m = true)
    (hbody : ∀ n m, I (n+1) m → ∃ k z, Eval safe body m k z ∧ k ≤ cost ∧ I n z)
    (n : Nat) (m : Memory K) (h : I n m) :
    ∃ k z, Eval safe (.loop c body) m k z ∧ k ≤ 1 + (2 + cost) * n ∧ I 0 z := by
  induction n generalizing m with
  | zero => exact ⟨1, m, .loopFalse (hz m h) (hs m h), by simp, h⟩
  | succ n ih =>
    obtain ⟨j, z, hz', hj, hI⟩ := hbody n m h
    obtain ⟨k, t, ht, hk, hI'⟩ := ih z hI
    exact ⟨_, t, .loopTrue (hn n m h) hz' ht, by rw [Nat.mul_succ]; omega, hI'⟩

/-- Move a counter into an accumulator, either adding it or subtracting with Nat truncation. -/
def countLoop (plus : Bool) (dst counter zeroReg : Nat) : Block :=
  .loop (.addrLT zeroReg counter) (.seq
    (.op (if plus then .incr dst dst else .decr dst dst)) (.op (.decr counter counter)))

theorem countLoop_correct (plus : Bool) (a r z : Nat) (har : a ≠ r) (haz : a ≠ z) (hrz : r ≠ z)
    (m : Memory K) (hm : Good P m) (hz : m.index z = 0) :
    ∃ k t, Eval (Good P) (countLoop plus a r z) m k t ∧ k ≤ 1+4*m.index r ∧
      t.data = m.data ∧ (∀ i, i ≠ a → i ≠ r → t.index i = m.index i) ∧ t.index r = 0 ∧
      t.index a = (if plus then m.index a + m.index r else m.index a - m.index r) := by
  let I := fun (n : Nat) (s : Memory K) =>
    s.data = m.data ∧ (∀ i, i ≠ a → i ≠ r → s.index i = m.index i) ∧ s.index r = n ∧
    n ≤ m.index r ∧ s.index a = (if plus then m.index a + (m.index r - n) else m.index a - (m.index r - n))
  have safe (n : Nat) (s : Memory K) (h : I n s) : Good P s := fun i => h.1 ▸ hm i
  have zero (n : Nat) (s : Memory K) (h : I n s) : s.index z = 0 := (h.2.1 z haz.symm hrz.symm).trans hz
  have step (n : Nat) (s : Memory K) (h : I (n+1) s) :
      ∃ k t, Eval (Good P) (.seq (.op (if plus then .incr a a else .decr a a))
        (.op (.decr r r))) s k t ∧ k ≤ 2 ∧ I n t := by
    let val := if plus then s.index a + 1 else s.index a - 1
    let p := s.putIndex a val
    let t := p.putIndex r (p.index r - 1)
    have hop : Eval (Good P) (.op (if plus then .incr a a else .decr a a)) s 1 p := by
      cases plus
      · exact eval_decr s (safe _ _ h) a a
      · exact eval_incr s (safe _ _ h) a a
    refine ⟨_, t, .seq hop (eval_decr p hop.safe_end r r), le_rfl, h.1, ?_, ?_, ?_, ?_⟩
    · intro i hi hj
      simpa [t, p, hi, hj] using h.2.1 i hi hj
    · simp [t, p, har.symm, h.2.2.1]
    · exact (Nat.le_succ n).trans h.2.2.2.1
    · simp only [t, p, getPutDifferent _ har, getPutSame, val, h.2.2.2.2]
      have := h.2.2.2.1
      cases plus <;> simp <;> omega
  have hi : I (m.index r) m := ⟨rfl, fun _ _ _ => rfl, rfl, le_rfl, by simp⟩
  obtain ⟨k,t,he,hk,h⟩ := loop_down (.addrLT z r) _ I 2 (safe 0)
    (fun s hs => by simp [Cond.test, zero _ _ hs, hs.2.2.1])
    (fun n s hs => by simp [Cond.test, zero _ _ hs, hs.2.2.1]) step _ m hi
  exact ⟨k,t,he,hk,h.1,h.2.1,h.2.2.1,by simpa using h.2.2.2.2⟩

end Tape
end RAM
end LinearProgramming
end Optimization
end OAI
