import OAI.Optimization.LinearProgramming.Compression.BinaryDivisionCore

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- A single composable RAM block performs Euclidean long division. The caller supplies
a numerator in data register 0, a positive divisor in 1, and a bit bound k in index 0.
It returns the remainder in 0 and quotient in 3. Only scalar registers 0 through 5
and address register 1 are modified. -/
theorem quotientRemainderBlock_spec (m : Memory ℚ) (a b k : ℕ) {P : ℚ → Prop}
    (hm : m.AllData P) (ha : m.data 0 = (a : ℚ)) (hb0 : m.data 1 = (b : ℚ))
    (hk : m.index 0 = k) (haK : a < 2^k) (hb : 0 < b) (hbK : b ≤ 2^k)
    (hP : ∀ v : ℕ, v ≤ 2^(2*k+2) → P (v : ℚ)) :
    ∃ (n : ℕ) (z : Memory ℚ), Block.Eval (Memory.AllData P) quotientRemainderBlock m n z ∧
      n ≤ 16*k+12 ∧ z.data 0 = (a%b : ℕ) ∧ z.data 1 = (b : ℚ) ∧
      z.data 3 = (a/b : ℕ) ∧ (∀ i, 6 ≤ i → z.data i = m.data i) ∧
      (∀ i, i ≠ 1 → z.index i = m.index i) := by
  let cap := 2^(2*k+2)
  have hsmall : 2^k ≤ cap := Nat.pow_le_pow_right (by decide) (by omega)
  have h01 : 2 ≤ cap := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ 2*k+2 by omega)
    simpa [cap] using h
  have h0 : P (0 : ℚ) := by exact_mod_cast hP 0 (Nat.zero_le _)
  have h1 : P (1 : ℚ) := by exact_mod_cast hP 1 (by omega)
  have h2 : P (2 : ℚ) := by exact_mod_cast hP 2 (by omega)
  have hbP : P (b : ℚ) := hP b (hbK.trans hsmall)
  have haP : P (a : ℚ) := hP a (haK.le.trans hsmall)
  have hweight (j : ℕ) (hj : j ≤ k) : b*2^j ≤ cap := by
    calc
      _ ≤ 2^k*2^k := Nat.mul_le_mul hbK (Nat.pow_le_pow_right (by decide) hj)
      _ = 2^(k+k) := (pow_add 2 k k).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hdouble {q : ℕ} (hq : q ≤ a) : 2*q+1 ≤ cap := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) (show k+1 ≤ 2*k+2 by omega)
    rw [pow_succ] at h
    dsimp [cap]
    omega
  let m1 := m.putData 2 (m.data 1)
  let m2 := m1.putData 3 0
  let m3 := m2.putData 4 2
  let m4 := m3.putData 5 1
  have h1' : Block.Eval (Memory.AllData P) (.op (.copy 2 1)) m 1 m1 :=
    Block.Eval.op_copy m 2 1 hm (hm.putData 2 (hm 1))
  have h2' : Block.Eval (Memory.AllData P) (.op (.const 3 0)) m1 1 m2 :=
    Block.Eval.op_const m1 3 0 h1'.safe_end (h1'.safe_end.putData 3 h0)
  have h3' : Block.Eval (Memory.AllData P) (.op (.const 4 2)) m2 1 m3 :=
    Block.Eval.op_const m2 4 2 h2'.safe_end (h2'.safe_end.putData 4 h2)
  have h4' : Block.Eval (Memory.AllData P) (.op (.const 5 1)) m3 1 m4 :=
    Block.Eval.op_const m3 5 1 h3'.safe_end (h3'.safe_end.putData 5 h1)
  let I := fun (j : ℕ) (s : Memory ℚ) => s = divisionFrame m a b (b*2^j) 0 j ∧ j ≤ k
  have hi : I 0 (m4.putIndex 1 0) := by
    refine ⟨?_, Nat.zero_le _⟩
    apply congrArg₂ Memory.mk
    · funext i
      match i with
      | 0 | 1 | 2 | 3 | 4 | 5 | _+6 =>
        simp [m4,m3,m2,m1,Memory.putData,Function.update,ha,hb0]
    · rfl
  have safeI (j : ℕ) (s : Memory ℚ) (hs : I j s) : s.AllData P ∧ s.index 1=j ∧ s.index 0=k := by
    obtain ⟨rfl,hj⟩ := hs
    exact ⟨divisionFrame_safe hm haP hbP (hP _ (hweight j hj)) (by simpa using h0) h2 h1 j,
      by simp [divisionFrame], by simp [divisionFrame, hk]⟩
  have incI (j : ℕ) (hj : j < k) (s : Memory ℚ) (hs : I j s) :
      ∃ t, Block.Eval (Memory.AllData P) (.op (.add 2 2 2)) s 1 t ∧
        I (j+1) (t.putIndex 1 (t.index 1+1)) := by
    have hsafe := (safeI j s hs).1
    obtain ⟨rfl,_⟩ := hs
    let t := divisionFrame m a b (b*2^(j+1)) 0 j
    have he : (divisionFrame m a b (b*2^j) 0 j).data 2 + (divisionFrame m a b (b*2^j) 0 j).data 2 =
        ((b*2^(j+1) : ℕ) : ℚ) := by
      change ((b*2^j : ℕ) : ℚ) + ((b*2^j : ℕ) : ℚ) = _
      push_cast; rw [pow_succ]; ring
    have hrun := Block.Eval.op_add (divisionFrame m a b (b*2^j) 0 j) 2 2 2 hsafe
    rw [he, divisionFrame_write2] at hrun
    refine ⟨t, hrun (divisionFrame_safe hm haP hbP (hP _ (hweight _ hj)) (by simpa using h0) h2 h1 j), ?_, hj⟩
    have hctr : t.index 1=j := by simp [t,divisionFrame]
    rw [hctr]; exact divisionFrame_index ..
  obtain ⟨s,hscale,hes⟩ := Block.Eval.forRange_invariant_exact 1 0 k 1 I m4 h4'.safe_end hi safeI incI
  let w := fun j => b*2^(k-j)
  let R := fun j => a % w j
  let Q := fun j => a / w j
  let J := fun (j : ℕ) (s : Memory ℚ) => s = divisionFrame m (R j) b (w j) (Q j) j ∧ j ≤ k
  have hw0 : a < w 0 := by
    simp only [w, Nat.sub_zero]
    exact haK.trans_le (Nat.le_mul_of_pos_left _ hb)
  have hj0 : J 0 (s.putIndex 1 0) := by
    refine ⟨?_,Nat.zero_le _⟩
    rw [hes.1, divisionFrame_index]
    simp [Q,R,Nat.mod_eq_of_lt hw0,Nat.div_eq_of_lt hw0,w]
  have safeJ (j : ℕ) (z : Memory ℚ) (h : J j z) :
      z.AllData P ∧ z.index 1=j ∧ z.index 0=k := by
    obtain ⟨rfl,hj⟩ := h
    exact ⟨divisionFrame_safe hm (hP _ ((Nat.mod_le ..).trans (haK.le.trans hsmall))) hbP
      (hP _ (hweight _ (Nat.sub_le ..))) (hP _ ((Nat.div_le_self ..).trans (haK.le.trans hsmall))) h2 h1 j,
      by simp [divisionFrame], by simp [divisionFrame, hk]⟩
  have scanJ (j : ℕ) (hj : j < k) (z : Memory ℚ) (hs : J j z) :
      ∃ t cost, cost ≤ 5 ∧ Block.Eval (Memory.AllData P) divisionStage z cost t ∧
        J (j+1) (t.putIndex 1 (t.index 1+1)) := by
    obtain ⟨rfl,_⟩ := hs
    have hjw : w j = 2*w (j+1) := by
      dsimp [w]
      rw [show k-j=(k-(j+1))+1 by omega, pow_succ]
      ring
    have hw : 0 < w (j+1) := Nat.mul_pos hb (by positivity)
    have hr : R j ≤ a := Nat.mod_le ..
    have hq : Q j ≤ a := Nat.div_le_self ..
    have ht := divisionStage_eval hm (R j) b (w (j+1)) (Q j) j
      (hP _ (hr.trans (haK.le.trans hsmall))) hbP
      (hP _ (hjw ▸ hweight (k-j) (Nat.sub_le ..))) (hP _ (hweight _ (Nat.sub_le ..)))
      (hP _ (hq.trans (haK.le.trans hsmall)))
      (hP _ ((Nat.le_succ _).trans (hdouble hq))) (hP _ (hdouble hq))
      (hP _ ((Nat.sub_le ..).trans (hr.trans (haK.le.trans hsmall)))) h2 h1
    obtain ⟨cost,hcost,hrun⟩ := ht
    have hnext := descend_division a (w (j+1)) hw
    change nextRemainder (a % (2*w (j+1))) (w (j+1)) = R (j+1) ∧
      nextQuotient (a%(2*w (j+1))) (w (j+1)) (a/(2*w (j+1))) = Q (j+1) at hnext
    rw [← hjw] at hnext
    change nextRemainder (R j) (w (j+1)) = _ ∧ nextQuotient (R j) (w (j+1)) (Q j) = _ at hnext
    rw [← hjw,hnext.1,hnext.2] at hrun
    refine ⟨_,cost,hcost,hrun,?_,hj⟩
    rw [show (divisionFrame m (R (j+1)) b (w (j+1)) (Q (j+1)) j).index 1 = j from by simp [divisionFrame],
      divisionFrame_index]
  obtain ⟨out,cost,hcost,hscan,hout⟩ := Block.Eval.forRange_invariant 1 0 k 5 J s hscale.safe_end hj0 safeJ scanJ
  refine ⟨_,out,h1'.seq (h2'.seq (h3'.seq (h4'.seq (hscale.seq hscan)))),by omega,?_,?_,?_,?_,?_⟩
  all_goals rw [hout.1]
  · simp [divisionFrame,R,w]
  · rfl
  · simp [divisionFrame,Q,w]
  · intro i hi
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_comm 6 n]; rfl
  · intro i hi
    exact Function.update_of_ne hi _ _

end Compression
end LinearProgramming
end Optimization
end OAI
