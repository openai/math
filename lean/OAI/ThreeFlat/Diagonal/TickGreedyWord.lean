import OAI.ThreeFlat.Diagonal.Scheduling
import OAI.ThreeFlat.Diagonal.DefectBudget
import OAI.ThreeFlat.Diagonal.GroupCount

namespace OAI
/-! # Cleared-denominator greedy scores fit the physical RAM word -/

namespace ThreeFlat.Diagonal.TickGreedyWord

/-- Every operand can grow as large as the common fourth power here.
Even the product of all three operands leaves four exponents of headroom
in the physical word. -/
theorem score_room {D J W B : ℕ} (dp : 0 < D)
    (j : J ≤ (2^D)^4) (w : W ≤ (2^D)^4) (b : B ≤ (2^D)^4) :
    2*(J*(W*B)) + 4*(W*B) < 2^(16*D) := by
  let V := 2^D
  have vp : 2 ≤ V := by
    change 2^1 ≤ 2^D
    exact Nat.pow_le_pow_right (by decide) dp
  have v1 : 1 ≤ V := by omega
  have wb : W*B ≤ V^8 := by
    calc
      W*B ≤ V^4*V^4 := Nat.mul_le_mul w b
      _ = V^8 := (pow_add V 4 4).symm
  have prod : J*(W*B) ≤ V^12 := by
    calc
      J*(W*B) ≤ V^4*V^8 := Nat.mul_le_mul j wb
      _ = V^12 := (pow_add V 4 8).symm
  have wb' := wb.trans (Nat.pow_le_pow_right v1 (by decide : 8 ≤ 12))
  have hc : 6 < V^4 := lt_of_lt_of_le (by decide : 6 < 2^4) (Nat.pow_le_pow_left vp _)
  have pv : 0 < V^12 := Nat.pow_pos (by omega)
  calc
    2*(J*(W*B))+4*(W*B) ≤ 6*(V^12) := by omega
    _ < V^4*(V^12) := Nat.mul_lt_mul_of_pos_right hc pv
    _ = V^16 := (pow_add V 4 12).symm
    _ = 2^(16*D) := by rw [Nat.mul_comm 16 D,Nat.pow_mul]

theorem physical_operands {u d A e L : ℕ} (large : d+16 ≤ u) (lcap : L ≤ u^d) :
    let V := 2^(u^10)
    let q := 2^(u^3)
    let T := 2^(u^6)
    let a := 2^(u^10-u^4)
    let B := 2*(q*V*L/u^(A+2))
    let W := q*V*T/u^e
    let J := 1024*B/a
    J ≤ V^4 ∧ W ≤ V^4 ∧ B ≤ V^4 := by
  intro V q T a B W J
  have up : 0 < u := by omega
  have vpos : 0 < V := Nat.two_pow_pos _
  have two : 2 ≤ V := by
    change 2^1 ≤ 2^(u^10)
    exact Nat.pow_le_pow_right (by decide) (Nat.pow_pos up)
  have qv : q ≤ V := Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right up (by decide : 3 ≤ 10))
  have tv : T ≤ V := Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right up (by decide : 6 ≤ 10))
  have lv : L ≤ V := lcap.trans ((width_pow_le_two_pow_sq (by omega : d ≤ u)).trans
    (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right up (by decide : 2 ≤ 10))))
  have hstep : 2*u^4 ≤ u^5 := by
    rw [pow_succ u 4,Nat.mul_comm 2 (u^4)]
    exact Nat.mul_le_mul_left (u^4) (by omega : 2 ≤ u)
  have jv : J ≤ V := (group_count_budget large lcap).trans (Nat.pow_le_pow_right (by decide)
    (hstep.trans (Nat.pow_le_pow_right up (by decide : 5 ≤ 10))))
  have v4 : V ≤ V^4 := Nat.le_self_pow (by decide) V
  refine ⟨jv.trans v4,?_,?_⟩
  · calc
      W ≤ q*V*T := Nat.div_le_self _ _
      _ ≤ V*V*V := Nat.mul_le_mul (Nat.mul_le_mul_right _ qv) tv
      _ = V^3 := by ring
      _ ≤ V^4 := Nat.pow_le_pow_right vpos (by decide)
  · calc
      B ≤ 2*(q*V*L) := Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
      _ ≤ V*(V*V*V) := Nat.mul_le_mul two (Nat.mul_le_mul (Nat.mul_le_mul_right _ qv) lv)
      _ = V^4 := by ring

/-- The score and both intermediate multiplication results fit before the
native compares the score to the remaining capacity. -/
theorem intermediates {J W B work pairs z : ℕ} (j : 0 < J) (wc : work ≤ W) (pc : pairs ≤ B)
    (room : 2*(J*(W*B))+4*(W*B) < z) :
    B*work < z ∧ W*pairs < z ∧ B*work+W*pairs < z ∧
      J*(B*work+W*pairs) < z ∧ 4*(W*B) < z := by
  have x : B*work ≤ W*B := by rw [Nat.mul_comm W B]; exact Nat.mul_le_mul_left _ wc
  have y := Nat.mul_le_mul_left W pc
  have u : W*B ≤ J*(W*B) := Nat.le_mul_of_pos_left _ j
  have sc := Nat.mul_le_mul_left J (show B*work+W*pairs ≤ 2*(W*B) by omega)
  rw [show J*(2*(W*B)) = 2*(J*(W*B)) by ring] at sc
  omega

end ThreeFlat.Diagonal.TickGreedyWord

end OAI
