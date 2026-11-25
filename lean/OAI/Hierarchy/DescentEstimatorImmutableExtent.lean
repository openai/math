import OAI.Hierarchy.DescentPackedWalshLiteralBill

namespace OAI
/-! # Address space of the packed estimator's complete immutable image -/

namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open DescentPackedWalsh DescentWalshPrecision Filter

private def literalCost (hosts axis payload digits levels cube lookup width : ℕ) :=
  let slab := hosts*payload+16*hosts*cube*digits
  let rom := lookup*width
  (2*width*(slab+payload)+2*rom) +
    (4*width+2008*(hosts+1)*width+25600*width*(hosts+1)*cube*(digits+1)+
      12800*width*cube*(width+1)^2+2*levels*rom) +
    (2*cube*width+rom) + width*(6*axis*(slab+payload)+(2*axis+1)*lookup*payload)

private theorem literalCost_bound (x : ℕ) :
    literalCost x x x x x x x x ≤ 2^17*(x+1)^6 := by
  unfold literalCost
  ring_nf
  omega

/-- The complete immutable word count has a uniform address exponent, including
the dyadic headers, the permutation, and the transform dictionaries. -/
theorem immutable_extent_at (E : EstimatorArena) (A C h : ℕ) (height : 0 < h)
    (hosts : E.hosts ≤ 2^(A*h)) (payload : E.payload ≤ C*h) (axis : E.dim ≤ h)
    (lanes : laneBits E.dim E.payload E.precision=E.low)
    (small : 8*E.precision ≤ E.payload/2) (gain : E.gainBits ≤ E.precision) :
    E.staticEnd-E.origin ≤ 2^((6*(A+C+1)+23)*h) := by
  let W := (A+C+1)*h
  have hW : h ≤ W := Nat.le_mul_of_pos_left _ (by omega : 0 < A+C+1)
  have hostW : A*h ≤ W := Nat.mul_le_mul_right h (by omega : A ≤ A+C+1)
  have payW := payload.trans (Nat.mul_le_mul_right h (by omega : C ≤ A+C+1))
  have hp := E.positive
  have part := Nat.div_le_self E.payload 2
  have digits : E.precision ≤ E.payload := by omega
  have positive : 0 < E.payload := hp.trans_le digits
  have count := hosts.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hostW)
  have priced := E.static_bill W W (Nat.le_mul_of_pos_right W positive) count
    (digits.trans (payW.trans (Nat.le_succ W))) lanes small gain
  have raw := (Nat.le_mul_of_pos_right (E.staticEnd-E.origin) (height.trans_le hW)).trans priced
  have depth : E.plan.depth ≤ W := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr count
  let x := 2^W
  have widthBound : W ≤ x := Nat.lt_two_pow_self.le
  have axisBound := (axis.trans hW).trans widthBound
  have payBound := payW.trans widthBound
  have digitBound := digits.trans payBound
  have levelBound := depth.trans widthBound
  have cube : 2^E.dim ≤ x := Nat.pow_le_pow_right (by decide) (axis.trans hW)
  have lookup : 2^(E.payload/2) ≤ x := Nat.pow_le_pow_right (by decide) (part.trans payW)
  have estimated : E.staticBill W W ≤ literalCost x x x x x x x x := by
    change literalCost E.hosts E.dim E.payload E.precision E.plan.depth (2^E.dim)
      (2^(E.payload/2)) W ≤ _
    dsimp only [literalCost]
    gcongr
  have grow : x+1 ≤ 2^(W+1) := by
    change 2^W+1 ≤ 2^(W+1)
    rw [pow_succ]
    have pos := Nat.two_pow_pos W
    omega
  calc
    _ ≤ E.staticBill W W := raw
    _ ≤ literalCost x x x x x x x x := estimated
    _ ≤ 2^17*(x+1)^6 := literalCost_bound x
    _ ≤ 2^17*(2^(W+1))^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left grow 6)
    _ = 2^(17+(W+1)*6) := by rw [← pow_mul,← pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp only [W]
      nlinarith only [height]

/-- A quadratic logarithmic local dimension meets the preceding finite
allocation at every sufficiently large original scale. -/
theorem eventually_immutable_extent (A C K : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ E : EstimatorArena, E.hosts ≤ 2^(A*h) →
      E.payload ≤ C*h → E.dim ≤ K*(Nat.log 2 h+1)^2 →
      laneBits E.dim E.payload E.precision=E.low → 8*E.precision ≤ E.payload/2 →
      E.gainBits ≤ E.precision → E.staticEnd-E.origin ≤ 2^((6*(A+C+1)+23)*h) := by
  filter_upwards [eventually_log_square K,eventually_ge_atTop 1] with h square positive
  intro E hosts payload axis lanes small gain
  exact E.immutable_extent_at A C h positive hosts payload (axis.trans square) lanes small gain

end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
