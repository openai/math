import OAI.Hierarchy.DescentTerminalSeedStampWidth
import OAI.Hierarchy.DescentTerminalChartScale
import OAI.Hierarchy.DescentPrivateShapeNumbers
import OAI.Hierarchy.DescentTerminalNativeLimits
import OAI.Hierarchy.DescentOperandStateCodec

namespace OAI
/-! # A single short field width for all dated operand records -/
namespace Hierarchy.DescentOperandWidth
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentOperandStateBanks
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)

/-- All fields use this same width at every stage, including the immutable
full original copy of an exterior operand. The raw digit includes the role
in the per-source ordinary cable ticket. -/
def publicCap := 2^(8+S.capGain*S.length)
def slices := S.epochPower^(S.localGrainExponent+S.localCapacityExponent)
def raw := 11*publicCap S+12
def bound (drift degree : ℕ) := max (max (NativeBranch.privateSlotCapacity G S drift) (slices S))
  (max (NativeBranch.localLimit G S) (max (raw S) degree))
def s (k tail drift degree : ℕ) := max 2 (max (S.stampBits k tail) (1+Nat.log 2 (bound G S drift degree)))

theorem wide (k tail drift degree : ℕ) : 2≤ s G S k tail drift degree :=Nat.le_max_left ..

theorem numeric {k tail drift degree a : ℕ} (h : a≤bound G S drift degree) :
    a<2^(s G S k tail drift degree) := by
  have log := Nat.lt_pow_succ_log_self (by decide : 1<2) (bound G S drift degree)
  have exponent : Nat.log 2 (bound G S drift degree)+1≤ s G S k tail drift degree := by
    unfold s
    omega
  exact (h.trans_lt log).trans_le (Nat.pow_le_pow_right (by decide) exponent)

theorem original {k tail drift degree : ℕ} (base : S.baseGroups=2^tail) (radix : S.radix=2^k) (j : Fin S.copies) :
    j.val<2^(s G S k tail drift degree) :=
  (S.stamp_room base radix j).trans_le (Nat.pow_le_pow_right (by decide)
    ((Nat.le_max_left ..).trans (Nat.le_max_right ..)))

theorem privateName {k tail drift degree : ℕ} (v : Fin (NativeBranch.privateSlotCapacity G S drift)) :
    v.val+1<2^(s G S k tail drift degree) := by
  apply numeric
  exact (show v.val+1≤NativeBranch.privateSlotCapacity G S drift from v.isLt).trans
    ((Nat.le_max_left ..).trans (Nat.le_max_left ..))

theorem cableName {k tail drift degree i outgoing role : ℕ}
    (age : i≤S.length) (atMost : outgoing≤2^(8+S.capGain*i)) (allowed : role≤11) :
    11*outgoing+role<2^(s G S k tail drift degree) := by
  have cap : outgoing≤publicCap S :=
    atMost.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_left _ age) 8))
  have first : 11*outgoing+role≤raw S := by unfold raw;omega
  exact numeric G S (first.trans ((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))))

theorem rangeField {k tail drift degree value : ℕ} (starts : value≤ slices S) :
    value<2^(s G S k tail drift degree) :=
  numeric G S (starts.trans ((Nat.le_max_right ..).trans (Nat.le_max_left ..)))

theorem peer {k tail drift degree : ℕ} (v : Fin degree) :
    v.val<2^(s G S k tail drift degree) :=
  numeric G S (v.isLt.le.trans ((Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))))

/-- Only the eventual lower cutoff on J depends on the tail coefficient.
The width exponent is uniform in that coefficient, including the copy stamp. -/
theorem scale_bound (k J t τ κ drift degree e : ℕ) (dates : S.length=(t+1)*J) (active : k≤κ*(J+1))
    (late : τ+κ*(t+2)≤2^(J+1)) (small : bound G S drift degree≤2^(scale J e)) :
    s G S k (τ*(J+1)) drift degree≤ scale J (max 3 (e+1)) := by
  have stamp:=S.stamp_width J t k τ κ dates active
  have jl : J+1≤2^(J+1):=(Nat.lt_two_pow_self).le
  have three : S.stampBits k (τ*(J+1))≤ scale J 3 := by
    refine stamp.trans ((Nat.mul_le_mul late (Nat.pow_le_pow_left jl 2)).trans_eq ?_)
    unfold scale
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  have lg : Nat.log 2 (bound G S drift degree)≤ scale J e := by
    have m:=Nat.log_mono_right (b:=2) small
    simpa only [Nat.log_pow (by decide : 1<2)] using m
  have double : 1+Nat.log 2 (bound G S drift degree)≤ scale J (e+1) := by
    rw [←scale_mul]
    have positive : 0<scale J e:=Nat.two_pow_pos _
    have two : 2≤ scale J 1 := by unfold scale;rw [Nat.one_mul,pow_succ];have:=Nat.two_pow_pos J;omega
    calc _≤ scale J e*2 := by omega
         _≤_ := Nat.mul_le_mul_left _ two
  have monotone {x y : ℕ} (less : x≤y) : scale J x≤ scale J y :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ less)
  have head : 2≤ scale J 3 := by
    change 2^1≤2^_
    apply Nat.pow_le_pow_right (by decide)
    omega
  exact max_le (head.trans (monotone (Nat.le_max_left ..)))
    (max_le (three.trans (monotone (Nat.le_max_left ..))) (double.trans (monotone (Nat.le_max_right ..))))


/-- The three interval counters additionally include an offset in the current p-bit word. -/
def recordBits (k tail drift degree p : ℕ) :=
  max (s G S k tail drift degree) (Nat.log 2 p+1)

theorem bitOffset {k tail drift degree p i : ℕ} (inside : i≤p) :
    i<2^(recordBits G S k tail drift degree p) :=
  (inside.trans_lt (Nat.lt_pow_succ_log_self (by decide : 1<2) p)).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_right ..))

theorem runLength {k tail drift degree p i : ℕ} (room : i≤drift+1) :
    i<2^(recordBits G S k tail drift degree p) := by
  have positive : 0<S.epochPower^(operandExponent G S+S.localTokenExponent) :=
    pow_pos (Nat.two_pow_pos _) _
  have size : drift+1≤NativeBranch.privateSlotCapacity G S drift := by
    unfold NativeBranch.privateSlotCapacity
    exact Nat.le_mul_of_pos_right _ positive
  exact (numeric G S (room.trans (size.trans ((Nat.le_max_left ..).trans (Nat.le_max_left ..)))))
    |>.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))

/-- A public bound on the raw field values. It only uses the old stencil degree,
private drift, gadget, and the prices of the fixed calendar. -/
def rate (r d : ℕ) :=
  max (max (r+operandExponent G S+S.localTokenExponent)
      (S.localGrainExponent+S.localCapacityExponent))
    (max ((2*G.b+1)+S.localCapacityExponent) (max (5+S.localCapacityExponent) d))

private theorem mono {J x y : ℕ} (h : x≤y) : scale J x≤ scale J y :=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h)

theorem value_bound (drift degree r d : ℕ) (hr : drift+1≤ scale S.height r)
    (hd : degree≤ scale S.height d) : bound G S drift degree≤ scale S.height (rate G S r d) := by
  let J:=S.height
  have period (a : ℕ) : S.epochPower^a≤ scale J a := by
    change (2^J)^a≤2^(a*(J+1))
    rw [←pow_mul,Nat.mul_comm J a]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.le_succ _))
  have cap : publicCap S≤ scale J S.localCapacityExponent := by
    apply Nat.pow_le_pow_right (by decide)
    change 8+S.capGain*((S.rounds+1)*J)≤(8+S.capGain*(S.rounds+1))*(J+1)
    have eqn : (8+S.capGain*(S.rounds+1))*(J+1)=
        (8+S.capGain*((S.rounds+1)*J))+(8*J+S.capGain*(S.rounds+1)) := by ring
    rw [eqn]
    exact Nat.le_add_right ..
  have exponent (a : ℕ) : a≤a*(J+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have privateBound : NativeBranch.privateSlotCapacity G S drift≤ scale J (r+operandExponent G S+S.localTokenExponent) := by
    rw [Nat.add_assoc,←scale_mul]
    exact Nat.mul_le_mul hr (period _)
  have lb : NativeBranch.localLimit G S≤ scale J ((2*G.b+1)+S.localCapacityExponent) := by
    rw [←scale_mul]
    apply Nat.mul_le_mul _ cap
    exact (Nat.lt_two_pow_self (n:=2*G.b)).le.trans (Nat.pow_le_pow_right (by decide)
      ((Nat.le_succ _).trans (exponent _)))
  have rb : raw S≤ scale J (5+S.localCapacityExponent) := by
    rw [←scale_mul]
    have pos : 0<publicCap S := Nat.two_pow_pos _
    have coeff : 32≤ scale J 5 := Nat.pow_le_pow_right (by decide : 0<2) (exponent 5)
    exact (show raw S≤32*publicCap S by unfold raw;omega).trans (Nat.mul_le_mul coeff cap)
  unfold bound rate
  exact max_le
    (max_le (privateBound.trans (mono ((Nat.le_max_left ..).trans (Nat.le_max_left ..))))
      ((period _).trans (mono ((Nat.le_max_right ..).trans (Nat.le_max_left ..)))))
    (max_le (lb.trans (mono ((Nat.le_max_left ..).trans (Nat.le_max_right ..))))
      (max_le (rb.trans (mono ((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..)))))
        (hd.trans (mono ((Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..)))))))

/-- On the actual calendar all seven widths have a single residual exponent
three. The eventual lower cutoff may depend on the fixed numerical parameters. -/
theorem calendar_scale (k τ κ drift degree r d p h B : ℕ) (hb : 0<B)
    (epoch : S.height=Nat.log 2 h/(2*B)) (word : p≤h) (active : k≤κ*(S.height+1))
    (driftRoom : drift+1≤ scale S.height r) (degreeRoom : degree≤ scale S.height d)
    (late : max (τ+κ*(S.rounds+2)) (max (rate G S r d+1) (2*B))≤2^(S.height+1)) :
    recordBits G S k (τ*(S.height+1)) drift degree p≤ scale S.height 3 := by
  let J:=S.height
  have cutoff₁ : τ+κ*(S.rounds+2)≤2^(J+1):=(Nat.le_max_left ..).trans late
  have cutoff₂ : rate G S r d+1≤2^(J+1):=(Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans late)
  have cutoff₃ : 2*B≤2^(J+1):=(Nat.le_max_right ..).trans ((Nat.le_max_right ..).trans late)
  have tick : J+1≤2^(J+1):=(Nat.lt_two_pow_self (n:=J+1)).le
  have prod : (2^(J+1))^2≤ scale J 3 := by
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have stamp := S.stamp_width J S.rounds k τ κ rfl active
  have stampFit : S.stampBits k (τ*(J+1))≤ scale J 3 := by
    refine stamp.trans ((Nat.mul_le_mul cutoff₁ (Nat.pow_le_pow_left tick 2)).trans_eq ?_)
    unfold scale
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  have lv := Nat.log_mono_right (b:=2) (value_bound G S drift degree r d driftRoom degreeRoom)
  have lg : Nat.log 2 (bound G S drift degree)≤(rate G S r d)*(J+1) := by
    simpa only [scale,Nat.log_pow (by decide : 1<2)] using lv
  have localFit : 1+Nat.log 2 (bound G S drift degree)≤ scale J 3 := by
    have top : 1+Nat.log 2 (bound G S drift degree)≤(rate G S r d+1)*(J+1) := by
      rw [Nat.add_mul,Nat.one_mul];omega
    exact top.trans ((Nat.mul_le_mul cutoff₂ tick).trans ((pow_two _).symm.le.trans prod))
  have pFit : Nat.log 2 p+1≤ scale J 3 := by
    have div : Nat.log 2 h < (J+1)*(2*B) := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0<2*B)).mp
      change Nat.log 2 h/(2*B)<S.height+1
      rw [←epoch]
      omega
    have first : Nat.log 2 p+1≤(J+1)*(2*B):=Nat.succ_le_of_lt ((Nat.log_mono_right (b:=2) word).trans_lt div)
    exact first.trans ((Nat.mul_le_mul tick cutoff₃).trans ((pow_two _).symm.le.trans prod))
  have two : 2≤ scale J 3 := by
    change 2^1≤2^_
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact max_le (max_le two (max_le stampFit localFit)) pFit


/-- Fixed drift and maximum stencil degree are part of the finite family.
The same exponent three pays all dates, all original input sizes and the
entire original copy stamp of every selected terminal operand. -/
theorem issued (drift D t f g reset τ B : ℕ) (hB : 0<B) :
    ∀ᶠ h : ℕ in Filter.atTop,let J:=Nat.log 2 h/(2*B)
      ∀M p degree : ℕ,let S:=stageNumbers G t J f g reset M (τ*(J+1))
        let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
        p≤h → degree≤D → recordBits G S k (τ*(J+1)) drift degree p≤ scale J 3 := by
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let e:=rate G (stageNumbers G t 0 f g reset 0 0) 1 1
  let C:=max (max (drift+1) D) (max (τ+κ*(t+2)) (max (e+1) (2*B)))
  filter_upwards [eventually_late C B hB] with h large
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M p degree pw dw
  let S₀:=stageNumbers G t J f g reset M (τ*(J+1))
  have late : C≤2^(J+1) := large.trans ((Nat.le_succ _).trans (Nat.lt_two_pow_self (n:=J+1)).le)
  have source : max (drift+1) D≤2^(J+1):=(Nat.le_max_left ..).trans late
  have cutoff : max (τ+κ*(t+2)) (max (e+1) (2*B))≤2^(J+1) :=(Nat.le_max_right ..).trans late
  apply calendar_scale G S₀ _ τ κ drift degree 1 1 p h B hB rfl pw
  · exact groupBits_linear ..
  · change drift+1 ≤ scale J 1
    simpa only [scale,Nat.one_mul] using (show drift+1≤2^(J+1) from (Nat.le_max_left ..).trans source)
  · change degree ≤ scale J 1
    simpa only [scale,Nat.one_mul] using (dw.trans ((Nat.le_max_right ..).trans source))
  · exact cutoff

end
end Hierarchy.DescentOperandWidth

end OAI
