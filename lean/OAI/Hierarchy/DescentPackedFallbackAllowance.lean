import OAI.Hierarchy.DescentResetRosterFunctions
import OAI.Hierarchy.DescentClosedReset
import OAI.Hierarchy.DescentOccurrenceAllowance
import OAI.Hierarchy.DescentPackedFallbackWidthBits
import OAI.Hierarchy.DescentResetCableSlots
import OAI.Hierarchy.DescentStackScale

namespace OAI
/-! # Local width of the fallback panel of a physically issued reset -/
noncomputable section
namespace Hierarchy
open scoped Classical
namespace DescentCompiler.AtomSchedule

def fallbackExponent (S : AtomSchedule) (cut : ℕ) :=
  2*(1+(S.hostGain+S.capGain)*(S.rounds+1)+8+cut)+S.localCapacityExponent+1

theorem fallback_slots (S : AtomSchedule) {k cut cap i : ℕ}
    (hj : 0<S.height) (age : i≤S.length) (capBound : cap≤2^(8+S.capGain*i))
    (key : k=groupBits S.rounds S.height S.hostGain S.capGain cut) :
    2^k*(2*cap) ≤ S.epochPower^(S.fallbackExponent cut) := by
  let rate:=1+(S.hostGain+S.capGain)*(S.rounds+1)+8+cut
  have keyBits : k≤rate*(S.height+1) := by
    rw [key]
    exact groupBits_linear ..
  have keyPaid : 2^k≤S.epochPower^(2*rate) := by
    unfold epochPower
    rw [←pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    calc
      k ≤ rate*(S.height+1) := keyBits
      _ ≤ rate*(2*S.height) := Nat.mul_le_mul_left _ (by omega)
      _ = S.height*(2*rate) := by ring
  have two : 2≤S.epochPower :=
    Nat.one_lt_two_pow (show S.height≠0 from hj.ne')
  have capPaid:=S.local_capacity hj age capBound
  calc
    2^k*(2*cap) ≤ S.epochPower^(2*rate)*(S.epochPower*S.epochPower^S.localCapacityExponent) :=
      Nat.mul_le_mul keyPaid (Nat.mul_le_mul two capPaid)
    _ = S.epochPower^(S.fallbackExponent cut) := by
      change _=S.epochPower^(2*rate+S.localCapacityExponent+1)
      rw [pow_succ,pow_add]
      ring

end DescentCompiler.AtomSchedule

namespace DescentPackedFallbackTree
open Filter DescentCompiler

/-- Fixed factors from the local template height and the genuine number of cable slots. -/
def columnFactor (H rootCap : ℕ) := (H+3)*(5*rootCap+1)

theorem all_columns_le (H n rootCap : ℕ) :
    max (width H n) (fieldWidth H n*(5*rootCap)) ≤ columnFactor H rootCap*(n+1) := by
  have fit : H+2≤(H+2)*(n+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have field : fieldWidth H n≤(H+3)*(n+1) := calc
    _ ≤ (H+2)*(n+1)+(n+1) := Nat.add_le_add fit (Nat.log_le_self 2 _)
    _ = _ := by ring
  have source : width H n≤(H+3)*(n+1) := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have reserve : (H+3)*(n+1)≤(H+3)*(n+1)*(5*rootCap+1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have both:=max_le (source.trans reserve) (Nat.mul_le_mul field (Nat.le_succ (5*rootCap)))
  simpa only [columnFactor,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using both

theorem columns_room {T n e H rootCap B height : ℕ} (positive : 2≤T)
    (slots : n≤T^e) (budget : e+Nat.clog 2 (columnFactor H rootCap)≤B)
    (room : 32*T^B≤height) :
    2*max (width H n) (fieldWidth H n*(5*rootCap))≤height := by
  let K:=columnFactor H rootCap
  have fixed : K≤T^(Nat.clog 2 K) := (Nat.le_pow_clog (by decide : 1<2) K).trans
    (Nat.pow_le_pow_left positive _)
  have joined : K*T^e≤T^B := calc
    _ ≤ T^(Nat.clog 2 K)*T^e := Nat.mul_le_mul_right _ fixed
    _ = T^(e+Nat.clog 2 K) := by rw [pow_add,Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) budget
  have big : 1≤T^e := Nat.pow_pos (by omega)
  have invoice:=Nat.mul_le_mul_left 2 (all_columns_le H n rootCap)
  calc
    _ ≤ 2*(K*(n+1)) := invoice
    _ ≤ 2*(K*(2*T^e)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left K (by omega))
    _ = 4*(K*T^e) := by ring
    _ ≤ 32*T^B := Nat.mul_le_mul (by decide) joined
    _ ≤ _ := room

theorem eventual_columns_room (H cap e B : ℕ) (positive : 0<B)
    (budget : e+Nat.clog 2 (columnFactor H cap)≤B) :
    ∀ᶠ h : ℕ in atTop, ∀ n≤(2^(Nat.log 2 h/(2*B)))^e,
      2*max (width H n) (fieldWidth H n*(5*cap))≤h := by
  filter_upwards [age_room B positive] with h allocation
  intro n slots
  exact columns_room (Nat.one_lt_two_pow allocation.1.ne') slots budget allocation.2

end DescentPackedFallbackTree

namespace DescentSixParty.ClosedReset
open DescentCompiler DescentPackedFallbackTree

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z wire hist : ℕ} {W : MarkedWorld F d P bits}
  {D n h C f g cut tail : ℕ} {input : Reached W G q ε S k i z D wire hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (Z : ClosedReset input ctl)

def fallbackSlots := 2^(Z.reset.k-Z.terminals.commonDepth)*(2*input.placement.cap)

theorem fallbackSlots_paid (age : i≤S.length) :
    Z.fallbackSlots≤S.epochPower^(S.fallbackExponent cut) := by
  unfold fallbackSlots
  rw [Z.keyWidth,Z.commonDepth,Nat.add_sub_cancel_left]
  exact S.fallback_slots ctl.height age input.valid.capacity ctl.fixed

/-- The SIMD lookup tariff's input/output lane condition for this actual panel,
including all five short fields at each available private cable address. -/
theorem fallback_columns_paid (age : i≤S.length) (B physical : ℕ)
    (budget : S.fallbackExponent cut+Nat.clog 2 (columnFactor (GroupStage.depthBound D n f g)
      (DescentResetCableSlots.cableCap ctl.board (GroupStage.depthBound D n f g)))≤B)
    (room : 32*S.epochPower^B≤physical) :
    let Ht:=GroupStage.depthBound D n f g
    let rootCap:=DescentResetCableSlots.cableCap ctl.board Ht
    2*max (DescentPackedFallbackTree.width Ht Z.fallbackSlots) (fieldWidth Ht Z.fallbackSlots*(5*rootCap))≤physical :=
  columns_room (Nat.one_lt_two_pow ctl.height.ne') (Z.fallbackSlots_paid age) budget room

/-- At the actual logarithmic epoch the width follows from arithmetic on the
external word height, with a fixed threshold independent of all residual groups. -/
theorem fallback_columns_at_height (age : i≤S.length) (B physical : ℕ)
    (budget : S.fallbackExponent cut+Nat.clog 2 (columnFactor (GroupStage.depthBound D n f g)
      (DescentResetCableSlots.cableCap ctl.board (GroupStage.depthBound D n f g)))≤B)
    (height : S.height=Nat.log 2 physical/(2*B)) (large : 2^(2*B+10)≤physical) :
    let Ht:=GroupStage.depthBound D n f g
    let rootCap:=DescentResetCableSlots.cableCap ctl.board Ht
    2*max (DescentPackedFallbackTree.width Ht Z.fallbackSlots) (fieldWidth Ht Z.fallbackSlots*(5*rootCap))≤physical := by
  apply Z.fallback_columns_paid age B physical budget
  have nz : physical≠0 := ((Nat.two_pow_pos _).trans_le large).ne'
  have exponent : 2*B+10≤Nat.log 2 physical :=
    (Nat.le_log_iff_pow_le (by decide) nz).mpr large
  have used : S.height*(2*B)≤Nat.log 2 physical := by
    rw [height]
    exact Nat.div_mul_le_self _ _
  have paid : 5+S.height*B≤Nat.log 2 physical :=
    by nlinarith only [used,exponent,Nat.zero_le B]
  change 2^5*(2^S.height)^B≤physical
  rw [←pow_mul,←pow_add]
  exact (Nat.le_log_iff_pow_le (by decide) nz).mp paid

end DescentSixParty.ClosedReset
end Hierarchy
end

end OAI
