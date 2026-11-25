import OAI.Hierarchy.DescentSeedNumberRates
import OAI.Hierarchy.DescentOperandWidth

namespace OAI
/-! # The installed operand width contains the dated donor and the full raw name -/
namespace Hierarchy.DescentOperandWidth
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem ticket_key_room (S : AtomSchedule) {k rest drift degree p cap i D : ℕ}
    (paths : (D+1)^4 ≤ 2^rest) (date : i≤S.length)
    (capacity : cap≤2^(8+S.capGain*i)) :
    (D+1)^4*2^k ≤ 2^(recordBits G S k rest drift degree p) ∧
      11*cap ≤ 2^(recordBits G S k rest drift degree p) :=by
  have root : S.stampBits k rest ≤ s G S k rest drift degree :=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have stored : s G S k rest drift degree ≤ recordBits G S k rest drift degree p :=Nat.le_max_left ..
  constructor
  · calc
      _ ≤ 2^rest*2^k :=Nat.mul_le_mul_right _ paths
      _ = 2^(rest+k) :=(pow_add ..).symm
      _ ≤ _ :=by
        apply Nat.pow_le_pow_right (by decide)
        apply le_trans _ (root.trans stored)
        change rest+k≤rest+k*(S.length-0)+k
        omega
  · have raw:=cableName G S (k:=k) (tail:=rest) (drift:=drift) (degree:=degree)
      (role:=0) date capacity (by decide)
    have fixed : 11*cap ≤ 2^(s G S k rest drift degree) :=by simpa only [Nat.add_zero] using raw.le
    exact fixed.trans (Nat.pow_le_pow_right (by decide) stored)

/-- A single cutoff covers all original round degrees, independently of the realized venue. -/
theorem eventually_ticket_key_room (t τ B : ℕ) (wide : 0<τ) (pos : 0<B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀(S : AtomSchedule) (k drift degree p cap i factor : ℕ),
        i≤S.length → cap≤2^(8+S.capGain*i) →
        (Chronology.OrdinaryLink.publicDegree t (2^k) factor+1)^4*2^k ≤
          2^(recordBits G S k (tail τ J) drift degree p) ∧
        11*cap ≤ 2^(recordBits G S k (tail τ J) drift degree p) :=by
  let lim:=(DescentDatedSeedStartup.initialDegreeMax t+1)^4
  filter_upwards [eventually_late lim B pos] with h late
  dsimp only
  intro S k drift degree p cap i factor date capacity
  apply ticket_key_room G S _ date capacity
  have bound := DescentDatedSeedStartup.seed_degree t (2^k) factor
  have first : (Chronology.OrdinaryLink.publicDegree t (2^k) factor+1)^4 ≤ lim :=
    Nat.pow_le_pow_left (Nat.add_le_add_right bound 1) 4
  apply (first.trans late).trans
  have one : Nat.log 2 h/(2*B) ≤ tail τ (Nat.log 2 h/(2*B)) :=by
    unfold tail
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ wide)
  exact one.trans Nat.lt_two_pow_self.le

/-- Even an unselected or malformed earlier matcher may report the doubled slot
range. At every ordinary date the published terminal capacity has at least one
remaining doubling, and the role digit has the original eleven-value alphabet. -/
theorem ticket_ordinal_room (S : AtomSchedule) {k rest drift degree p i cap : ℕ}
    (gain : 0 < S.capGain) (date : i < S.length) (capacity : cap≤2^(8+S.capGain*i)) :
    22*cap+10 < 2^(recordBits G S k rest drift degree p) :=by
  have stage := Nat.mul_le_mul_left S.capGain (show i+1≤S.length from date)
  rw [Nat.mul_add,Nat.mul_one] at stage
  have growth := Nat.pow_le_pow_right (by decide : 0<2)
    (show (8+S.capGain*i)+1≤8+S.capGain*S.length by omega)
  rw [pow_succ] at growth
  have inside : 22*cap+10≤raw S :=by unfold raw publicCap;omega
  have deep : 22*cap+10≤bound G S drift degree :=
    inside.trans ((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..)))
  exact (numeric G S (k:=k) (tail:=rest) deep).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_left ..))

theorem stage_ticket_ordinal_room (t J f g reset M rest k drift degree p i cap : ℕ)
    (date : i < (stageNumbers G t J f g reset M rest).length)
    (capacity : cap ≤ 2^(8+(stageNumbers G t J f g reset M rest).capGain*i)) :
    22*cap+10 < 2^(recordBits G (stageNumbers G t J f g reset M rest) k rest drift degree p) :=by
  apply ticket_ordinal_room G _ _ date capacity
  change 0<capRate G t g
  unfold capRate
  omega

end Hierarchy.DescentOperandWidth

end OAI
