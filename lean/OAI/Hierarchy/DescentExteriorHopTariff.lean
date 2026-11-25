import OAI.Hierarchy.DescentExteriorHopPages
import OAI.Hierarchy.DescentTerminalCohortScale
import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # The total initialized memory of the exterior hop tables across all dates -/
namespace Hierarchy.DescentExteriorReplay.Snapshots
open scoped BigOperators

theorem start_eq_sum {k : ℕ} (S : Snapshots k) (base f n : ℕ) :
    S.start base f n = base+∑ j ∈ Finset.range n, HopLiteral.words (S.hosts j) k f := by
  induction n with
  | zero => simp [start]
  | succ n ih => simp only [start,ih,Finset.sum_range_succ,Nat.add_assoc]

/-- Paying every host cell at every date costs at most two final host arrays. -/
theorem start_bound {k : ℕ} (S : Snapshots k) (base f n : ℕ)
    (grow : ∀j, 2*S.hosts j ≤ S.hosts (j+1)) :
    S.start base f n ≤ base+2*S.hosts n+n*(2+2^k+2^f) := by
  induction n with
  | zero => simp [start]
  | succ n ih =>
    have one := HopLiteral.words_le (S.hosts n) k f
    have more := grow n
    rw [start,Nat.succ_mul n (2+2^k+2^f)]
    omega

/-- The existing roster bound with gain one has room for one shape and frozen
digit table per date, including their padding. -/
theorem overhead (k n : ℕ) :
    n*(2+2^k+2^(k*n)) ≤ DescentTerminalFrozenRoster.ROM.size (k*n) (8+n) := by
  cases n with
  | zero => simp
  | succ n =>
    let age:=n+1
    have kfit : k ≤ k*age := Nat.le_mul_of_pos_right _ (Nat.succ_pos n)
    have table : 2^k ≤ 2^(k*age) := Nat.pow_le_pow_right (by decide) kfit
    have nonzero : 1 ≤ 2^(k*age) := Nat.one_le_two_pow
    have each : 2+2^k+2^(k*age) ≤ 4*2^(k*age) := by omega
    have visits : 4*age ≤ 2^(8+age) := by
      have count : age ≤ 2^age := Nat.lt_two_pow_self.le
      rw [pow_add]
      change 4*age ≤ 256*2^age
      omega
    change age*(2+2^k+2^(k*age)) ≤ _
    calc
      _ ≤ age*(4*2^(k*age)) := Nat.mul_le_mul_left _ each
      _ = (4*age)*2^(k*age) := by ring
      _ ≤ 2^(8+age)*2^(k*age) := Nat.mul_le_mul_right _ visits
      _ ≤ _ := Nat.le_add_left _ _

end Hierarchy.DescentExteriorReplay.Snapshots

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentExteriorReplay Filter
open scoped Topology BigOperators
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B : ℕ)
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
local notation "schedule" => fun J M=>stageNumbers G t J f g reset M (tail τ J)
local notation "bits" => fun J=>groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)

/-- All three literal regions are initialized on the same stage scale, at every
earlier date, even when a native reset additionally consults its sparse rank map. -/
theorem stage_hop_literal_tariff (big : 10≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B); ∀ M base (R : Snapshots (bits J)),
      R.hosts=(schedule J M).hostSize →
      R.start base (bits J*((schedule J M).length)) (schedule J M).length ≤
        base+2*(schedule J M).hostSize (schedule J M).length+3*2^(h/2) := by
  filter_upwards [cohort_tables t κ 1 B big] with h ready
  intro J M base R hosts
  let age:=(t+1)*J
  let k:=bits J
  let rate:=2^(hostRate t reset)*2^k
  have kpos : 1≤k := by
    change 1≤(_+_+8)+_
    exact (show 1≤8 by decide).trans ((Nat.le_add_left 8 _).trans (Nat.le_add_right ..))
  have radix : 2≤2^k := (Nat.pow_le_pow_right (n:=2) (by decide) kpos : 2^1 ≤ 2^k)
  have expands : 2≤rate := radix.trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  have grow (j : ℕ) : 2*R.hosts j ≤ R.hosts (j+1) := by
    rw [hosts]
    change 2*(M*rate^j) ≤ M*rate^(j+1)
    calc
      2*(M*rate^j) = (M*rate^j)*2 := Nat.mul_comm ..
      _ ≤ (M*rate^j)*rate := Nat.mul_le_mul_left _ expands
      _ = M*rate^(j+1) := by rw [pow_succ,Nat.mul_assoc]
  have arena := R.start_bound base (k*age) age grow
  have tables := (ready k (groupBits_linear ..)).2
  change DescentTerminalFrozenRoster.ROM.size (k*age) (8+1*age) ≤ 3*2^(h/2) at tables
  rw [Nat.one_mul] at tables
  have extra := (Snapshots.overhead k age).trans tables
  rw [hosts] at arena
  exact arena.trans (Nat.add_le_add_left extra _)

end
end Hierarchy.DescentSixParty

end OAI
