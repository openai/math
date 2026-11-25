import OAI.Hierarchy.DescentPrivateHostCalendar

namespace OAI
/-! # Complete native cost of the authenticated terminal used-word register -/
namespace Hierarchy.DescentCompiler.TerminalScale

/-- Literal score-page install, one native masked-shelf scan, one prefix scan, and the
final grain conversion and subtraction (including its exact static multiplier). -/
def privateHomeClock (capacity homes blocks p : ℕ) :=
  ((4+10*capacity)+(4+homes*(16+234*blocks)))+(13+12*homes)+(56+4*ProtocolRAMPortScale.bitWidth p)

theorem home_clock {h W c capacity homes blocks M copies p T : ℕ}
    (cpu : W≤ c*h) (width : p≤h) (rom : capacity≤2^(h/2)) (block : 0<blocks)
    (headFee : (2^(h/2)*h)*T≤(M*copies)*p) (siteFee : homes*blocks*h*T≤(M*copies)*p) :
    privateHomeClock capacity homes blocks p*W*T≤357*c*((M*copies)*p) := by
  let U:=2^(h/2)
  have one : 1≤U := Nat.one_le_two_pow
  have high : h/2+1≤U := Nat.lt_two_pow_self
  have index : ProtocolRAMPortScale.bitWidth p≤2*U := by
    have log:=Nat.log_le_self 2 p
    unfold ProtocolRAMPortScale.bitWidth
    omega
  have h₁ : 77+10*capacity+4*ProtocolRAMPortScale.bitWidth p≤95*U := by omega
  have h₂ : 28+234*blocks≤262*blocks := by omega
  have price : privateHomeClock capacity homes blocks p≤95*U+262*(homes*blocks) := by
    unfold privateHomeClock
    calc
      _ = (77+10*capacity+4*ProtocolRAMPortScale.bitWidth p)+homes*(28+234*blocks) := by ring
      _ ≤ 95*U+homes*(262*blocks) := Nat.add_le_add h₁ (Nat.mul_le_mul_left _ h₂)
      _ = _ := by ring
  calc
    _ ≤ ((95*U+262*(homes*blocks))*(c*h))*T := Nat.mul_le_mul_right _ (Nat.mul_le_mul price cpu)
    _ = c*(95*((U*h)*T)+262*(homes*blocks*h*T)) := by ring
    _ ≤ c*(95*((M*copies)*p)+262*((M*copies)*p)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ headFee) (Nat.mul_le_mul_left _ siteFee))
    _ = _ := by ring

end Hierarchy.DescentCompiler.TerminalScale

namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler DescentCompiler.TerminalScale Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The complete native invoice holds at the actual stage, with no separate runtime
charge for unoccupied terminal hosts and no assumption about the selected branch. -/
theorem stage_home_clock_split (t f g reset e apertureRate τ B : ℕ)
    (reserve : 5+(hostRate t reset*(t+1)+1)+e≤τ) (bought : 2*apertureRate+1≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M socket split capacity W c : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
      2^h≤2*(M*S.copies) → 0< socket → 0<split → socket≤ scale J e → socket*split≤ scale J apertureRate → capacity≤2^(h/2) → W≤ c*h →
      let p:=split*(h/(16*(socket*split)))
      privateHomeClock capacity (S.hostSize S.length) S.radix p*W*S.epochPower≤357*c*((M*S.copies)*p) := by
  have pos : 0<B := by omega
  filter_upwards [age_room B pos,
    eventually_ge_atTop 10] with h viable large
  let J:=Nat.log 2 h/(2*B)
  let T:=2^J
  change 0<J ∧ 32*T^B≤h at viable
  dsimp only
  intro M socket split capacity W c fund occupied live rates footprint rom cpu
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let p:=split*(h/(16*(socket*split)))
  have socketCap : socket*split≤T^(2*apertureRate) := by
    apply footprint.trans
    change 2^(apertureRate*(J+1))≤(2^J)^(2*apertureRate)
    rw [←pow_mul]
    apply Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    have a:=Nat.mul_le_mul_left apertureRate (show J+1≤2*J by omega)
    nlinarith only [a]
  have piece : T≤h/(16*(socket*split)) := by
    apply (Nat.le_div_iff_mul_le (show 0<16*(socket*split) by positivity)).mpr
    calc
      _ ≤ T*(16*T^(2*apertureRate)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ socketCap)
      _ = 16*T^(2*apertureRate+1) := by rw [pow_succ];ring
      _ ≤ 32*T^B := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right (Nat.two_pow_pos _) bought)
      _ ≤ _ := viable.2
  have longer : h/(16*(socket*split))≤p :=
    Nat.le_mul_of_pos_left _ live
  have aperture : 32*(socket*split)≤h := by
    apply (Nat.mul_le_mul_left 32 (socketCap.trans (Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega : 2*apertureRate≤B)))).trans viable.2
  have packed:=packing_width live occupied aperture
  have inside : 16*(socket*p)≤h := by simpa only [p,Nat.mul_comm split] using packed.2.2.1
  have fits : p≤h := (Nat.le_mul_of_pos_left p occupied).trans
    ((Nat.le_mul_of_pos_left (socket*p) (by decide : 0<16)).trans inside)
  have lower : h≤32*(p*socket) := by
    simpa only [p,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using packed.2.2.2
  have sites:=stage_host_gate_budget G t J f g reset e τ h M socket p reserve rates lower
  exact home_clock cpu fits rom (Nat.two_pow_pos _)
    (Nat.mul_le_mul (table_fund large fund) (piece.trans longer)) sites

theorem stage_home_clock (t f g reset e τ B : ℕ)
    (reserve : 5+(hostRate t reset*(t+1)+1)+e≤τ) (bought : 2*e+1≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M socket capacity W c : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
      2^h≤2*(M*S.copies) → 0< socket → socket≤ scale J e → capacity≤2^(h/2) → W≤ c*h →
      let p:=h/(16*socket)
      privateHomeClock capacity (S.hostSize S.length) S.radix p*W*S.epochPower≤357*c*((M*S.copies)*p) := by
  filter_upwards [stage_home_clock_split G t f g reset e e τ B reserve bought] with h paid
  dsimp only at paid ⊢
  intro M socket capacity W c fund occupied footprint rom cpu
  simpa only [Nat.mul_one,Nat.one_mul] using
    paid M socket 1 capacity W c fund occupied (by decide) footprint (by simpa only [Nat.mul_one] using footprint) rom cpu

end Hierarchy.DescentSixParty.NativeBranch

end OAI
