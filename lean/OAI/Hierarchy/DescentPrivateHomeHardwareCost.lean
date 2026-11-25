import OAI.Hierarchy.DescentPrivateHomeClock

namespace OAI
/-! # Public hardware size of the terminal private scalar on its physical host shelf -/

namespace Hierarchy.DescentCompiler.TerminalScale

/-- This is the register, instruction-label and literal-slot bound of the actual
three-part terminal program, including the score table and static multiplier. -/
def privateHomeNames (capacity blocks p : ℕ) :=
  15*(capacity+1)+176+468*blocks+8*ProtocolRAMPortScale.bitWidth p

theorem home_names_le {capacity homes blocks p : ℕ} (live : 0<homes) :
    privateHomeNames capacity blocks p≤3*privateHomeClock capacity homes blocks p := by
  have h := Nat.le_mul_of_pos_left (16+234*blocks) live
  unfold privateHomeNames privateHomeClock
  omega

end Hierarchy.DescentCompiler.TerminalScale

namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler DescentCompiler.TerminalScale Filter

variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The same payment covers the whole public hardware at the measured CPU word width. -/
theorem stage_home_hardware (t f g reset e τ B : ℕ)
    (reserve : 5+(hostRate t reset*(t+1)+1)+e≤τ) (bought : 2*e+1≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M socket capacity W c : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
      2^h≤2*(M*S.copies) → 0< socket → socket≤ scale J e → capacity≤2^(h/2) → W≤c*h →
      let p:=h/(16*socket)
      privateHomeNames capacity S.radix p*W*S.epochPower≤1071*c*((M*S.copies)*p) := by
  filter_upwards [stage_home_clock G t f g reset e τ B reserve bought] with h price
  dsimp only
  intro M socket capacity W c fund occupied footprint rom cpu
  let S:=stageNumbers G t (Nat.log 2 h/(2*B)) f g reset M (tail τ (Nat.log 2 h/(2*B)))
  let p:=h/(16*socket)
  have pos : 0<M := by
    by_contra! hm
    have hz : M=0 := Nat.eq_zero_of_le_zero hm
    simp [hz] at fund
  have rad : 0<S.radix := Nat.two_pow_pos _
  have homes : 0<S.hostSize S.length := by
    exact Nat.mul_pos pos (pow_pos (Nat.mul_pos (Nat.two_pow_pos _) rad) _)
  have clock:=price M socket capacity W c fund occupied footprint rom cpu
  calc
    _ ≤ (3*privateHomeClock capacity (S.hostSize S.length) S.radix p)*W*S.epochPower :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (home_names_le homes))
    _ = 3*(privateHomeClock capacity (S.hostSize S.length) S.radix p*W*S.epochPower) := by ring
    _ ≤ 3*(357*c*((M*S.copies)*p)) := Nat.mul_le_mul_left _ clock
    _ = _ := by ring

end Hierarchy.DescentSixParty.NativeBranch

end OAI
