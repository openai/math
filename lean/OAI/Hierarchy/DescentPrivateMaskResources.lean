import OAI.Hierarchy.DescentPrivateMaskArena
import OAI.Hierarchy.DescentPrivateMaskPrice

namespace OAI
/-! # The full masked scalar gate, at the chosen physical split and a single memory width -/
namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler DescentCompiler.TerminalScale Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem physical_grain_le (h socket split : ℕ) (used : 0<socket) :
    split*(h/(16*(socket*split)))≤h := by
  have small : split≤16*(socket*split) :=(Nat.le_mul_of_pos_left _ used).trans
    (Nat.le_mul_of_pos_left _ (by decide : 0<16))
  calc
    _ ≤ (16*(socket*split))*(h/(16*(socket*split))) := Nat.mul_le_mul_right _ small
    _ = (h/(16*(socket*split)))*(16*(socket*split)) := Nat.mul_comm _ _
    _ ≤ h := Nat.div_mul_le_self _ _

theorem stage_mask_resources (t f g reset e apertureRate τ B prior c : ℕ)
    (reserve : 5+(hostRate t reset*(t+1)+1)+e≤τ) (bought : 2*apertureRate+1≤B)
    (cpu : max (clockRate G t f g reset τ) (privateMaskArenaRate G t f g reset τ prior)≤c) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M base socket split cells cap : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
      M≤2^(2*h) → 2^h≤2*(M*S.copies) → 0<socket → 0<split → socket≤ scale J e →
      socket*split≤ scale J apertureRate → cap≤2^(h/2) → base≤2^(prior*h) → cells≤2*cap+9*S.radix →
      let p:=split*(h/(16*(socket*split)))
      let W:=c*h
      let homes:=S.hostSize S.length
      Nat.log 2 (privateMax G S p)+1≤W ∧ base+cells+cap+homes+homes+3<2^W ∧
      (privateMaskedClock cells cap homes S.radix p+privateMaskedNames cells cap S.radix p)*W*S.epochPower≤
        3213*c*((M*S.copies)*p) := by
  have bank : privateMaskArenaRate G t f g reset τ prior≤c :=(le_max_right ..).trans cpu
  have size : clockRate G t f g reset τ≤c :=(le_max_left ..).trans cpu
  filter_upwards [stage_home_clock_split G t f g reset e apertureRate τ B reserve bought,
    stage_mask_arena G t f g reset τ B prior (by omega) (by omega),eventually_ge_atTop (1:ℕ)] with h gate arena hh
  dsimp only
  intro M base socket split cells cap slots funded used live source both page old rom
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let p:=split*(h/(16*(socket*split)))
  have positive : 0<M := by
    by_contra! zero
    obtain rfl: M=0:=by omega
    have impossible : 2^h≤0 := by simp at funded
    exact (Nat.not_lt_of_ge impossible) (Nat.two_pow_pos _)
  have radix : 0<S.radix:=Nat.two_pow_pos _
  have homes : 0<S.hostSize S.length := Nat.mul_pos positive (pow_pos (Nat.mul_pos (Nat.two_pow_pos _) radix) _)
  have packed : p≤h := physical_grain_le h socket split used
  have value:=private_clock_chosen G t f g reset M τ p h B hh (by omega) slots packed
  have price:=gate M socket split cap (c*h) c funded used live source both page (le_refl _)
  exact ⟨value.trans (Nat.mul_le_mul_right h size),(arena M base cells cap slots old page rom).trans_le
    (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_right h bank)),masked_home_bill rom homes price⟩

end Hierarchy.DescentSixParty.NativeBranch

end OAI
