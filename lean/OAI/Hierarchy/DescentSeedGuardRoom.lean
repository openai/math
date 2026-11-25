import OAI.Hierarchy.DescentSeedTokenLaneFit
import OAI.Hierarchy.DescentSeedPrintedPitch
import OAI.Hierarchy.DescentStackScale

namespace OAI
/-! # Native width guards on the arbitrary original ballot checker and its retained primitive pages -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentSIMDLookup DescentSeedRoot DescentPrimitivePalette Filter
variable {F : Type} [Field F] (D : PoweredGadget F) (op : RotorSpec)

theorem primitive_word_room (B κ : ℕ) (positive : 0 < B) (enough : κ+3+6 ≤ B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀s Z k : ℕ,s ≤ h → Z ≤ s → 2^k ≤ scale J κ →
        16*digitsNeeded s ≤ h ∧ 0 < Primitive.paletteLanes D op s Z h k ∧
        printedBits D s Z op*Primitive.paletteLanes D op s Z h k ≤ h/2 :=by
  filter_upwards [primitive_rate D op B positive,age_room B positive,eventually_ge_atTop 1] with h widths age high
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro s Z k src grain blocks
  obtain ⟨print,raw,dg⟩:=widths s Z grain src
  have mono (n : ℕ) (le : n ≤ κ+3) : scale J n ≤ scale J (κ+3) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)
  have cap : max (DescentPackedSeed.Primitive.roleBits s*2^k) (printedBits D s Z op) ≤ scale J (κ+3) :=
    max_le ((Nat.mul_le_mul raw blocks).trans_eq (by rw [scale_mul,Nat.add_comm 3]))
      (print.trans (mono 3 (by omega)))
  have tall:=token_epoch_room h B (κ+3) high age.1 enough
  have digits:=dg.trans (mono 2 (by omega))
  refine ⟨(Nat.mul_le_mul_left 16 digits).trans tall,?_,Primitive.chosen_printed_half D op s Z h k⟩
  have rp : 0 < DescentPackedSeed.Primitive.roleBits s:=Nat.zero_lt_succ _
  have inc := (Nat.mul_pos rp (Nat.two_pow_pos k)).trans_le
    (Nat.le_max_left (DescentPackedSeed.Primitive.roleBits s*2^k) (printedBits D s Z op))
  exact (occupancy h (4*max (DescentPackedSeed.Primitive.roleBits s*2^k) (printedBits D s Z op))
    (by omega) (by nlinarith only [tall,cap])).1

end Hierarchy.DescentDatedSeedStartup

end OAI
