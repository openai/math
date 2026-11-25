import OAI.Hierarchy.DescentTerminalRawSpanBound
import OAI.Hierarchy.DescentTerminalRoleWordRoom
import OAI.Hierarchy.DescentTerminalRoleTableMount
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! Price of the installed physical shifts and both terminal role decoding tables. -/
namespace Hierarchy.DescentTerminalRoleTables
open DescentTerminalCombinedRole DescentCompiler Filter
noncomputable section
open scoped BigOperators
set_option quotPrecheck false

/-- The shared initializer writes each word once and pays its actual opcode labels. -/
theorem mount_charge (bits:Fin 6→ℕ) (data:ℕ→ℕ) (base w:ℕ) :
    (4+10*count bits+7*DescentStaticWordColumn.names (DescentStaticWordColumn.program w base data (count bits)))*w =
      (109+115*count bits)*w :=by
  rw [DescentStaticWordColumn.names_mount]
  ring

theorem shared_mount (ratio saving:ℕ) : ∀ᶠ h:ℕ in atTop,∀(J M base w:ℕ) (bits:Fin 6→ℕ) (data:ℕ→ℕ),
    J ≤ Nat.log 2 h → 2^h ≤ M → w ≤ ratio*h → count bits ≤ 2^(h/2) →
    (4+10*count bits+7*DescentStaticWordColumn.names (DescentStaticWordColumn.program w base data (count bits)))*w ≤
      M/(2^J)^saving :=by
  filter_upwards [global_control_shared (224*ratio) 1 0 0 saving] with h paid
  intro J M base w bits data age sites word fit
  have one : 1 ≤ 2^(h/2):=Nat.two_pow_pos _
  have bound : 109+115*count bits ≤ 224*2^(h/2):=by omega
  rw [mount_charge]
  calc
    _ ≤ (224*2^(h/2))*(ratio*h):=Nat.mul_le_mul bound word
    _ = (224*ratio*h)*2^(h/2):=by ring
    _ ≤ ((224*ratio)*(h+1)^1*2^0)*2^(h/2):=by
      simp only [pow_one,pow_zero,Nat.mul_one]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ h))
    _ ≤ _:=paid J 0 M age (Nat.zero_le _) sites

end
end Hierarchy.DescentTerminalRoleTables

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentPrimitivePalette DescentTerminalCombinedRole
open DescentResetGates DescentTerminalRoleTables Filter
open scoped BigOperators
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F)

/-- At the actual date the bought raw role rectangle pays all six shift alphabets
and both decoded menu pages, independently of any submitted row values. -/
theorem terminal_role_mount_charge (op:RotorSpec) (drift t f g reset τ B ratio saving:ℕ)
    (branch:G.b ≤ 2^(capRate G t g)) (den:0 < B)
    (ageFit:2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19)) ≤ B) :
    ∀ᶠ h:ℕ in atTop,∀M p groups base w:ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      let n:=colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
      let slots:=NativeBranch.privateSlotCapacity G S drift
      let field:=fun f:Fin 6=>width n (max 8 (2^S.capGain)) slots p drift f*
        (S.epochPower^S.localTokenExponent)*groups
      ∀data:ℕ→ℕ,2^h ≤ M → p ≤ h → w ≤ ratio*h → 0 < groups → groups ≤ S.groupCount S.length*2^k →
      count field ≤ 2^(h/2) ∧
      (4+10*count field+7*DescentStaticWordColumn.names (DescentStaticWordColumn.program w base data (count field)))*w ≤
        M/(2^J)^saving :=by
  filter_upwards [terminal_raw_room G op drift t f g reset τ B branch den ageFit,shared_mount ratio saving] with h raw fees
  intro M p groups base w J S k n slots field data sites small word positive covered
  have total:32*(groups*actualRawSpan G S op p drift) ≤ h:=
    (Nat.mul_le_mul_left 32 (Nat.mul_le_mul_right _ covered)).trans (raw M p 0 small (Nat.zero_le _))
  have fit:count field ≤ 2^(h/2):=
    DescentTerminalRoleTables.price (role_words_room n (max 8 (2^S.capGain)) slots p drift
      (S.epochPower^S.localTokenExponent) groups h total positive)
  exact ⟨fit,fees J M base w field data (Nat.div_le_self ..) sites word fit⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
