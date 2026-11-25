import OAI.Hierarchy.DescentOriginalRoleMount
import OAI.Hierarchy.DescentTerminalRoleMountCharge

namespace OAI
/-! The installed phase's one-copy allowance in the original funded terminal reel. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentTerminalCombinedRole DescentTerminalRoleTables Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)

/-- The actual terminal table installer at one public height, for every original memory placement. -/
def RoleReelAt (drift t f g reset τ B h : ℕ) : Prop :=
  ∀M p base roof w : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      ∀(endAt : base+count (originalRoleBits G op S p drift) ≤ roof) (room : roof<2^w),
      2^h ≤ M → p ≤ h →
      let mount:=originalRoleMount G op S p drift base roof endAt room
      (mount.phase.ticks+7*DescentStaticWordColumn.names mount.phase.program)*(h+1)*2^J ≤ M

theorem original_role_reel_price (drift t f g reset τ B : ℕ)
    (branch : G.b≤2^(capRate G t g)) (den : 0<B)
    (ageFit : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19)) ≤ B) :
    ∀ᶠ h : ℕ in atTop, RoleReelAt G op drift t f g reset τ B h :=by
  filter_upwards [terminal_role_mount_charge G op drift t f g reset τ B 2 1 branch den ageFit,
    eventually_ge_atTop (1:ℕ)] with h native hp
  intro M p base roof w J S endAt room copies piece mount
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  have pos : 0<S.groupCount S.length :=by
    change 0<2^(tail τ J)*S.radix^(S.length-S.length)
    rw [Nat.sub_self,pow_zero,Nat.mul_one]
    exact Nat.two_pow_pos _
  have quo:= (native M p (S.groupCount S.length) base (h+1) (fun _=>0) copies piece (by omega) pos
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k))).2
  let bits:=originalRoleBits G op S p drift
  change (4+10*count bits+7*DescentStaticWordColumn.names (DescentStaticWordColumn.program (h+1) base (fun _=>0) (count bits)))*(h+1) ≤ _ at quo
  rw [mount_charge] at quo
  rw [pow_one] at quo
  have fee : mount.phase.ticks+7*DescentStaticWordColumn.names mount.phase.program=109+115*count bits :=by
    change 4+10*count bits+7*DescentStaticWordColumn.names (DescentStaticWordColumn.program w base _ (count bits))=_
    rw [DescentStaticWordColumn.names_mount]
    ring
  rw [fee]
  exact (Nat.mul_le_mul_right (2^J) quo).trans (Nat.div_mul_le_self M (2^J))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
