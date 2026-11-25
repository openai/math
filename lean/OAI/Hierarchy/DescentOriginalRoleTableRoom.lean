import OAI.Hierarchy.DescentOriginalRoleWordBits
import OAI.Hierarchy.DescentTerminalRawRoleRoom
import OAI.Hierarchy.DescentChosenExteriorHeadWidths
import OAI.Hierarchy.DescentChosenGrainRoom

namespace OAI
/-! # The role dictionary between the last dated register and the exterior replay -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentPrimitivePalette Filter
noncomputable section
variable {F:Type} [Field F] (G : PoweredGadget F) (op:RotorSpec)

variable (t f g rate τ β drift:ℕ)
def RoleWordsAt (h:ℕ) : Prop :=
  let J:=Nat.log 2 h/(2*β)
  let k:=groupBits t J (hostRate t rate) (capRate G t g) (cutRate t f g)
  ∀M,let S:=stageNumbers G t J f g rate M (tail τ J)
    DescentTerminalRoleTables.count (originalRoleBits G op S (headGrain G S k h) drift)≤2^(h/2)

theorem original_role_words (branch:G.b≤2^(capRate G t g)) (positive:0<β)
    (budget:2*(τ+groupRate G t f g rate+(6*(terminalDegree G t f g rate+1)+19))≤β) :
    ∀ᶠ h:ℕ in atTop,RoleWordsAt G op t f g rate τ β drift h:=by
  filter_upwards [terminal_raw_room G op drift t f g rate τ β branch positive budget] with h bound
  intro M S
  let age := Nat.log 2 h / (2 * β)
  let k := groupBits t age (hostRate t rate) (capRate G t g) (cutRate t f g)
  let p:=headGrain G S k h
  let N:=S.epochPower^S.localTokenExponent
  let groups:=S.groupCount S.length
  have live:0<groups:=by
    change 0<S.baseGroups*S.radix^(S.length-S.length)
    rw [Nat.sub_self,pow_zero,Nat.mul_one]
    exact Nat.two_pow_pos _
  have seed:S.firstWidth G.b p≤h:=S.split_first_width G.b h _ _ (Nat.two_pow_pos _)
  have raw:=bound M p 0 (S.grain_le_payload G.b p h G.base_pos seed) (Nat.zero_le _)
  have enough : 32*(groups*actualRawSpan G S op p drift)≤h:=
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right groups (Nat.two_pow_pos k)))).trans raw
  exact DescentTerminalRoleTables.price
    (role_words_room (DescentPrimitivePalette.colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
      (max 8 (2^S.capGain)) (NativeBranch.privateSlotCapacity G S drift) p drift N groups h enough live)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
