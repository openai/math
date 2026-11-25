import OAI.Hierarchy.DescentRegisteredPriorRows
import OAI.Hierarchy.DescentRegisteredInputNumbers
import OAI.Hierarchy.DescentIssuedOrdinaryInvoice

namespace OAI
/-! # The two physical prior-field sweeps in an ordinary registered argument entry -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentSIMDLookup DescentOrdinaryPriorPad DescentStaticWordColumn
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (a : ArgumentEntry v) (floor w : ℕ)

def inputFee :=
  phaseCharge w (7*w) (DescentOrdinaryPriorPad.phase a.previous a.clip.venue.hosts a.clip.working
    (a.priorStart v floor) a.previousBase w)+
  phaseCharge w (7*w) ((a.roleLayout v).phase (a.roleStart v floor) a.role w)

local notation "old" => a.previous
local notation "rod" => a.roleLayout v
local notation "lanes₁" => a.clip.working
local notation "H₁" => a.clip.venue.hosts
local notation "G₁" => a.clip.venue.groups

theorem input_charge (A h ratio u : ℕ) (live : 0<A)
    (groups : (old).groups=G₁)
    (oldHosts : 0<(old).hosts ∧ (old).hosts≤2*A) (newHosts : H₁≤2*A)
    (short : DescentOrdinaryPriorRetile.digits old*(old).lanes≤h/2 ∧ (rod).bits*(rod).beforeLanes≤h/2)
    (bounded : 0<(old).lanes ∧ (old).lanes≤h ∧ 0<(rod).beforeLanes ∧ (rod).beforeLanes≤h)
    (rows : (old).hosts*chunks (old).groups (old).lanes*h≤(old).hosts*h+(old).hosts*(old).groups*u ∧
      (rod).oldHosts*chunks (rod).groups (rod).beforeLanes*h≤(rod).oldHosts*h+(rod).oldHosts*(rod).groups*u)
    (out : 0<lanes₁ ∧ lanes₁≤h ∧ h≤lanes₁*u) (bus : w≤ratio*h) :
    v.inputFee a floor w ≤ ratio*(MaterialProgram.retileFactor (DescentOrdinaryPriorRetile.pages old) u+
      MaterialProgram.retileFactor (rod).blocks u)*MaterialProgram.purchased A G₁ h :=by
  let arg:=DescentOrdinaryPriorPad.phase old H₁ lanes₁ (a.priorStart v floor) a.previousBase w
  let roles:=(rod).phase (a.roleStart v floor) a.role w
  have first:=DescentOrdinaryPriorPad.padded_word_rows old H₁ lanes₁ (a.priorStart v floor) a.previousBase
    w h ratio u u bounded.1 out.1 oldHosts.1 bounded.2.1 out.2.1 short.1 rows.1 out.2.2 bus
  have next:=DescentOrdinaryRoleHostPad.Layout.word_rows rod (a.roleStart v floor) a.role w h ratio u u
    bounded.2.2.1 out.1 oldHosts.1 bounded.2.2.2 out.2.1 short.2 rows.2 out.2.2 bus
  have bound₀ : arg.wordInvoice≤MaterialProgram.retileCharge ratio (DescentOrdinaryPriorRetile.pages old)
    (old).hosts H₁ G₁ h u :=by
    simpa only [MaterialProgram.retileCharge,MaterialProgram.halfPages,←groups,Nat.mul_assoc] using first
  have bound₁ : roles.wordInvoice≤MaterialProgram.retileCharge ratio (rod).blocks (old).hosts H₁ G₁ h u:=by
    change (roles.ticks+7*names roles.program)*w ≤ _
    simpa only [roles,MaterialProgram.retileCharge,MaterialProgram.halfPages,ArgumentEntry.roleLayout,Nat.mul_assoc] using next
  have total:=Nat.add_le_add (bound₀.trans (MaterialProgram.retile_charge live oldHosts.2 newHosts))
    (bound₁.trans (MaterialProgram.retile_charge live oldHosts.2 newHosts))
  have price (p : NativePhase w) : phaseCharge w (7*w) p=p.wordInvoice:=by
    unfold phaseCharge codeCharge NativePhase.wordInvoice DescentPacking.PackedMatch.Local.Stage.DateBill.bitTariff
    ring
  calc
    _ = arg.wordInvoice+roles.wordInvoice:=congrArg₂ (·+·) (price arg) (price roles)
    _ ≤ _:=total.trans_eq (by ring)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
