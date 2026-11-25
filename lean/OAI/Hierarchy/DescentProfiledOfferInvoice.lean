import OAI.Hierarchy.DescentProfiledOrdinaryOffer
import OAI.Hierarchy.DescentRegisteredOrdinaryStep

namespace OAI
/-! The native program priced for a particular funded profile is exactly the
ordinary instruction of its original named ticket. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler TerminalScale Chronology DescentPacking.PackedMatch.Local.Stage DescentDatedAddressBook
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {G : PoweredGadget F} {n d : ℕ} {board : NonlinearExpanders.Graph n d}
  {op : RotorSpec} {t f g reset τ drift degreeMax B h : ℕ}
  (x : ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h)
local notation "J" => Nat.log 2 h/(2*B)
local notation "k" => groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "tb" => tail τ J
local notation "z" => x.slot
local notation "cur" => (z).position
local notation "menu" => (z).menu

abbrev CodeRoom := DatePorts.OrdinaryCodeRoom (cur).ports x.cut.ticket op g tb (z).p f drift (z).degree h
  ((menu).seats (z).age) (cur).floor (menu).ordinary (z).bus

def date (positive : 0 < k) (room : x.CodeRoom) : DateCode (z).bus :=
  DatePorts.ordinaryDate (cur).ports x.cut.ticket op g tb (z).p f drift (z).degree h
    ((menu).seats (z).age) (cur).floor (menu).ordinary (z).bus ((menu).profile (z).age) (menu).header positive room

open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall in
def HeaderRoom : Prop :=
  (menu).header ≤ (cur).floor ∧ (sourceBank ((menu).profile (z).age) ((menu).seats (z).age)
    (DescentPackedEpochShelves.grain (h/2) G.C)).Fits (z).bus (cur).floor

def Price (lead exponent share saving : ℕ) :=let S:=stageNumbers G t J f g reset (z).sites tb
  S.hostSize (z).age*h*(lead*scale J exponent)+S.hostSize (z).age*(S.groupCount (z).age*S.radix)*(lead*scale J exponent)+
    share*((z).sites/(2^J)^saving)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
