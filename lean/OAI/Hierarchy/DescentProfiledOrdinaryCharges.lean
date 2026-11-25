import OAI.Hierarchy.DescentProfiledOfferInvoice
import OAI.Hierarchy.DescentRegisteredOrdinaryBill
import OAI.Hierarchy.DescentProfiledReturnCharge

namespace OAI
/-! # The eight charges in the code addressed by the original public register -/
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


open DescentPacking.PackedMatch.Local.Stage
local notation "S₀" => stageNumbers G t J f g reset (z).sites tb
local notation "ports" => (cur).ports
local notation "date₀" => Chronology.DonorDate.atDate G S₀ g k (z).age (z).p
local notation "seats" => (menu).seats (z).age
local notation "boardBits" => (S₀).censusBits (z).p
local notation "area₀" => (date₀).schedule h seats boardBits
local notation "mat" => x.base.registered_match ports x.stageFloor
  (Nat.le_max_left (ports).argumentsPerNode ((S₀).retainedArgumentsAt G drift))
local notation "geometry" => x.base.registered_geometry ports x.stageFloor
local notation "entry" => x.base.registeredEntry ports x.stageFloor
local notation "old" => (⟨(ports).archive.count,(ports).io.roster,(ports).io.hubs⟩:DescentOrdinaryVenueReturn.Sources)

def privateFee :=
  let r:=(area₀).rotationEnd (ports).io.roster x.stageFloor
  let counter:=(date₀).counter h r (menu).header
  ((date₀).afterMatcher h seats (ports).io boardBits x.stageFloor (z).bus).wordInvoice+
    DateBill.bitTariff (counter.program (z).bus) counter.ticks

def matchInvoice (live : 0 < k) :=
  let receipt:Dated.Measures:=⟨x.cut.source.placement.wire,x.cut.source.placement.z,x.cut.source.placement.hist⟩
  DateBill.bitTariff ((area₀).program G live (ports).io receipt (z).bus x.stageFloor)
    ((area₀).ticks G live (ports).io receipt (z).bus x.stageFloor)

def dateSteps (room : x.CodeRoom) :=
  x.model.issuedSteps (cur).floor ports entry room.signed (z).bus mat geometry room.blocks room.paths
    room.slots room.chip room.endFit room.packed room.radix room.funded

def archiveInvoice :=(x.model.archivePhase (cur).floor ((menu).profile (z).age) (z).bus).wordInvoice

def lastInvoice (room : x.CodeRoom) :=
  x.model.tailAmount x.stageFloor (z).bus (x.model.reachedSources x.stageFloor) room.result

theorem charged_date (live : 0 < k) (room : x.CodeRoom) :
    (x.date live room).tariff=x.archiveInvoice+x.matchInvoice live+x.privateFee+x.returnInvoice room+
      (x.dateSteps room).arguments.wordInvoice+(x.dateSteps room).paid.wordInvoice+x.lastInvoice room+
      (x.dateSteps room).primitive.wordInvoice :=
  DatePorts.ordinary_date_charges ports x.cut.ticket op g tb (z).p f drift (z).degree h seats (cur).floor
    (menu).ordinary (z).bus ((menu).profile (z).age) (menu).header live room

theorem price_mono {lead rate share lead' rate' share' saving : ℕ}
    (l : lead ≤ lead') (r : rate ≤ rate') (s : share ≤ share') : x.Price lead rate share saving ≤ x.Price lead' rate' share' saving:=by
  have hrate : scale J rate ≤ scale J rate':=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ r)
  unfold Price
  dsimp only
  gcongr

theorem price_add {a b c d s t saving : ℕ} :
    x.Price a b s saving+x.Price c d t saving ≤ x.Price (a+c) (max b d) (s+t) saving:=by
  calc
    _ ≤ x.Price a (max b d) s saving+x.Price c (max b d) t saving:=
      Nat.add_le_add (x.price_mono le_rfl (Nat.le_max_left ..) le_rfl)
        (x.price_mono le_rfl (Nat.le_max_right ..) le_rfl)
    _=_:=by unfold Price;ring

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
