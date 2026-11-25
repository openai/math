import OAI.Hierarchy.DescentOriginalRelayPadding
import OAI.Hierarchy.DescentMeasuredTreeAbsent

namespace OAI
/-! # The empty native gate ordinal of an occupied bank site -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentPacking Chronology
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentDatedAddressBook
open DescentPaidResidentCount
variable {p : ℕ} (hp : 0<p) (whole : p∣B.reset.unit) (a₀ : Archive W) (rank₀ : Local a₀.bit)
local notation "new_" => (resetArchive B p hp whole a₀).bit
local notation "number_" => DescentLocalArchiveOrder.reset B p hp whole a₀ rank₀
variable (ports : Chronology.DatePorts) (places : Chronology.DatePorts.RangeRoom ports B.next new_)
  (x₀ : Fin (2^ports.venue.k)) (slot : Fin ports.nodes) (rh : Fin ports.operandHosts) (rg : Fin ports.venue.groups)
  (inside : rh.val<Fintype.card B.next.V)
local notation "missing" => Chronology.DatePorts.slotAt ports B.next new_ number_ places x₀ slot rh rg=none

local notation "realBank" z:arg => B.reblock.destination ((B.reset.resetNames B.terminals).symm (.inr z))
local notation "atBank" z:arg => occupies B.next.placement (Equiv.refl _) B.next.vertex ⟨rh.val,inside⟩
  (rg.cast places.groups.symm) (x₀.cast (congrArg (2^·) places.radix.symm)) (realBank z)
local notation "id₀" => DescentOrderedReset.grains W B.count B.order
local notation "prog" => B.reset.laneRecipe id₀ (B.reset.unit/p) p hp (Nat.div_mul_cancel whole).symm

theorem bank_slot_padding (z₀ : B.reset.bank.Site) (here : atBank z₀) (empty : missing) :
    Fintype.card (prog z₀).Node≤ slot.val :=by
  have absent:=Chronology.DatePorts.slot_absent_range ports B.next new_ number_ places x₀ slot rh rg inside empty
  have card:=DescentPrimitivePalette.reached_card B hp whole a₀ (.inr z₀)
  change Fintype.card ((new_).recipe (realBank z₀)).Node=Fintype.card (prog z₀).Node at card
  by_contra! occupied
  exact absent ⟨realBank z₀,here,by rwa [card]⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
