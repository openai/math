import OAI.Hierarchy.DescentCalendarPrimaryPrivateKeys
import OAI.Hierarchy.DescentDatedOperandMovement

namespace OAI
/-! Previous population, arity and operand words on the actual remixed fallback root. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentDenseHostOrder DescentResetOperandSetup DescentColonies DescentGL
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open DescentSixParty.PackedFlow.Channels DescentSixParty.Chronology
open scoped Classical BigOperators Fin.CommRing
open DescentPlainTerminal DescentPackedResetDonors DescentBaseProfile DescentResetHostSize DescentPaidResidentCount.Reset
open DescentPacking.PackedMatch.Local.Stage DescentPhysicalOrder DescentRetainedResetPinPointer
open DescentPrimitivePalette DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder
open DescentIssuedFallbackPanel DescentPaidResidentCount.Reset DescentRetainedRangeDigits
open DescentRetainedPrivateSlotBook DescentRelativeContacts DescentFallbackShapeTable DescentPackedWalsh
open DescentLocalPrivateNames DescentRetainedControl DescentSixParty.ClosedReset
open DescentPacking.PackedMatch.Local.Stage DescentRotorWindowArchive DescentGL
open scoped BigOperators

variable {F Pin:Type} [Field F] {d:ℕ} {bits:Pin→ℕ} {W:MarkedWorld F d Pin bits}
    {G:PoweredGadget F} {q ε:ℝ} {S:DescentCompiler.AtomSchedule} {k age z D wire hist n h C f g cut tail p R:ℕ}
    {input:Reached W G q ε S k age z D wire hist} {ctl:ResetRates G S k D n h C f g cut tail}
    (B:ClosedReset input ctl) (chart:DescentResetOperandSetup.Chart) (oldA:Archive W) (num:Local oldA.bit)
    (shape:WorldShape p R oldA.bit) (hp:0<p) (pin:Pin→ℕ)
local notation "L" => chart.retained
local notation "T" => B.terminals
variable (total:(L).high+(L).low=S.groupWidth k tail age+k) (axis:(L).cut=(T).commonDepth)
    (blocks:(L).blocks=2^k) (groups:(L).groups=S.groupCount age)
    (size:2^((L).high+(L).low)=(L).groups*(L).blocks) (cutRoom:(L).cut≤(L).high+(L).low)
    (hostRoom:Fintype.card input.V≤(L).hosts) (nodeRoom:∀v,Fintype.card (oldA.bit.recipe v).Node≤(L).previousNodes)
    (args:∀v n₀,((shape.sites v).recipe hp).arity n₀≤(L).previousArgs)
    (basis:DescentGL.Layout ((L).high+(L).low)) (values:(L).Values)
local notation "names" => input.vertex.trans (Fin.castLEEmb hostRoom)
local notation "dirs" => finCongr (congrArg (fun s=>2^s) (congrArg₂ Nat.sub total axis))
local notation "data_" => fun j=>blockValues cutRoom ((L).before size values j) basis

/-- Original input words retained together at each reached fallback root. -/
def PrimaryDonorRead : Prop :=
  ∀y:NodeOrder.All oldA.bit,
    let t:=(T).home y.1
    let carrier:=(names) (B.frame.host.symm ((T).code t).1)
    let hi:=(B.reset.rootBlock T (.inr t)).cast (congrArg (2^·) axis).symm
    let data:=(L).site data_ carrier hi
    let d:=calendar_donor_index (b:=B) (a:=oldA) (yy:=y) (chart:=chart) (total:=total) (axis:=axis)
    (∀lo,let inputCell:=(rearrange basis).symm (join cutRoom hi ((dirs).symm lo))
         let place:=finProdFinEquiv.symm (inputCell.cast size)
         (L).originalCount data ((dirs).symm lo)=∑v,if DescentPaidResidentCount.occupies input.placement
           (Equiv.refl _) names carrier (place.1.cast groups) (place.2.cast blocks) v
           then Fintype.card (oldA.bit.recipe v).Node else 0) ∧
    (∀(u:DescentNamedContact.Fibre (T).home t) n₀,
      ((L).entry data (d u) ((num u.val n₀).castLE (nodeRoom u.val)) (L).arityField).val=
        ((shape.sites u.val).recipe hp).arity n₀) ∧
    (∀(u:DescentNamedContact.Fibre (T).home t) (s₀:Slot ((shape.sites u.val).recipe hp)) (f₀:Fin 4),
      ((L).entry data (d u) ((num u.val s₀.1).castLE (nodeRoom u.val))
        ((L).operandField (f₀.castLE (by decide:4≤7)) (s₀.2.castLE (args u.val s₀.1)))).val=
      (Reached.argumentPointer input oldA.bit num shape hp pin (L).previousArgs ⟨u.val,s₀.1⟩ s₀.2.val).header f₀) ∧
    ∀(u:DescentNamedContact.Fibre (T).home t) (s₀:Slot ((shape.sites u.val).recipe hp)) (f₀:Fin 3),
      ((L).entry data (d u) ((num u.val s₀.1).castLE (nodeRoom u.val))
        ((L).operandField (DescentRetainedRangeDigits.page f₀) (s₀.2.castLE (args u.val s₀.1)))).val=
      atSlot (shape.sites u.val) s₀.1 s₀.2.val f₀

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
