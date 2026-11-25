import OAI.Hierarchy.DescentMountedRotorTransport
import OAI.Hierarchy.DescentMountedStemWord
import OAI.Hierarchy.DescentGoodTapIssuedWord
import OAI.Hierarchy.DescentFreshArgumentRoom
import OAI.Hierarchy.DescentNamedRotorAddressRoom
import OAI.Hierarchy.DescentResetOriginRangeShape

namespace OAI
/-! # The measured rotor range on an original reached bank and its actual gate -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentSixParty.ClosedReset.Window DescentKernelHistory DescentBundleHistory
open DescentCompiler DescentPrimitivePalette DescentLocalArchiveOrder DescentRetainedRangeDigits
open DescentDenseHostOrder DescentChosenRouter DescentResetPublicOperandBook
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset cap ctl) (hp : 0<p) (whole : p∣B.reset.unit)
  (a : Archive W) (earlier : Local a.bit)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "m" => (Z).unit/p
local notation "key" => DescentOrderedReset.grains W B.count B.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "prg" => (Z).laneRecipe key m p hp fit
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "order" => DescentLocalArchiveOrder.reset B p hp whole a earlier
local notation "badge" u:arg => (Z).localShape T (B.next.placement.pos (u).1).2
local notation "Ht" => GroupStage.depthBound D n f g
local notation "res" => (Z).k-(T).commonDepth
variable {field query lanes nodes args width : ℕ}
local notation "cfg" => publicOperandConfig B field query lanes m m nodes args p
variable (side : Bool) (root : B.reset.placement.Good) (actor : (DescentCommonPalette.rotor B.reset.graph).Site)
local notation "installedSite" => DescentCommonPalette.rotorSiteEquiv (Z).graph d
  (selectedRotorLayers (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit side root) C (Z).width (Z).unit
local notation "venue" => (⟨(side,.inl root),installedSite actor⟩ : (Z).bank.Site)
local notation "plan" => (Z).laneShape key m p hp fit venue

set_option maxHeartbeats 800000 in
/-- The law transported from the original CPU reads the range digit at the true local
ordinal. Its gate, ordered public sockets and payment are those of the chosen reset. -/
theorem reached_mounted_span (recorded : B.Recorded p) (date : ℕ)
    (grain : z=S.grainAt G.b p date) (growth : G.b≤2^S.capGain)
    (node : (prg venue).Node) (u : NodeOrder.All next_)
    (origin : resetOrigin B hp whole a u=.inr (.inr ⟨venue,node⟩)) (slot : ℕ)
    (row : (cfg).Data (Z).n) (read : Fin 3→ℕ)
    (law : OperandMenu.MountedRotorLaw (Z).graph cfg row (order u.1 u.2).val slot width read)
    (observed : GoodTapRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes)
      (args:=args) (grain:=p) B side root row)
    (depth : ((cfg).reg row 1).val=((Z).goodLabel T root).val.1+1) (safe : ((cfg).reg row 2).val%2=0)
    (ranked : ((cfg).reg row 3).val=(localRank (Z).graph res Ht (badge u)).val)
    (room : 2<2^width) (span : ∀axis,atSlot plan node slot axis<2^width)
    (capacity : S.retainedNodes≤nodes) :
    ∀axis,read axis=atSlot plan node slot axis:=by
  have number:=fresh_local_ordinal B hp whole a earlier u ⟨venue,node⟩ origin
  have shapeSeen : (badge u).val=.good side ((),((Z).goodLabel T root).val.2) actor:=by
    rw [fresh_shape B hp whole a u ⟨venue,node⟩ origin]
    simp only [DescentCommonHost.bankNode,DescentDenseHostOrder.shape,Equiv.symm_apply_apply,
      DescentCanonicalPorts.short,DescentCanonicalPorts.relative,DescentSixParty.ResetInput.goodLabel]
  have layer:=sized_layer_count (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit m p fit side root
  let sized := (fit ▸ (Z).circuit : Hardware (K:=F) (C₀:=C) (u:=m*p) (Z).placement (Z).graph (Z).positive (Z).pay)
  have sameLayers := layer.trans (selectedRotorLayers_eq (Z).placement (Z).graph (Z).positive (Z).pay sized side root)
  have budget:=B.named_rotor_address_room recorded date grain growth side root
  intro axis
  exact law (Z).placement (Z).positive (Z).pay (Z).circuit key d hp fit side root actor
    ((Z).laneWidth_eq m p fit venue) node (badge u) ((Z).goodLabel T root) (publicRotorSlots B side root)
    number depth safe ranked ranked shapeSeen (observed.layers.trans sameLayers) ((Nat.mul_le_mul_right m sameLayers.ge).trans (budget.trans capacity))
    observed.present observed.missing observed.earlier observed.traffic room axis (span axis)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
