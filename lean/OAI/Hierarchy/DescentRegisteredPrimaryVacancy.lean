import OAI.Hierarchy.DescentRegisteredPrimaryCoordinates
import OAI.Hierarchy.DescentRetainedPrimaryCompleteness

namespace OAI
/-! # Original primary geometry at an empty registered scalar coordinate -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentSixParty.Chronology DescentKernelHistory DescentLocalArchiveOrder
open DescentCompiler DescentBundleHistory DescentCommonHost DescentDenseHostOrder DescentResetActorClass
open DescentSIMDLookup DescentRotor DescentDatedAddressBook DescentColonies
open DescentSixParty.ClosedReset.Window
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits}
  {G:PoweredGadget F} {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist p:ℕ}
  {input:Reached W G q ε S k i z D wire hist} {ctl:ResetRates G S k D n h C f g cut tail}
  (b:ClosedReset input ctl) (hp:0<p) (whole:p∣b.reset.unit) (a:Archive W) (old:Local a.bit)
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "next_" => (resetArchive b p hp whole a).bit
local notation "num" => DescentLocalArchiveOrder.reset b p hp whole a old
variable (ports:DatePorts) (room:DatePorts.RangeRoom ports b.next next_)
variable (x:Fin (2^ports.venue.k)) (slot:Fin ports.nodes) (h₁:Fin ports.operandHosts) (g₁:Fin ports.venue.groups)
open DescentFallbackShapeTable DescentRelativeContacts DescentIssuedFallbackPanel
local notation "H" => S.hostSize (i+1)
local notation "res" => (Z).k-(T).commonDepth
local notation "Y" => b.next
local notation:max "home" t:arg => (Z).placed T (((Z).resetNames T).symm (.inl (false,t)))
local notation:max "oldHost" t:arg => b.frame.host.symm ((T).code t).1
local notation:max "code" t:arg => DescentFallbackShapeTable.cell res (shortName (T).commonDepth ((T).code t)).2
local notation:max "hi" t:arg => (Z).rootBlock T (.inr t)
local notation "out" => S.resetOutputDigits ctl.base ctl.radix b.age b.commonDepth
local notation "high_" => (out).symm (g₁.cast room.groups.symm,x.cast (congrArg (2^·) room.radix.symm))
variable (present:h₁.val<Fintype.card (Y).V) (absent:DatePorts.slotAt ports (Y) next_ num room x slot h₁ g₁=none)
local notation "act" => (DescentStageEdgeReceipt.dense (Y).vertex).symm ⟨h₁.val,present⟩
local notation:max "available" t₀:arg term:arg => ((T).code term).1=b.frame.host (oldHost t₀) ∧ hi term=high_ ∧ code term=code t₀

include absent in
theorem registered_primary_empty_cases {wanted:ℕ} (retained:primaryTarget (Z).graph res (act).val=some wanted) :
    ∃t₀:(Z).Fallback,act=home t₀ ∧ code t₀=wanted ∧
    ((∃t:(Z).Fallback,available t₀ t ∧
       (∑u:DescentNamedContact.Fibre (T).home t,Fintype.card (a.bit.recipe u.val).Node)≤ slot.val) ∨
      ¬∃t:(Z).Fallback,available t₀ t):=by
  obtain ⟨t₀,home₀,code₀⟩:=primary_claim b (act) retained
  refine ⟨t₀,home₀,code₀,?_⟩
  by_cases reached_:∃t:(Z).Fallback,available t₀ t
  · left
    obtain ⟨t,h,atHigh,encoded⟩:=reached_
    refine ⟨t,⟨h,atHigh,encoded⟩,?_⟩
    have dense:((Y).vertex (act)).val=h₁.val:=congrArg Fin.val
      ((DescentStageEdgeReceipt.dense (Y).vertex).apply_symm_apply ⟨h₁.val,present⟩)
    have same:home t=act:=(same_primary b t t₀ (h.trans (b.frame.host.apply_symm_apply _)) encoded).trans home₀.symm
    have bound:h₁.val<H:=present.trans_le b.next.valid.host
    by_contra! small
    have highAt:out (hi t)=(g₁.cast room.groups.symm,x.cast (congrArg (2^·) room.radix.symm)):=by
      rw [atHigh,Equiv.apply_symm_apply]
    obtain ⟨entry,seen,_⟩:=primary_at_slot b hp whole a old slot (x.cast (congrArg (2^·) room.radix.symm))
      ⟨h₁.val,bound⟩ (g₁.cast room.groups.symm) t ((congrArg (fun u=>((Y).vertex u).val) same).trans dense) highAt small
    change Reached.NodeCells.atPhysical (Y) next_ num _ slot h₁ _=none at absent
    rw [Reached.NodeCells.atPhysical,dite_eq_left bound,seen] at absent
    contradiction
  · exact Or.inr reached_

end
end Hierarchy.DescentPrimitivePalette

end OAI
