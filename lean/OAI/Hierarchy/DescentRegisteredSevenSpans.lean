import OAI.Hierarchy.DescentResetArchiveCertificate
import OAI.Hierarchy.DescentSlotAbsentRange

namespace OAI
/-! # The three posted range fields on original, relay and installed bank nodes -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedColony DescentPackedZip
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentPrimitivePalette RegisterTimeline
open DescentPacking.PackedMatch.Local.Stage
open DescentColonies DescentDatedNodeMetadata DescentOperandStateBanks DescentOperandCandidateLookup DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "start" => (v).sheetsStart b
local notation "plan" => (v).linkedRankInputs u.sectors start
local notation "rendered" => (v).renderFromRanks plan b
local notation "ports" => reset a floor u
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation:max "acted" m:arg actorMem:arg => ((head).seq ((v).actor.actorBody u.actor ((v).middle.stop b) w)).Exec m actorMem
  (ht+(v).actor.actorTicks u.actor ((v).middle.stop b) w)



variable {F P:Type} [Field F] [Fintype P] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:DescentCompiler.AtomSchedule} {k age grain degree wire hist p R seedGrain:ℕ}
  (r:Reached W G q ε S k age grain degree wire hist) (B:BitDescription W) (number:Local B)
  (places:RangeRoom (reset a floor u) r B) (shape:WorldShape p R B) (hp:0<p) (pin:P→ℕ)
  (op:RotorSpec) (label:NodeOrder.All B→Label G hist seedGrain op)
local notation "L" => (ports).rangeLayout
local notation "R₁" => (v).rangeLayout
local notation "c₀" => (ports).metadataChart
local notation "c₁" => (v).metadata.chart
local notation "slot" => slotAt ports r B number places
local notation "flags" => archiveFlag r B number ports places
local notation "ptr" => Reached.argumentPointer r B number shape hp pin (ports).argumentsPerNode
local notation:max "argc" y:arg => (DescentRetainedRangeDigits.occurrences (shape.sites (y:NodeOrder.All B).1) y.2).length
local notation:max "reg" m:arg => rangeRegister ports r B number places.capacity places.hosts places.groups places.radix places.positive m

variable (ok : u.Ready) (small : 2*a.successor.receiver.candidates<2^a.successor.receiver.queryBits)
    (axes : (reset a floor u).rangeLayout=a.successor.rangeLayout)
    (actorMem : Memory w) (choice : ∀i,OrdinalRead u ok small actorMem i)


local notation:max "amount" f:arg j:arg x:arg n:arg h:arg g:arg => ((choice ((v).operandOrdinal (s) (DescentRetainedRangeDigits.page f)
  (((j : Fin (L).operands).cast (congrArg Layout.operands axes)).cast ok.slots.symm)
  ((x : Fin (L).blocks).cast (congrArg Layout.blocks axes))
  (((n : Fin (L).nodes).cast (congrArg Layout.nodes axes)).cast ok.nodes.symm))).amount
  ((h : Fin (L).hosts).cast (congrArg Layout.hosts axes)) ((g : Fin (L).groups).cast (congrArg Layout.groups axes))).val

def SevenOriginSpans {U V : Type*} (origin : NodeOrder.All B→V) (tag : U→V) : Prop :=
  ∀(x:Fin (L).blocks)(j:Fin (L).operands)(f:Fin 3) h g n y,slot x n h g=some y → (j.val<argc y ∨ f=2) →
    ∀v₀,origin y=tag v₀ → amount f j x n h g=DescentRetainedRangeDigits.atSlot (shape.sites y.1) y.2 j.val f

def SevenVacant : Prop :=
  ∀(x:Fin (L).blocks)(j:Fin (L).operands) h g n,slot x n h g=none → amount (2:Fin 3) j x n h g=0

local notation:max "part" src:arg tag:arg => SevenOriginSpans u r B number places shape ok small axes actorMem choice src tag

omit [Fintype P] in
theorem registered_seven_spans {K E V : Type*} (origin : NodeOrder.All B→K⊕(E⊕V))
    (retained : part origin Sum.inl) (relay : part origin (Sum.inr ∘ Sum.inl))
    (bank : part origin (Sum.inr ∘ Sum.inr)) :
    SevenSpans u r B number places shape ok small axes actorMem choice :=by
  intro x j f h g n y slot_ available
  cases loc:origin y with
  | inl old => exact retained x j f h g n y slot_ available old loc
  | inr born =>
    cases born with
    | inl e => exact relay x j f h g n y slot_ available e loc
    | inr v₀ => exact bank x j f h g n y slot_ available v₀ loc

omit [Fintype P] in
/-- Absent numeric gates either lie outside the host register, in a physically empty
block, or past the last gate of its actual site. Every real site can be considered even
when its own recipe has no gates at all. -/
theorem registered_seven_vacant
    (outside : ∀(x:Fin (L).blocks)(j:Fin (L).operands) h g n,Fintype.card r.V≤h.val →
      slot x n h g=none → amount (2:Fin 3) j x n h g=0)
    (unoccupied : ∀(x:Fin (L).blocks)(j:Fin (L).operands) h g n (hv : h.val<Fintype.card r.V),
      (¬∃site,DescentPaidResidentCount.occupies r.placement (Equiv.refl _) r.vertex ⟨h.val,hv⟩
        (g.cast places.groups.symm) (x.cast (congrArg (2^·) places.radix.symm)) site) →
      slot x n h g=none → amount (2:Fin 3) j x n h g=0)
    (padded : ∀(x:Fin (L).blocks)(j:Fin (L).operands) h g n (hv : h.val<Fintype.card r.V) site,
      DescentPaidResidentCount.occupies r.placement (Equiv.refl _) r.vertex ⟨h.val,hv⟩
        (g.cast places.groups.symm) (x.cast (congrArg (2^·) places.radix.symm)) site →
      Fintype.card (B.recipe site).Node≤n.val → slot x n h g=none → amount (2:Fin 3) j x n h g=0) :
    SevenVacant u r B number places ok small axes actorMem choice :=by
  intro x j h g n none_
  by_cases hv : h.val<Fintype.card r.V
  · by_cases used : ∃site,DescentPaidResidentCount.occupies r.placement (Equiv.refl _) r.vertex ⟨h.val,hv⟩
          (g.cast places.groups.symm) (x.cast (congrArg (2^·) places.radix.symm)) site
    · obtain ⟨site,land⟩:=used
      apply padded x j h g n hv site land _ none_
      exact Nat.le_of_not_gt (fun bound=>
        slot_absent_range ports r B number places x n h g hv none_ ⟨site,land,bound⟩)
    · exact unoccupied x j h g n hv used none_
  · exact outside x j h g n (Nat.le_of_not_gt hv) none_

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
