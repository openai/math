import OAI.Hierarchy.DescentPostedResetSevenArchive
import OAI.Hierarchy.DescentRootPrimitivePaidRead
import OAI.Hierarchy.DescentPhysicalResetMetadataRead
import OAI.Hierarchy.DescentResetVenueScalarSpan
import OAI.Hierarchy.DescentRegisterArchiveFlagAfter
import OAI.Hierarchy.DescentMetadataInputCore
import OAI.Hierarchy.DescentResetSelectedNewbornRange

namespace OAI
/-! # The structural counts and funding bits at the true reset metadata input -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedNodeMetadata DescentColonies DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedColony DescentPackedZip DescentSIMDLookup
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM RegisterTimeline
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
    {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist p R : ℕ}
    (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W) (rank : Local B)
local notation "ports" => reset a floor u
variable (room : RangeRoom (reset a floor u) r B) (shape : WorldShape p R B)
local notation "v" => a.successor
local notation "c₀" => (ports).metadataChart
local notation "c₁" => (v).metadata.chart
local notation "slot" => slotAt ports r B rank room
local notation "argc" y:arg => (occurrences (shape.sites (y : NodeOrder.All B).1) y.2).length
local notation "bank" => (v).metadata
variable (chart : (reset a floor u).metadataChart=a.successor.metadata.chart)
local notation "rawX" x:arg => (x : Fin (c₁).blocks).cast (congrArg Chart.blocks chart).symm
local notation "rawN" n:arg => (n : Fin (c₁).nodes).cast (congrArg Chart.nodes chart).symm
local notation "rawH" h:arg => (h : Fin (c₁).hosts).cast (congrArg Chart.hosts chart).symm
local notation "rawG" g:arg => (g : Fin (c₁).groups).cast (congrArg Chart.groups chart).symm
local notation "at_" x:arg n:arg h:arg g:arg => slot (rawX x) (rawN n) (rawH h) (rawG g)
local notation "arity" x:arg n:arg h:arg g:arg => (at_ x n h g).elim 0 (fun y=>argc y)

omit [Fintype P] in
theorem reset_reached_metadata (z : u.FinalInputs) (ok : u.Ready) (fits : z.Room) (mid : Memory w)
    (blocks : (c₁).blocks≤2^(v).venue.next.k) (hosts : (ports).operandHosts=S.hostSize age)
    (positive : 0<age) (hp : 0<p) (bound : ∀y : NodeOrder.All B,argc y≤u.operand.slots)
    (mass : r.placement.wire*(r.placement.z*G.b)*r.placement.cap<2^(bank).paidBits)
    (sp : Fin (c₁).blocks→Fin (c₁).nodes→Fin u.operand.slots→Fin (c₁).hosts→Fin (c₁).groups→Cell (bank).spanBits)
    (measured : ∀x, Source ((PhysicalReset.FinalInputs.paid u) x) (fun h g=>
      Census.count r.placement (Equiv.refl _) (r.vertex.trans (Fin.castLEEmb r.valid.host)) (bank).paidBits
        ((rawH h).cast hosts) ((rawG g).cast room.groups.symm)
        ((rawX x).cast (congrArg (2^·) room.radix.symm))) (c₁).lanes (z.venueImage mid))
    (amounts : ∀x n j,Source (z.spans x n j) (sp x n j) (c₁).lanes (z.venueImage mid))
    (spans : ∀x n j h g,(sp x n j h g).val=(at_ x n h g).elim 0
      (fun y=>atSlot (shape.sites y.1) y.2 j.val 2)) :
    ∃amount : Fin (c₁).blocks→Fin (c₁).hosts→Fin (c₁).groups→Cell (bank).paidBits,
    ∃count : Fin (c₁).blocks→Fin (c₁).nodes→Fin (c₁).hosts→Fin (c₁).groups→ℕ,
      (∀x n h g,count x n h g≤u.operand.slots) ∧
      (∀x n j h g,sp x n j h g≠0 ↔ j.val<count x n h g) ∧
      (∀x, Source ((PhysicalReset.FinalInputs.paid u) x) (amount x) (c₁).lanes (z.tokenImage (z.roleInput mid))) ∧
      (∀x n j,Source (z.spans x n j) (sp x n j) (c₁).lanes (z.tokenImage (z.roleInput mid))) ∧
      (∀x n h g,let X:=x.cast (congrArg Chart.blocks chart);let H:=h.cast (congrArg Chart.hosts chart);
        let J:=g.cast (congrArg Chart.groups chart)
        (if n.val<(amount X H J).val then 1 else 0)=archiveFlag r B rank ports room x n h g) ∧
      ∀x n h g,count (x.cast (congrArg Chart.blocks chart)) (n.cast (congrArg Chart.nodes chart))
          (h.cast (congrArg Chart.hosts chart)) (g.cast (congrArg Chart.groups chart))=(slot x n h g).elim 0 (fun y=>argc y):=by
  have frame:=z.metadata_input_frames ok fits mid blocks
  let paidRows (x : Fin (c₁).blocks) (h : Fin (c₁).hosts) (g : Fin (c₁).groups) : Cell (bank).paidBits :=
    Census.count r.placement (Equiv.refl _) (r.vertex.trans (Fin.castLEEmb r.valid.host)) (bank).paidBits
      ((rawH h).cast hosts) ((rawG g).cast room.groups.symm) ((rawX x).cast (congrArg (2^·) room.radix.symm))
  refine ⟨paidRows, fun x n h g=>arity x n h g,?_,?_,?_,?_,?_,?_⟩
  · intro x n h g
    cases here : at_ x n h g with
    | none=>simp [here]
    | some y=>simpa [here] using bound y
  · intro x n j h g
    have digit:=spans x n j h g
    cases here : at_ x n h g with
    | none=>
      have zero : sp x n j h g=0:=Fin.ext (by simpa [here] using digit)
      simp [here,zero]
    | some y=>
      simp only [here,Option.elim_some] at digit ⊢
      have pos : 0<atSlot (shape.sites y.1) y.2 j.val 2 ↔ j.val<argc y:=by
        rw [atSlot_count,DescentRetainedRangeDigits.length _ _ hp]
        exact DescentResetMetadataInputs.span_occupied hp (shape.sites y.1) y.2 j.val
      have nz : sp x n j h g≠0 ↔ 0<(sp x n j h g).val:=by
        constructor
        · intro hn
          by_contra! zero
          exact hn (Fin.ext (by simpa using zero))
        · intro hn zero
          simp [zero] at hn
      rw [nz,digit]
      exact pos
  · intro x t
    exact (frame.2.1 x _).trans (measured x t)
  · intro x n j t
    exact (frame.2.2 x n j _).trans (amounts x n j t)
  · intro x n h g
    exact (archiveFlag_after r positive B rank ports room r.valid.host (bank).paidBits mass
      x n h g (h.cast hosts) rfl).symm
  · intro x n h g
    rfl

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
