import OAI.Computability.VPVNP.CompressorShrinkOutputAllocation
import OAI.Computability.VPVNP.CompressorRecordsShrinkPreimages
import OAI.Computability.VPVNP.ShrinkFieldBounds

/-! # Constructing the next shrinking incidence directory from selected term rows

The width sweep reads the ten words written for each admitted motif. Its
absolute split rows feed the ordered-slot passes in the same memory. All
old directories below the new width rectangle and all interval records
of the sweep survive the slot construction.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkOutput

open Compression Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion Slots SlotOwners SlotLevel ShrinkSlots
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ShrinkSliceSweep

variable {a b g w : ℕ} {k : Type*} [_root_.Field k] {factor δ : ℝ}
variable (X : State a (packingLaneBits a g))
variable (F : FixedBlock k demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (sel : X.ShrinkSelection F)
variable (term : Word w) (stride role retained : ℕ)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

local notation "sitesOrd" => Shrink.packedIndex (a := a) (g := g) X.baseIndex
local notation "sh" => levelShape (b := b) X
local notation "T" => splitBank (b := b) X F sel term stride role retained
local notation "h" => slotHeads (b := b) X term.val stride role retained
local notation "cutoff" => widthBase X term.val stride role retained
local notation "last" => stop (b := b) X term.val stride role retained
local notation "side" => selectedLayout X F sel
local notation "termInput" => Terms X.packingData X.shrinkNumber sitesOrd T F X.packingWidth sel
local notation "sizeAt" => selected X.packingData X.shrinkNumber sitesOrd T F X.packingWidth sel
local notation "splits" => SlotWidthScan.SplitRows X.packingData (Shape.subdivisions sh) X.baseIndex
  (bitWordFinEquiv (Shrink.J a)) (bitWordFinEquiv g) (branchWidth X F sel) cutoff

/-- The total probe count for constructing the output slot directory, including genuine and
dummy slots and the base and actual arc scans. -/
def slotProbes (s : Shape) :=
  (24+2*sites s+2*(owners s+fields s)) +
    (6*genuineCount s+3*dummyCount s+5*fields s+3*(owners s*s.newDegree)+8*baseArcs s+12*actualCount s)

/-- Word bounds on static arithmetic and the current maximum wire width,
independent of the selected branch. -/
structure FitsWords : Prop where
  room : last < 2^w
  selector : F.selectorBits < 2^w
  supply : fieldFactor F * (X.maxWireWidth+1) < 2^w
  lanes : (sh).lanes < 2^w
  tags : (sh).tags < 2^w
  profile : (∑ t, (sh).subdivisions t) < 2^w
  degree : (sh).newDegree < 2^w

private theorem roles_frame (mem out : Memory w) (roles : DemandRAM.RoleColumns X side role mem)
    (eqn : ∀ x < cutoff, out x = mem x) : DemandRAM.RoleColumns X side role out := by
  have bound (arc) (j : ℕ) (hj : j < 4) : role + 4*(DemandRAM.absoluteIndex X arc).val+j < cutoff := by
    have hi := (DemandRAM.absoluteIndex X arc).isLt
    have stopRole := role_room X term stride role retained
    change (DemandRAM.absoluteIndex X arc).val < absoluteCount X at hi
    omega
  constructor
  · intro arc; rw [eqn _ (bound arc 3 (by decide))]; exact roles.cd arc
  · intro arc r; rw [eqn _ (bound arc.val (roleOffset r) (by cases r <;> decide))]; exact roles.packed arc r

/-- Every selected physical supply width is bounded by the same quantity
fixed before the verifier chooses the terms. -/
theorem supply_fit (hw : FitsWords (b := b) X F term stride role retained) (i : Allocation.Id (motifCount X)) :
    sizeAt i < 2^w := by
  let m := (ShrinkMotifOrder.stateNumber X).symm i.1
  have bound := X.packingData.shrinkTerm_bounds (State.two_le_packingColors _) (Nat.two_pow_pos _)
    X.shrinkNumber X.packingWidth (fun _ => X.width_le_maxWireWidth _) F m (sel m)
  exact (bound.2 (side,i.2)).2.trans_lt hw.supply

/-- The complete slot build and the readbacks of the final shared memory. -/
structure Constructed (mem out : Memory w) (r : Build.Construction w)
    (slotStart : ℕ := (h).role) : Prop where
  inputRoles : DemandRAM.RoleColumns X side role out
  slots : r.Native sh (heads sh role slotStart) cutoff side out
  cursors : r.Cursors sh
  incidence : (directory sh (heads sh role slotStart) w).Represents (X.shrinkNext F ready sel) (r.final out)
  roles : DemandRAM.RoleColumns X side role (r.final out)
  widths : splits (r.final out)
  intervals : ∀ i, Image ((T).row i) (sizeAt i) (r.final out)
  frame : ∀ x, x < cutoff ∨ finish sh (heads sh role slotStart) ≤ x → r.final out x = mem x
  probes : RAMBuckets.cost Report.probes r.all = slotProbes sh

set_option maxHeartbeats 1600000 in
/-- The surviving sweep's absolute width rows are the input of the native
slot passes. Their interval records and the earlier directories survive. -/
theorem finish_after_sweep_at (slotStart : ℕ) (gap : (h).role ≤ slotStart)
    (endFit : finish sh (heads sh role slotStart) < 2^w) (wide : 10 ≤ stride) (hw : FitsWords (b := b) X F term stride role retained)
    (mem out : Memory w) (roles : DemandRAM.RoleColumns X side role mem)
    (images : ∀ i, Image ((T).row i) (sizeAt i) out)
    (values : ∀ (m : X.packingData.Motif) (t : Fin 4) (j : Fin ((T).subdiv t)),
      (out ((T).widthBase+((oldArcIndex X.packingData X.baseIndex (bitWordFinEquiv (Shrink.J a))
        (bitWordFinEquiv g) m.val).val*4+t.val)*(T).stride+j.val)).val =
          splitWidth (X.packingData.termWidths F X.shrinkNumber X.packingWidth sel m (T).layout t) ((T).subdiv t) j)
    (oldFrame : ∀ x, x < cutoff ∨ (T).last ≤ x → out x = mem x) :
    ∃ r, Constructed X F ready sel term stride role retained mem out r slotStart := by
  let fit := fits X F sel term stride role retained ready wide hw.room
  have sr := Build.splitRows_of_values X (sh).subdivisions cutoff out (branchWidth X F sel) (fun m t j => by
    have hl : (T).layout = side := rfl
    have hv := values m t j
    rw [hl] at hv
    rw [← Nat.add_assoc]
    exact hv)
  have kept := roles_frame X F sel term stride role retained mem out roles (fun x hx => oldFrame x (.inl hx))
  have roleRoom : role+4*absoluteCount X ≤ (h).role :=
    (role_room X term stride role retained).trans (width_le_slots X term stride role retained)
  have splitRoom : cutoff+(oldBaseArcCount (sh).bases (sh).tags (sh).oldDegree (sh).colors*(sh).lanes)*4*
      (∑ t,(sh).subdivisions t) ≤ (h).role := Nat.le_add_right ..
  obtain ⟨r,native,cursors,inc,ro,sp,slotFrame,slotCost⟩ :=
    Build.build X F ready sel (heads sh role slotStart) cutoff out kept sr (roleRoom.trans gap) (splitRoom.trans gap)
      le_rfl le_rfl le_rfl endFit
      hw.lanes hw.tags hw.profile hw.degree
  refine ⟨r,⟨kept,native,cursors,inc,ro,sp,?_,?_,slotCost⟩⟩
  · intro i
    apply (images i).keep
    intro x hx
    exact slotFrame x (.inl (lt_of_not_ge fun he => hx ((T).rowOutside fit i x (.inr (gap.trans he)))))
  · intro x hx
    have hle := width_le_slots (b := b) X term stride role retained
    have he : (h).role ≤ finish sh (heads sh role slotStart) := gap.trans (by
      dsimp [finish, widthHead, inHead, outHead, inverseBaseHead, stopAddress, shiftsHead, targetsHead, inverseHead, rowsHead, heads]
      omega)
    exact (slotFrame x (hx.imp (fun p => p.trans_le (hle.trans gap)) id)).trans
      (oldFrame x (hx.imp id (fun p => he.trans p)))

/-- The consecutive allocation uses the first free address after the width
and interval rectangle as the start of the ordered-slot bank. -/
theorem finish_after_sweep (wide : 10 ≤ stride) (hw : FitsWords (b := b) X F term stride role retained)
    (mem out : Memory w) (roles : DemandRAM.RoleColumns X side role mem)
    (images : ∀ i, Image ((T).row i) (sizeAt i) out)
    (values : ∀ (m : X.packingData.Motif) (t : Fin 4) (j : Fin ((T).subdiv t)),
      (out ((T).widthBase+((oldArcIndex X.packingData X.baseIndex (bitWordFinEquiv (Shrink.J a))
        (bitWordFinEquiv g) m.val).val*4+t.val)*(T).stride+j.val)).val =
          splitWidth (X.packingData.termWidths F X.shrinkNumber X.packingWidth sel m (T).layout t) ((T).subdiv t) j)
    (oldFrame : ∀ x, x < cutoff ∨ (T).last ≤ x → out x = mem x) :
    ∃ r, Constructed X F ready sel term stride role retained mem out r :=
  finish_after_sweep_at X F ready sel term stride role retained (h).role le_rfl hw.room
    wide hw mem out roles images values oldFrame

end CompressorRecords.ShrinkOutput

end

end VPVNP
end Computability
end OAI
