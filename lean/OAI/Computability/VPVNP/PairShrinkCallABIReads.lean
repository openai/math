import OAI.Computability.VPVNP.PairShrinkCDReadBounds
import OAI.Computability.VPVNP.PairShrinkDescriptorReads
import OAI.Computability.VPVNP.PairShrinkPartyABReads
import OAI.Computability.VPVNP.PairSimulationMapHandlerAction

/-!
# External reads of the six-register shrink map writer

Each emitted operand expression reads from the selected old header, its
incidence and classification tables, or the dense demand and term records
in the completed shrink arena. The same header and arena bounds used by the
native AB gather suffice for the CD lookup and the raw descriptor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData CompressorRecords
open CompressorRecords.PhaseRecipe Compression.ShrinkMotif MotifGrid MotifBlocks MotifConversion
open scoped Fin.CommRing
open private cell_reads from OAI.Computability.VPVNP.PairShrinkPartyABReads

variable {w a b g : ℕ} {K : Type*} [_root_.Field K] {δ factor : ℝ}
variable {X : State a (packingLaneBits a g)}
variable {F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
variable {m : X.packingData.Motif} {party : Fin 6}
variable (J : Job X F ready sel m party w) (degree : ℕ)
variable {pub : Fin 5 → Word w} {state level H : Word w} {mem : Memory w}
variable {T : IncidenceDirectory w} {origin : ℕ}
local notation "O" => ShrinkCallABI.operands degree
local notation "C" => ShrinkCallHeader.Operands.cdHeader (ShrinkCallABI.operands degree) a
local notation "rd" => Expr.ReadsFrom (· < H.val) pub state mem
local notation "ev" => Expr.eval pub state mem
local notation "d" => 2 ^ a
local notation "Q" => pieceCount d (Shrink.colors a)
local notation "term" => ShrinkInput.termHead (w := w) X origin
local notation "dense" => ShrinkInput.demandHead (w := w) X origin
local notation "idx" => Fin.val (ShrinkMotifOrder.stateNumber X m)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- Every external load, including the full scan used to recover the CD
source ID, lies below the terminal controller header. -/
theorem Job.abi_descriptor_reads
    (old : J.OldPublished O pub state mem level T origin)
    (areas : J.ABAreas level T origin H.val)
    (termsEnd : ShrinkInput.termEnd X origin 10 ≤ H.val) :
    rd ((O).inputs a).descriptor ∧ ∀ j arg, rd (((O).inputs a).fields j arg) := by
  have ins := J.abi_inputs_readable degree old areas
  have cell := cell_reads old.live.header ins.level areas.levelEnd
  have twoFits : 2 < 2 ^ w := by have := areas.levelEnd; have := H.isLt; omega
  have G := ShrinkCallHeader.geometry X T origin old.space
  have heads := ShrinkCallHeader.heads X F sel m O pub state level mem J.arena T origin
    J.older J.pitch J.first J.scratch.hidden J.scratch.stride J.scratch.hist old.levelData old.live
  have inputs : ShrinkCDReadBounds.ScanInputs C H.val pub state mem := by
    have oldSites : rd (((O).cell 0).mul ((O).cell 2)) := ⟨cell 0 (by decide), cell 2 (by decide)⟩
    have oldSlots : rd ((((O).cell 0).mul ((O).cell 2)).mul ((O).cell 1)) :=
      ⟨oldSites, cell 1 (by decide)⟩
    exact ⟨⟨cell 46 (by decide), cell 44 (by decide), trivial, oldSlots⟩, cell 46 (by decide),
      ins.motif, trivial, cell 45 (by decide), ⟨cell 44 (by decide), trivial, oldSites⟩⟩
  obtain ⟨arcRead, flagRead⟩ := ShrinkCDReadBounds.scan X m C H.val T origin inputs heads.ab G
    heads.owners heads.thickness old.tables twoFits old.space areas.classifier
  have arc := ShrinkCD.arc_eq X C pub state mem m heads.ab G.arcFit G.bucketFit G.piecesFit
    twoFits heads.owners G.regions G.nrows G.cap old.tables.preimages old.tables.ranked
  have endpoint (dir : Bool) := J.old_field_reads O old ins areas m.1 ((C).arc Q) dir arc arcRead
  have cdReads (atD : Bool) : rd (((O).inputs a).cd atD) := by
    cases atD
    · exact ⟨⟨flagRead, endpoint true⟩, ⟨trivial, flagRead⟩, endpoint false⟩
    · exact ⟨⟨⟨trivial, flagRead⟩, endpoint true⟩, ⟨trivial, trivial, flagRead⟩, endpoint false⟩
  have stored := ShrinkCallHeader.stored X F sel m O pub state level mem J.arena T origin
    J.older J.pitch J.first J.scratch.hidden J.scratch.stride J.scratch.hist old.levelData old.live
    old.tables old.space twoFits
  have count : rd ((O).count a) :=
    ⟨⟨⟨cell 0 (by decide), trivial, cell 3 (by decide)⟩, trivial⟩, trivial⟩
  have ord : idx < ShrinkTermInputs.motifCount X := ((ShrinkMotifOrder.entries X).symm m).isLt
  have termRoom : (term).val + ShrinkTermInputs.motifCount X * 10 ≤ H.val := by
    rw [ShrinkTermSelection.motifCount_eq X]
    apply le_trans (Nat.add_le_add_right (Nat.mod_le ..) _) termsEnd
  have pairRoom := (ShrinkInput.termLayout X T origin 10 (termsEnd.trans_lt H.isLt)).2.2.1
  apply ShrinkDescriptorReads.fields stored H.val ins.level _ ins.motif ins.hidden ins.slot count
    (show rd (O).hist from trivial) cdReads
  · omega
  · omega
  · change (ev (O).level).val + 59 < H.val
    rw [old.live.header]
    have := areas.levelEnd
    omega

section Handler

variable {k₀ : Type} [_root_.Field k₀] {S : BlockSchedule k₀} (B : S.Templates)
variable {sel₀ : X.ShrinkSelection B.shrink} (job : Job X B.shrink ready sel₀ m party w)
variable {t : ℕ} (ordinal : B.Entry → Fin t)

/-- The selected handler's entire successful event list reads below the terminal
controller header, including the external setup of its private descriptor. -/
theorem Job.abi_success_reads
    (old : job.OldPublished O pub state mem level T origin)
    (areas : job.ABAreas level T origin H.val)
    (termsEnd : ShrinkInput.termEnd X origin 10 ≤ H.val)
    (I : LocalHistory.EntryInput B.shrink) (width : MapConstants.widthThreshold B.shrink ≤ w) :
    SourceTransport.Reads (· < H.val) ((ShrinkCallABI.family B degree a ordinal).successEvents
      demandMass_pos I width pub state mem) := by
  obtain ⟨ptr, fields⟩ := job.abi_descriptor_reads degree old areas termsEnd
  exact (ShrinkCallABI.family B degree a ordinal).successEvents_readsFrom demandMass_pos I width
    pub state mem (· < H.val) ptr (fields I.party)

end Handler

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
