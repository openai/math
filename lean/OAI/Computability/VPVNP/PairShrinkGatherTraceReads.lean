import OAI.Computability.VPVNP.PairShrinkPartyNative

/-!
# External reads of the selected shrinking-party gather

Each visited frame contributes its compiled pointer loads and the three
possible slice-header reads. The published interval banks identify the
header addresses and prove that they fit in the native word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentColumn

open BurstRAM CompressorRecords
open private frame_reads from OAI.Computability.VPVNP.PairResidentFrameColumn
open private reads_append from OAI.Computability.VPVNP.CompressorFormulaFootprint

/-- The allowed pointer and header addresses of the rows cover every external
read in their chronological trace. -/
theorem trace_reads {N w : ℕ} (S : Fin N → Setup) (row : Fin N → Row) (is : List (Fin N))
    (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w) (allowed : ℕ → Prop)
    (safe : ∀ i, (row i).ReadSafe (S i) allowed pub state mem)
    (fit : ∀ i, (row i).frame + 2 < 2 ^ w) :
    SourceTransport.Reads allowed (trace S row is pub state mem) := by
  intro addr value read
  obtain ⟨i, _, hit⟩ := List.mem_flatMap.mp read
  have loads := RegisterSetup.lines_reads (S i).operands allowed pub state mem (safe i).loads
    (fun _ ↦ 0)
  exact reads_append loads (frame_reads (row i) (S i) allowed pub state mem (safe i) (fit i))
    addr value hit

end PairSimulation.ResidentColumn

namespace PairSimulation.ShrinkPartyNative

open BurstRAM CompressorRecords CompressorRecords.ShrinkSlots Compression Compression.ShrinkMotif
open MotifBlocks MotifConversion MotifGrid ShrinkPartyColumns
open private Job.recorded from OAI.Computability.VPVNP.PairShrinkPartyNative

variable {a b g w : ℕ} {δ factor : ℝ} {K : Type*} [_root_.Field K]
  {X : State a (packingLaneBits a g)}
  {F : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
  {m : X.packingData.Motif} {party : Fin 6}
  (J : Job X F ready sel m party w) (O : ShrinkCallHeader.Operands) (nodeExpr : PhaseRecipe.Expr)
  (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w) (allowed : ℕ → Prop)
  {level absolute : Word w} {T U : IncidenceDirectory w} {origin layer pitch : ℕ}
  {heads : SlotLevel.Heads}

local notation "side" => selectedLayout X F sel

/-- The public trace of the actual resident job reads only the addresses
allowed for its AB and surviving rows. -/
theorem Job.trace_reads (old : J.OldPublished O pub state mem level T origin)
    (next : J.SupplyPublished O nodeExpr pub state mem heads absolute U layer pitch)
    (safe : ∀ c i, (J.row c i).ReadSafe (setups O nodeExpr a b party side c i)
      allowed pub state mem) :
    SourceTransport.Reads allowed (J.trace O nodeExpr pub state mem) :=
  ResidentColumn.trace_reads _ _ _ pub state mem allowed (fun _ ↦ safe _ _)
    (fun _ ↦ (Job.recorded J O nodeExpr pub state mem old next _ _).frameFit)

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
