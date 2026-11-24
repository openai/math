import OAI.Computability.VPVNP.PairShrinkPartyNative

/-!
# Choices and external writes of a shrinking-party gather

Operand setup and slice headers only read external memory. Each subsequent
bit copy takes private steps. These trace properties hold for arbitrary
packet contents and values returned by the header probes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentColumn

open BurstRAM CompressorRecords
open scoped Fin.CommRing
open private no_choices from OAI.Computability.VPVNP.CompressorRecordRegisterSetup
open private eval_no_writes from OAI.Computability.VPVNP.CompressorFormulaFootprint

variable {N w : ℕ} (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)

private theorem frameTrace_noChoices (s : Setup) (row : Row) :
    choiceBits (frameTrace s row pub state m) = [] := by
  have head : choiceBits (PrivateSlices.headerEvents m (row.frame : Word w)) = [] := by
    by_cases h : m ((row.frame : Word w) + 1 + 1).val = 0 <;>
      simp [PrivateSlices.headerEvents, h, choiceBits]
  simp only [frameTrace, PrivateSlices.frameEvents, PrimedInputRAM.Flow.choiceBits_append,
    no_choices, head, List.nil_append]
  split <;> simp [choiceBits, PrivateFields.events_bits]

private theorem frameTrace_noWrites (s : Setup) (row : Row) :
    SourceTransport.Writes (fun _ ↦ False) (frameTrace s row pub state m) := by
  intro a v h
  rcases List.mem_append.mp h with setup | frame
  · exact eval_no_writes (fun _ ↦ False) pub state m _ _ a v setup
  rcases List.mem_append.mp frame with head | copy
  · by_cases h : m ((row.frame : Word w) + 1 + 1).val = 0 <;>
      simp [PrivateSlices.headerEvents, h] at head
  · split at copy
    · exact List.not_mem_nil copy
    · exact (FlowFootprint.bounds_of_noProbes (fun _ ↦ False) (fun _ ↦ False)
        (PrivateFields.events_work (w := w) .copy row.bits).2).2 a v copy

variable (S : Fin N → Setup) (row : Fin N → Row) (is : List (Fin N))

theorem trace_noChoices : choiceBits (trace S row is pub state m) = [] := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [trace, List.flatMap_cons, PrimedInputRAM.Flow.choiceBits_append,
      frameTrace_noChoices, List.nil_append]
    exact ih

theorem trace_noWrites : SourceTransport.Writes (fun _ ↦ False) (trace S row is pub state m) := by
  intro a v h
  obtain ⟨i, _, frame⟩ := List.mem_flatMap.mp h
  exact frameTrace_noWrites pub state m (S i) (row i) a v frame

end PairSimulation.ResidentColumn

namespace PairSimulation.ShrinkPartyNative

open BurstRAM CompressorRecords Compression Compression.State Compression.ShrinkMotif
open MotifBlocks MotifConversion MotifGrid

variable {a b g w : ℕ} {δ factor : ℝ} {K : Type*} [_root_.Field K]
  {X : State a (packingLaneBits a g)}
  {F : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
  {m : X.packingData.Motif} {party : Fin 6}
  (J : Job (a := a) (b := b) (g := g) X F ready sel m party w)
  (O : ShrinkCallHeader.Operands) (nodeExpr : PhaseRecipe.Expr) (pub : Fin 5 → Word w)
  (state : Word w) (mem : Memory w)

theorem Job.trace_noChoices : choiceBits (J.trace O nodeExpr pub state mem) = [] :=
  ResidentColumn.trace_noChoices pub state mem _ _ _

theorem Job.trace_noWrites :
    SourceTransport.Writes (fun _ ↦ False) (J.trace O nodeExpr pub state mem) :=
  ResidentColumn.trace_noWrites pub state mem _ _ _

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
