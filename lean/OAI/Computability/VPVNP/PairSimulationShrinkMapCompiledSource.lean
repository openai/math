import OAI.Computability.VPVNP.PairSimulationShrinkMapRowRetention
import OAI.Computability.VPVNP.PairSimulationShrinkMapTermReadback
import OAI.Computability.VPVNP.PairSimulationShrinkMapVertexMemory
import OAI.Computability.VPVNP.CompressorCompiledResident
import OAI.Computability.VPVNP.CompressorShrinkHistoryDirectory
import OAI.Computability.VPVNP.CompressorShrinkScoreOperands

/-!
# The actual compiled shrinking map source at a selected vertex

The compiled payload records the native term run of its producing occurrence
and retains the grid ordinal of each of its selected motifs. The resident map
and term heads in that same payload are the words read by the shrinking map
segment. The final vertex frame preserves these operands at every ordinal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM Compression CompressorRecords DescriptorSpace MapResidentRows LocalHistory
open scoped Fin.CommRing

variable {w : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  (base : Word w) (positions blocks n cur : ℕ) (i : Fin S.steps) {g : ℕ}
  (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
  (sel : SelectedScore.Selection B X)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

local notation "lay" => BlockProgram.layout B base.val positions blocks
local notation "head" => levelStart lay cur
local notation "next" => levelStart lay (cur + 1)
local notation "tab" => (fun j : Fin 6 => tableBase lay cur j)
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "bank" => ShrinkResidentLayout.layout X (tab 5)
local notation "side" => SelectedFinish.chosen B X sel
local notation "inc" => packedIncidence lay w cur (DemandRAM.oldCount X)

open private grid_word_eq from OAI.Computability.VPVNP.PairSimulationShrinkMapTermReadback

/-- Extract the map arrays, term records and descriptor from one compiled
shrinking payload. The certificate for the term words is the actual run stored
by the producer, with its original input memory and chronological reports. -/
theorem mapRowSource_compiled {m : Memory w}
    (payload : CompiledResident.ShrinkPayload B base positions blocks n cur i X sel m) :
    let p := (bank).params (ShrinkBlockInputs.a i) true w
    ∃ R : MapRowSource X sel side m (head : Word w) term,
      R.first = tab 5 ∧ R.InLevel lay cur ∧
      MapResidentInputs.Published m (head : Word w) (p 3) (p 5) term 10 := by
  have bounds := payload.bounds
  have words := payload.words
  have room := words.oldRoom
  have levelVal : (head : Word w).val = head := Nat.mod_eq_of_lt (by omega)
  have low (j : Fin 6) : head + 65 < tab j := by
    change head + 65 < head + 66 + 6 * slotCapacity lay + j.val * tableWords lay
    omega
  have firstEnd : tab 1 ≤ next :=
    (Nat.le_add_right ..).trans (tableEnd_le_nextLevel lay cur (1 : Fin 6))
  have termLow := (low 0).le.trans (ScorePackets.start_le_term i X (tab 0) bounds.termRoom)
  have nextRoom := (levelStart_mono lay bounds.nextLive.le).trans_lt bounds.room
  have rowFit := bounds.residentEnd.trans_lt nextRoom
  have termHigh : (term).val + (shrinkMotifOrder X).length * 10 ≤ next := by
    apply le_trans _ (bounds.termBefore.trans firstEnd)
    rw [show (shrinkMotifOrder X).length =
      ShrinkTermSelection.bundles X * ShrinkTermSelection.ranks (ShrinkBlockInputs.a i) from
      ShrinkTermSelection.motifCount_eq X]
    exact Nat.add_le_add_right (Nat.mod_le ..) _
  obtain ⟨dense, fuel, before, reports, written⟩ := payload.termRun
  have grid (e : X.packingData.Motif) :
      m ((term).val + (ordinal X e).val * 10) =
      after before (eventLog reports) ((term).val + (ordinal X e).val * 10) := by
    have fits : (term).val + (ordinal X e).val * 10 < 2 ^ w := by
      have epos := (ordinal X e).isLt
      exact lt_of_lt_of_le (by omega) nextRoom.le
    have addr : (ShrinkTermSelection.rowBase X term 10 e).val =
        (term).val + (ordinal X e).val * 10 := Nat.mod_eq_of_lt fits
    have live := (payload.sources.terms e).1
    have source := (written.fields e).1
    rw [addr] at live source
    exact grid_word_eq live source
  let params := (bank).params (ShrinkBlockInputs.a i) true w
  have p : MapResidentInputs.Published m (head : Word w) (params 3) (params 5) term 10 := by
    have pos (j : ℕ) (hj : j ≤ 65) : ((head : Word w) + (j : Word w)).val = head + j := by
      rw [← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [levelVal]
      exact words.residentHeads 4
    · rw [levelVal]
      exact words.residentHeads 5
    · rw [levelVal, ← pos 36 (by decide)]
      exact words.level.termHead
    · rw [levelVal, ← pos 37 (by decide)]
      exact words.level.termStride
  let R : MapRowSource X sel side m (head : Word w) term :=
    ⟨tab 5, rowFit, payload.sources.residents true, dense, fuel, before, reports, written,
      termHigh.trans nextRoom.le, grid, words.level.layout⟩
  have floor : levelsBase lay ≤ head := Nat.le_add_right ..
  refine ⟨R, rfl, ⟨levelVal, ?_, ?_, ?_, bounds.residentEnd, ?_, termHigh⟩, p⟩
  · rw [levelVal]
    exact (by omega : head + 38 ≤ head + 65).trans_lt ((low 1).trans_le firstEnd)
  · rw [levelVal]
    omega
  · exact (floor.trans (Nat.le_add_right ..)).trans (low 5).le
  · exact (floor.trans (Nat.le_add_right ..)).trans termLow

section Vertex

open LiveProgram.PairStages LiveProgram.PairStages.Group.Auxiliary TraversalRows

variable {G : Group} {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
  {lanes T : ℕ} (hT : T * S.laneBits ≤ lanes) (start : State (S.degreeExponent 0) lanes)
  (z : (B.execute f hf T hT start).Choices)

local notation "vs" => executeLevels B f hf T hT start z
local notation "pub" => terminalOperands G
set_option quotPrecheck false in
local notation "D" => BlockProgram.layout B (terminalOperands G 2).val positions T
local notation "Y" => StateExecution.finalState (B.execute f hf T hT start) z

/-- Read the actual row certificate at an arbitrary later final-site call of
the packed terminal program, identifying the producing pass by its selected
occurrence in the executed history. -/
theorem mapRowSource_vertex (j : Fin (vs).length) (tape : List Bool)
    (occurrence : vs[j] = shrinkLevel B f hf i X sel tape)
    {table : Fin (D).shape.tables} {baseBits laneBits cap width ord : ℕ}
    {roles : List TraversalRoles.TaggedLayer} {calendar reference phy : Memory G.w}
    {bits : Fin (Y).totalWidth → Bool}
    (history : SelectedPayloadHistory.Past B f hf D
      (CompiledResident.payload B f hf (pub 2) positions T n) vs calendar)
    (entry : TerminalProgram.VertexEntry B f hf T hT start z D table baseBits laneBits pub
      calendar reference bits)
    (packed : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord phy) :
    let level := (levelStart D j.val : Word G.w)
    let first := tableBase D j.val (5 : Fin 6)
    let selectedTerm := ShrinkInput.termHead (w := G.w) X (tableBase D j.val (0 : Fin 6))
    let p := (ShrinkResidentLayout.layout X first).params (ShrinkBlockInputs.a i) true G.w
    ∃ R : MapRowSource X sel side phy level selectedTerm, R.first = first ∧
      MapResidentInputs.Published phy level (p 3) (p 5) selectedTerm 10 := by
  have own := CompiledResident.read history j
  rw [occurrence] at own
  have payload := (CompiledResident.shrink_payload ..).mp own
  obtain ⟨R, first, bounds, heads⟩ :=
    mapRowSource_compiled B (pub 2) positions T n j.val i X sel payload
  have agree := entry.packedLevelWindow packed frame j
  exact ⟨R.transport bounds agree, first, R.published bounds heads agree⟩

end Vertex

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
