import OAI.Computability.BorderVNP.PackedFrozenOuterProjection
import OAI.Computability.BorderVNP.PackedFrozenNativeInnerProjection
import OAI.Computability.BorderVNP.PackedHistoryNormalizedProfile

/-! # Projection of every frozen-tape history onto its original geometric history

The statement ranges over all profile digits, including invalid count words.
It identifies the accepted word with the very same code of the original
dependent history and projects every returned geometric bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Inherited WorkWords FrozenTape ProgramSchemas EnrichedOuter VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1500000
set_option maxRecDepth 4500

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {start T w : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (R : Compiled bits deep budget cap w)
    (base : Format) (header : WorkWords.Ports (CoverScale.sites (Cube D) start))
    (leaf : P ↪ Fin (CoverScale.sites (Cube D) start)) (wr : WidthRanges S start T w) (hm : 0 < m)

/-- Every augmented outer step evaluates to its original state and flag on
the public geometry pins, on every possible child and histogram assignment. -/
theorem tapeSteps_project :
    StepsProject (fun _ z => .inl (.inl z)) (R.tapeSteps base header leaf wr hm) R.machine.steps := by
  intro t ht xg result
  exact R.tapeStep_project base t ht (prepHeader (S:=S) t header) (wr.initial t ht)
    (R.stageSteps base header leaf wr hm t ht) (R.stageSteps_project base header leaf wr hm t ht) xg result


variable {σ : Type} [Fintype σ] (init : Frame σ (outerPins S start w base 0))
    (source : Frame σ (Boundary.Pins S start (boundaryShape S start) w 0))
    (x : σ → Bool) (same : init.eval x ∘ (fun z => .inl (.inl z)) = source.eval x)
include same

/-- For the complete real compiled tree the projection covers both returned
geometry and the bank flag, even for guesses failing at an internal node. -/
theorem tapeCompile_project (g : Slot (fan S) (Machine.Guess S start (fun _ _ => w)) T → Bool) :
    output (R.tapeSteps base header leaf wr hm) T le_rfl (repeatLeaf (fan S) init T) x g ∘ (fun z => .inl (.inl z)) = output R.machine.steps T le_rfl (repeatLeaf (fan S) source T) x g ∧
      flag (R.tapeSteps base header leaf wr hm) T le_rfl (repeatLeaf (fan S) init T) x g = flag R.machine.steps T le_rfl (repeatLeaf (fan S) source T) x g :=
  (R.tapeSteps_project base header leaf wr hm).repeatLeaf T le_rfl init source x x same g

variable (bottom : Admissible (Boundary.Good (S:=S) (start:=start) (bits:=bits)
    (shape:=boundaryShape S start) (w:=w) budget) 0) (seedRead : source.eval x = bottom.val.words)
variable {reserve : ℕ} (widths : ℕ → ℕ) (order : ∀ j, Machine.Guess S start (fun _ _ => w) j ≃ Fin (widths j)) (fit : broadcastWidth (fan S) widths T ≤ reserve)

/-- Every padded word accepted by the augmented machine is the unique original
dependent history code. All unused positions obey the original zero-padding rule. -/
theorem tapeCode_valid (profile : Fin reserve → Bool) :
    validProfile (broadcastOrder (fan S) widths order T) fit (fun g => flag (R.tapeSteps base header leaf wr hm) T le_rfl (repeatLeaf (fan S) init T) x g = true) profile ↔
      ∃! q : (packHistory bottom R.machine.epoch T).Index, (R.machine.nativeCode bottom source x seedRead widths order fit q).val = profile := by
  have eqn : (fun g => flag (R.tapeSteps base header leaf wr hm) T le_rfl (repeatLeaf (fan S) init T) x g = true) = (fun g => flag R.machine.steps T le_rfl (repeatLeaf (fan S) source T) x g = true) := by
    funext g
    rw [(R.tapeCompile_project base header leaf wr hm init source x same g).2]
  exact (congrArg (fun test => validProfile (broadcastOrder (fan S) widths order T) fit test profile) eqn).to_iff.trans
    (R.machine.nativeCode_valid bottom source x seedRead widths order fit profile)

/-- Decoding the original code in the augmented machine returns the exact
same state of that history, with its stored routes, directory and padding. -/
theorem tapeCode_geometry (q : (packHistory bottom R.machine.epoch T).Index) :
    output (R.tapeSteps base header leaf wr hm) T le_rfl (repeatLeaf (fan S) init T) x (readProfile (broadcastOrder (fan S) widths order T) fit (R.machine.nativeCode bottom source x seedRead widths order fit q).val) ∘ (fun z => .inl (.inl z)) =
      ((packHistory bottom R.machine.epoch T).term q).val.words :=
  (R.tapeCompile_project base header leaf wr hm init source x same _).1.trans
    (R.machine.nativeCode_state bottom source x seedRead widths order fit q)

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
