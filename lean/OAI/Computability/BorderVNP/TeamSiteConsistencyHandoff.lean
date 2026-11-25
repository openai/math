import OAI.Computability.BorderVNP.TeamContractionWireChecks
import OAI.Computability.BorderVNP.TeamSiteEndpointRuns

/-! # Gluing the physically shared handoff fields across all real sites

An internal sender and its successor inspect the identical raw bits in the actual wire
assignment. Canonical frame encoding is injective, so the decoded incoming control and
clock are the preceding outgoing control and clock. The final halt is checked locally and
adds no wire variable. All these checks also apply to a valid zero-weight path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency

open VPVNP TeamContraction.Wires TeamTapeHandoff
open BurstRAM (Word)
open TeamSite.Endpoint (closeMode)

variable {r k w : ℕ}

/-- The internal array consists of the non-final real processor outputs in index order. -/
def internalFrames (out : Fin r → Frame w k) (i : Fin (r-1)) : Frame w k :=
  out ⟨i.val,by have := i.isLt; omega⟩

/-- Register-link readout at the incoming and outgoing checks of the actual processors,
with the program's public first frame taking the place of a missing predecessor. -/
structure FrameChecks (raw : Fin (r-1) → Fin (frameWidth k w) → Bool) (first : Frame w k)
    (input out : Fin r → Frame w k) : Prop where
  /-- Public first-processor state. -/
  initial : ∀ j, j.val = 0 → input j = first
  /-- Decoded canonical predecessor at each real internal boundary. -/
  received : ∀ j, 0 < j.val → (input j).bits = frameInput raw true j
  /-- Actual transmitted canonical output at each real internal boundary. -/
  sent : ∀ j, j.val+1 < r → (out j).bits = frameInput raw false j

/-- The real finish table returns its successful label exactly for a correct frame.
This includes `sg = none`: the validity check precedes the signed zero contribution. -/
theorem finishLabel_done_iff {p a pub m g : ℕ} {P : TeamOpcode.Program p k pub a} {Q : Type}
    (sg : Option Bool) (live : Option (Fin p)) (last : Bool) (regs : Fin k → Word w)
    (elapsed : Word w) (candidate : List Bool) :
    TeamSite.Endpoint.finishLabel sg (TeamSite.Endpoint.valid (closeMode live) last regs elapsed candidate) =
      (TeamSite.Endpoint.Label.done sg : TeamSite.Endpoint.Label P Q m g) ↔
      if last then live = none else (TeamLocalClock.Finish.frame (closeMode live) regs elapsed).bits = candidate := by
  cases last with
  | false =>
    by_cases h : (TeamLocalClock.Finish.frame (closeMode live) regs elapsed).bits = candidate <;>
      simp [TeamSite.Endpoint.finishLabel,TeamSite.Endpoint.valid,h]
  | true =>
    cases live <;> simp [TeamSite.Endpoint.finishLabel,TeamSite.Endpoint.valid,closeMode,TeamLocalClock.Finish.Mode.halted]

/-- Raw slot agreement forces exact equality of the two neighboring typed frames. -/
theorem FrameChecks.adjacent {raw first input out} (checks : FrameChecks (r := r) (k := k) (w := w)
    raw first input out) (i j : Fin r) (h : j.val = i.val+1) : input j = out i := by
  have hi := i.isLt
  have hj := j.isLt
  let b : Fin (r-1) := ⟨i.val,by omega⟩
  have ei : i = ⟨b.val,by have := b.isLt; omega⟩ := rfl
  have ej : j = ⟨b.val+1,by have := b.isLt; omega⟩ := Fin.ext h
  have same := adjacent_frame b
  rw [← ei,← ej] at same
  apply Frame.bits_injective
  rw [checks.received _ (by omega),checks.sent _ (by omega),frameInput,frameInput,same]

/-- Internal output bits uniquely determine every actual raw frame wire, even when the
first processor also happens to be the final processor. -/
theorem FrameChecks.assignment {raw first input out} (checks : FrameChecks (r := r) (k := k) (w := w)
    raw first input out) : raw = frameAssignment (internalFrames out) := by
  funext i
  apply List.ofFn_injective
  rw [frameAssignment_bits]
  let j : Fin r := ⟨i.val,by have := i.isLt; omega⟩
  have hj : j.val+1 < r := by have := i.isLt; dsimp [j]; omega
  have he := checks.sent j hj
  simpa [frameInput,frameIndex,j,internalFrames,show i.val+1 < r from hj] using he.symm

private theorem chain_indices (P : Control w k → TeamRAM.Instr w (Control w k)) (limit : Word w)
    (r : ℕ) (first : Frame w k) (input out : Fin r → Frame w k) (chunks : Fin r → List (TeamRAM.Event w))
    (head : ∀ j, j.val = 0 → input j = first)
    (adj : ∀ i j, j.val=i.val+1 → input j = out i)
    (step : ∀ j, nextFrame P limit (input j) (chunks j) = some (out j)) :
    Chain P limit first (List.ofFn chunks) (List.ofFn out) := by
  induction r generalizing first with
  | zero => simp [Chain]
  | succ r ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    refine ⟨(head 0 rfl ▸ step 0),?_⟩
    apply ih (out 0) (fun j => input j.succ) (fun j => out j.succ) (fun j => chunks j.succ)
    · intro j h; apply adj 0 j.succ; simp [h]
    · intro i j h; apply adj i.succ j.succ; simp [h]
    · intro j; exact step j.succ

/-- Canonical physical predecessor decoding and sender equality join the local transition
tables to the original sequential register chain, without a further link assumption. -/
theorem FrameChecks.chain {raw first input out} (checks : FrameChecks (r := r) (k := k) (w := w)
    raw first input out) (P : Control w k → TeamRAM.Instr w (Control w k)) (limit : Word w)
    (chunks : Fin r → List (TeamRAM.Event w))
    (step : ∀ j, nextFrame P limit (input j) (chunks j) = some (out j)) :
    Chain P limit first (List.ofFn chunks) (List.ofFn out) :=
  chain_indices P limit r first input out chunks checks.initial checks.adjacent step

/-- A native sequential chain and any locally validated physical chain yield the same
complete frame list and the same canonical interior register-link bits. -/
theorem FrameChecks.native_frames {raw first input out} (checks : FrameChecks (r := r) (k := k) (w := w)
    raw first input out) (P : Control w k → TeamRAM.Instr w (Control w k)) (limit : Word w)
    (chunks : Fin r → List (TeamRAM.Event w)) (frames : Fin r → Frame w k)
    (native : Chain P limit first (List.ofFn chunks) (List.ofFn frames))
    (step : ∀ j, nextFrame P limit (input j) (chunks j) = some (out j)) :
    out = frames ∧ raw = frameAssignment (internalFrames frames) := by
  have he := List.ofFn_injective (chain_unique P limit (checks.chain P limit chunks step) native)
  exact ⟨he, he ▸ checks.assignment⟩

/-- Input to site zero is public; later sites receive the exact preceding native output. -/
def predecessor (first : Frame w k) (out : Fin r → Frame w k) (j : Fin r) : Frame w k :=
  if h : 0 < j.val then out ⟨j.val-1,by have := j.isLt; omega⟩ else first

/-- Conversely, the native frames fill the true handoff wires once and pass the receiver
and sender tests at every endpoint. -/
theorem native_frame_checks (first : Frame w k) (out : Fin r → Frame w k) :
    FrameChecks (frameAssignment (internalFrames out)) first (predecessor first out) out := by
  constructor
  · intro j h; simp [predecessor,h]
  · intro j h; simp [predecessor,frameInput,frameIndex,h,frameAssignment_bits,internalFrames]
  · intro j h; simp [frameInput,frameIndex,h,frameAssignment_bits,internalFrames]

private theorem indexed_step (P : Control w k → TeamRAM.Instr w (Control w k)) (limit : Word w)
    (r : ℕ) (first : Frame w k) (input out : Fin r → Frame w k) (chunks : Fin r → List (TeamRAM.Event w))
    (head : ∀ j, j.val = 0 → input j = first)
    (adj : ∀ i j, j.val=i.val+1 → input j = out i)
    (chain : Chain P limit first (List.ofFn chunks) (List.ofFn out)) :
    ∀ j, nextFrame P limit (input j) (chunks j) = some (out j) := by
  induction r generalizing first with
  | zero => intro j; exact j.elim0
  | succ r ih =>
    rw [List.ofFn_succ,List.ofFn_succ] at chain
    refine Fin.cases (head 0 rfl ▸ chain.1) ?_
    apply ih (out 0) (fun j => input j.succ) (fun j => out j.succ) (fun j => chunks j.succ) _ _ chain.2
    · intro j h; apply adj 0 j.succ; simp [h]
    · intro i j h; apply adj i.succ j.succ; simp [h]

/-- Each physical owner's predecessor in the canonical native assignment realizes exactly
the next-frame equation of the global native register chain. -/
theorem native_step (P : Control w k → TeamRAM.Instr w (Control w k)) (limit : Word w)
    (first : Frame w k) (out : Fin r → Frame w k) (chunks : Fin r → List (TeamRAM.Event w))
    (chain : Chain P limit first (List.ofFn chunks) (List.ofFn out)) (j : Fin r) :
    nextFrame P limit (predecessor first out j) (chunks j) = some (out j) :=
  let checks := native_frame_checks first out
  indexed_step P limit r first _ out chunks checks.initial checks.adjacent chain j

end TeamSiteConsistency

end BorderVNP
end Computability
end OAI
