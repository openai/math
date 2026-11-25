import OAI.Computability.BorderVNP.TeamSiteConsistencyInterior
import OAI.Computability.BorderVNP.TeamSiteConsistencyHandoff
import OAI.Computability.BorderVNP.TeamSiteChunkJoint

/-! # Actual finite processor histories and transmitted interior bits

The sites store their native instruction events, canonical typed successor state and
one assignment on all real frame and sort wires. Shared physical receive and send
checks identify the typed inputs from the predecessor, including an accepted idle site.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency

open VPVNP RAMTape RAMTape.PublicExprMachine TeamRAM TeamTapeHandoff TeamContraction.Wires
open TeamTapeSorting TeamTapeInputRoute.Verify
open BurstRAM (Word)
variable {teams w p r k a e : ℕ}

/-- Fields of a complete one-team validator path. All physical interior wires occur once. -/
structure RawHistory (teams r w e : ℕ) where
  /-- The actual ordered events at each real site. -/
  blocks : Fin teams → List (Event w)
  /-- Complete outgoing register frame, with the accepted frame propagated across idle sites. -/
  frames : Fin teams → Frame w r
  /-- Every physical register, sorter-send and boundary field bit. -/
  links : Edge teams r w e (w+1) → Bool

/-- Actual typed inputs and raw frame wires are forced by the outgoing frames. -/
theorem frameChecks_iff {first : Frame w r} {ins out : Fin teams → Frame w r}
    {raw : Fin (teams-1) → Fin (frameWidth r w) → Bool} :
    FrameChecks raw first ins out ↔ raw = frameAssignment (internalFrames out) ∧ ins = predecessor first out := by
  constructor
  · intro check
    refine ⟨check.assignment,?_⟩
    funext j
    by_cases h : 0 < j.val
    · let i : Fin teams := ⟨j.val-1,by have := j.isLt; omega⟩
      have hij : j.val = i.val+1 := by dsimp [i]; omega
      simpa only [predecessor,dite_eq_left_iff,h,↓reduceDIte] using check.adjacent i j hij
    · simpa [predecessor,h] using check.initial j (by omega)
  · rintro ⟨rfl,rfl⟩
    exact native_frame_checks first out

/-- The finite-PC schedule checked on the physical path, including the mandatory
accepted frame on the final real processor. -/
def Scheduled (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : TeamOpcode.Macros w a)
    (start : TeamOpcode.State w p r) (H limit cap : Word w) (es : List (Event w))
    (blocks : Fin teams → List (Event w)) (out : Fin teams → Frame w r) : Prop :=
  (List.ofFn blocks).flatten = es ∧ TeamSite.ChargedRows P pub lib H limit cap
    (initial (packed w start.pc.val) start.reg) (List.ofFn blocks) (List.ofFn out) ∧
    (List.ofFn out).getLast? = some (.accepted (packed w (cost es)))

/-- Both raw handoff checks and all actual real-owner memory checks, including the
secondary virtual lane when one is assigned to that owner. -/
def RawHistory.WireChecks (z : RawHistory teams r w e) (first : Frame w r) (input : Fin teams → List Bool)
    (hw : 2 ≤ w+1) (hc : 2^(Nat.clog 2 teams)*2^e < 2^(w+1)) : Prop :=
  FrameChecks (edgeEquiv z.links).1 first (predecessor first z.frames) z.frames ∧
    ∀ j, ownerValid hw hc (edgeEquiv z.links).2 (array e input z.blocks) (primary j) (secondary j)

private theorem wireChecks_iff_owners (z : RawHistory teams r w e) (first : Frame w r) (input : Fin teams → List Bool)
    (hw : 2 ≤ w+1) (hc : 2^(Nat.clog 2 teams)*2^e < 2^(w+1)) :
    z.WireChecks first input hw hc ↔ OwnerChecks hw hc input z.blocks (internalFrames z.frames) z.links := by
  simp only [RawHistory.WireChecks,OwnerChecks,frameChecks_iff,eq_self,and_true]
  apply and_congr_left'
  constructor
  · intro eq j; rw [eq,frameAssignment_bits]
  · intro h; funext j; exact List.ofFn_injective ((h j).trans (frameAssignment_bits _ _).symm)

/-- The real sender/receiver conditions and paired buffer checks at each site recover
the native execution and force the actual bit assignment, for every proposed path. -/
theorem RawHistory.wireChecks_iff_execute (z : RawHistory teams r w e) (first : Frame w r)
    (input : Fin teams → List Bool) {S : Type*} {P : S → Instr w S} {start : S}
    (hr : 0 < teams) (hw : 2 ≤ w+1) (hc : 2^(Nat.clog 2 teams)*2^e < 2^(w+1))
    (loc : Local P start (List.ofFn z.blocks).flatten)
    (time : 1+cost (List.ofFn z.blocks).flatten ≤ 2^w)
    (header : (List.ofFn input).flatten.length ≤ 2^w)
    (size : ∀ j, (realRows input z.blocks j).length ≤ 4*2^e) :
    z.WireChecks first input hw hc ↔ z.links = canonicalLinks hw (internalFrames z.frames) (array e input z.blocks) ∧
      execute P start (inputMemory w input) ((List.ofFn z.blocks).flatten.map Event.choices) =
        some (List.ofFn z.blocks).flatten :=
  (wireChecks_iff_owners ..).trans (ownerChecks_iff_execute hr hw hc input z.blocks _ z.links loc time header size)

/-- Signed contribution of all actual per-processor event paths, including an absorbed zero. -/
def RawHistory.weight (z : RawHistory teams r w e) : ℤ :=
  ((List.ofFn z.blocks).map fun es => (TeamPrivateCall.sign (TeamSite.chunkSign (some false) es)).value).prod

theorem RawHistory.weight_eq (z : RawHistory teams r w e) :
    z.weight = ((List.ofFn z.blocks).flatten.map (Sign.value ∘ Event.sign)).prod := by
  unfold RawHistory.weight
  have weight (es : List (Event w)) : (TeamPrivateCall.sign (TeamSite.chunkSign (some false) es)).value =
      (es.map (Sign.value ∘ Event.sign)).prod := by
    rw [TeamSite.chunkSign_value]
    change 1 * _ = _
    exact one_mul _
  simp_rw [weight]
  exact Team.prod_block_weights (Sign.value ∘ Event.sign) rfl

end TeamSiteConsistency

end BorderVNP
end Computability
end OAI
