import OAI.Computability.BorderVNP.TeamTapeInputEmit
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-! # Initializing the team record-buffer stacks from the processor's public fields

The padded binary starting address supplies the width for the zero word. Four scans
of the unary bucket capacity allocate every sorting slot. The header, the address
word, and the public capacity are preserved while the fixed named-stack table prepares
the cursor and buffer. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputEmit.Setup

open VPVNP BurstRAM RAMTape

/-- Public data and named ports of the emitter. -/
inductive Port where
  | start | bucket | emit (p : TeamTapeInputEmit.Port)
  deriving DecidableEq, Fintype

private abbrev scratch := Port.emit (.buffer .temp)
private abbrev zeros := Port.emit (.buffer .zeros)
private abbrev remaining := Port.emit (.buffer .remaining)

private def copyCursor := SuccessorFields.prependCopy Port.start (.emit .cursor) scratch
private def zeroWord := WordCopy.mapWord scratch zeros (fun _ => false) .start
private def addSlots := WordCopy.mapWord scratch remaining (fun _ => true) .bucket

private def slotCopies : ℕ → FiniteRoutine Port
  | 0 => .ret
  | k+1 => addSlots.followedBy (slotCopies k)

/-- Copy the starting address, form the zero word and install four free slots per
unit of the public capacity. -/
def setup : FiniteRoutine Port :=
  (copyCursor.followedBy zeroWord).followedBy (slotCopies 4)

/-- Initial public parameters and input bits, with empty scratch and record storage. -/
def input (w H a : ℕ) (bs : List Bool) : Stacks Port
  | .start => wordBits (word w a)
  | .bucket => List.replicate H true
  | .emit .bits => bs
  | _ => []

/-- Public parameters preserved, cursor and empty record buffer installed. -/
def prepared (w H a : ℕ) (bs : List Bool) : Stacks Port
  | .emit .cursor => wordBits (word w a)
  | .emit (.buffer .zeros) => List.replicate w false
  | .emit (.buffer .remaining) => List.replicate (4*H) true
  | p => input w H a bs p

private theorem slotCopies_runs (k H : ℕ) (s : Stacks Port) (hs : s scratch = [])
    (hH : (s .bucket).length = H) :
    (slotCopies k).Runs (k*(5*H+2)+1) s
      (Function.update s remaining (List.replicate (k*H) true ++ s remaining)) := by
  induction k generalizing s with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.nil_append, Function.update_eq_self]
    exact Routine.runs_ret s
  | succ k ih =>
    let mid := Function.update s remaining (List.replicate H true ++ s remaining)
    have h₁ : addSlots.Runs (5*H+2) s mid := by
      simpa [addSlots, mid, List.map_const', hH] using
        WordCopy.mapWord_run scratch remaining (fun _ => true) (by decide : Port.bucket ≠ scratch)
          (by decide) (by decide) s hs
    have h₂ := ih mid (by simpa [mid] using hs) (by simpa [mid] using hH)
    have run := h₁.followedBy h₂
    rw [show (k+1)*(5*H+2)+1 = (5*H+2)+(k*(5*H+2)+1) by ring, Nat.succ_mul k H, List.replicate_add]
    simpa only [slotCopies, mid, Function.update_self, Function.update_idem, List.append_assoc] using run

/-- Exact deterministic execution from the parsed layout and header. The table derives the
word width from the address and the free-slot marks from the bucket tally. -/
theorem setup_runs (w H a : ℕ) (bs : List Bool) :
    setup.Runs (10*w+20*H+13) (input w H a bs) (prepared w H a bs) := by
  let s := input w H a bs
  let x := Function.update s (.emit .cursor) (wordBits (word w a))
  let y := Function.update x zeros (List.replicate w false)
  have hx : copyCursor.Runs (5*w+2) s x := by
    simpa [copyCursor, s, x, input] using SuccessorFields.prependCopy_runs Port.start (.emit .cursor)
      scratch (by decide) (by decide) (by decide) s rfl
  have hy : zeroWord.Runs (5*w+2) x y := by
    simpa [zeroWord, x, y, s, input] using WordCopy.zero_template scratch zeros
      (by decide : Port.start ≠ scratch) (by decide) (by decide) x rfl rfl
  have hz := slotCopies_runs 4 H y rfl (by simp [y,x,s,input])
  have hout : Function.update y remaining (List.replicate (4*H) true ++ y remaining) =
      prepared w H a bs := by
    funext p; cases p with
    | start => rfl
    | bucket => rfl
    | emit q =>
      cases q with
      | bits => rfl
      | cursor => rfl
      | buffer r => cases r <;> simp [prepared,y,x,s,input]
  rw [hout] at hz
  simpa only [setup, show 5*w+2+(5*w+2)+(4*(5*H+2)+1) = 10*w+20*H+13 by omega] using
    (hx.followedBy hy).followedBy hz

/-- The prepared bank meets every entry condition of the physical initialization emitter. -/
theorem ready {w : ℕ} (hw : 2 ≤ w) (H a : ℕ) (bs : List Bool) :
    Ready hw H a bs [] (prepared w H a bs ∘ Port.emit) :=
  ⟨rfl, rfl, ⟨by simp, rfl, rfl, rfl, rfl, rfl⟩, fun _ => Nat.zero_le _⟩

end TeamTapeInputEmit.Setup

end BorderVNP
end Computability
end OAI
