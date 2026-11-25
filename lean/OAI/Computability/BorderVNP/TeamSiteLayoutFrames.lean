import OAI.Computability.BorderVNP.TeamSiteLayout

/-! # Cutting raw register handoffs from a signed processor tape

The first processor reads a pinned initial frame from the literal. Every later processor
reads its predecessor frame from the incident interior bits. Every processor with a
successor reads its proposed outgoing frame from the same stream. The sorter receives
the remaining bytes in their original order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Layout

open VPVNP BurstRAM RAMTape

variable {r k d w : ℕ}

/-- One tag and one word each for the PC, the registers, and the elapsed clock. -/
def frameSize (r w : ℕ) := 1+(r+2)*w

local notation "P" => Port r k d

private def marks : ℕ → FiniteRoutine P
  | 0 => .ofRoutine { entry := (), code := fun _ => .push .frameWidth true none }
  | n+1 => (WordCopy.mapWord .tmp .frameWidth (fun _ => true) .width).followedBy (marks n)

private theorem marks_runs (n : ℕ) (s : Stacks P) (ht : s .tmp = []) :
    (marks n).Runs (n*(5*(s .width).length+2)+1) s
      (Function.update s .frameWidth (List.replicate (1+n*(s .width).length) true ++ s .frameWidth)) := by
  induction n generalizing s with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero, List.replicate_one, List.singleton_append]
    exact .cons (.push rfl) (.nil ..)
  | succ n ih =>
    let L := (s .width).length
    let mid := Function.update s .frameWidth (List.replicate L true ++ s .frameWidth)
    have h₁ : (WordCopy.mapWord .tmp .frameWidth (fun _ => true) .width).Runs (5*L+2) s mid := by
      simpa [mid,L,List.map_const'] using WordCopy.mapWord_run (.tmp : P) .frameWidth (fun _ => true)
        (show (Port.width : P) ≠ .tmp by intro e; cases e) (by intro e; cases e)
        (by intro e; cases e) s ht
    have h₂ := ih mid (by simpa [mid] using ht)
    change (marks n).Runs (n*(5*L+2)+1) mid
      (Function.update mid .frameWidth (List.replicate (1+n*L) true ++ mid .frameWidth)) at h₂
    change (marks (n+1)).Runs ((n+1)*(5*L+2)+1) s
      (Function.update s .frameWidth (List.replicate (1+(n+1)*L) true ++ s .frameWidth))
    rw [show (n+1)*(5*L+2)+1 = (5*L+2)+(n*(5*L+2)+1) by ring,
      show 1+(n+1)*L = (1+n*L)+L by ring, List.replicate_add, List.append_assoc]
    simpa only [marks,mid,Function.update_idem,Function.update_self] using h₁.followedBy h₂

/-- Prepare a reusable unary frame width from the measured logical word width. -/
def frameMarks : FiniteRoutine P := marks (r+2)

/-- The constructor uses one marker per tag or word bit, independent of all frame values. -/
theorem frameMarks_runs (s : Stacks P) (hw : (s .width).length = w)
    (hs : s .frameWidth = []) (ht : s .tmp = []) :
    frameMarks.Runs ((r+2)*(5*w+2)+1) s
      (Function.update s .frameWidth (List.replicate (frameSize r w) true)) := by
  simpa only [frameMarks,frameSize,hw,hs,List.append_nil] using marks_runs (r+2) s ht

/-- Whether a physical frame is supplied as public initialization, predecessor data,
or a candidate successor. -/
inductive FrameSource | literal | previous | next
  deriving DecidableEq

/-- The physical field supplying this frame. -/
def FrameSource.source : FrameSource → P
  | .literal => metadata
  | .previous | .next => incident

/-- The endpoint checker consumes predecessor and successor data on distinct stacks. -/
def FrameSource.dest : FrameSource → P
  | .literal | .previous => .incoming
  | .next => .outgoing

private def wordPorts (f : FrameSource) : SuccessorFields.WordPort → P
  | .input => f.source
  | .width => .frameWidth
  | .tmp => .tmp
  | .out => f.dest

private theorem wordPorts_injective (f : FrameSource) : Function.Injective (wordPorts (r := r) (k := k) (d := d) f) := by
  intro i j h; cases f <;> cases i <;> cases j <;> simp_all [wordPorts,FrameSource.source,FrameSource.dest]

/-- Consume exactly one fixed-size raw frame. Its tags and canonicality are checked by the
endpoint machine after extraction. -/
def takeFrame (f : FrameSource) : FiniteRoutine P :=
  FiniteRoutine.ofStackCode SuccessorFields.wordCode (wordPorts f) .collect (fun q => decide (q = .done))

/-- The extracted frame preserves every bit, including invalid payloads, and the route
stream now begins with the next field. -/
theorem takeFrame_runs (f : FrameSource) (s : Stacks P) (data tail : List Bool)
    (hin : s f.source = data ++ tail) (hw : s .frameWidth = List.replicate data.length true)
    (ht : s .tmp = []) (he : s f.dest = []) :
    (takeFrame f).Runs (6*data.length+2) s
      (Function.update (Function.update s f.source tail) f.dest data) := by
  let small := s ∘ wordPorts f
  unfold takeFrame
  apply FiniteRoutine.runs_ofStackCode_framed (wordPorts_injective f)
    (src := SuccessorFields.wordCode) (normal := fun q => decide (q = .done)) (entry := .collect)
    (exit := .done) rfl rfl (fun q h => by obtain rfl := of_decide_eq_true h; rfl)
    (SuccessorFields.word_runs small data tail hin hw ht) (fun _ => rfl)
  · intro q
    cases f <;> cases q <;> simp_all [small,wordPorts,FrameSource.source,FrameSource.dest]
  · intro p h
    have hi := Ne.symm (h .input)
    have ho := Ne.symm (h .out)
    simp only [wordPorts] at hi ho
    simp [hi,ho]

end TeamSite.Layout

end BorderVNP
end Computability
end OAI
