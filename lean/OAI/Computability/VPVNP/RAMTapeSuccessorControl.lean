import OAI.Computability.VPVNP.RAMTapeSuccessorCap
import OAI.Computability.VPVNP.RAMTapeSuccessorScan
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-!
# The fixed stack control for checking a parsed successor field

The control reads each of the eight little-endian words, retaining its
small tag. It compares the cost and the cap bit by bit. All input words
are restored. The two output stacks receive the running-state flag and
the format validity flag, respectively.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Successor

open BurstRAM RAMSerialization SuccessorTags TapeWord

/-- Stacks for the eight parsed words, cap comparison, running-state bit, and field verdict. -/
inductive CheckPort where
  | word (i : Fin 8) | cap | tmp | capTmp | running | verdict
  deriving DecidableEq, Fintype

/-- Phases for scanning successor tags, comparing the cost with the cap, and emitting the
running and validity bits. -/
inductive CheckState where
  | tags (q : TagState)
  | cap (tagOK running : Bool) (q : SuccessorCap.State)
  | emit (good running : Bool)
  | verdict (good : Bool)
  | done
  deriving DecidableEq, Fintype

/-- Wire the cap comparator to successor word one, the public cap, and their two scratch
stacks. -/
def capPorts : ScanPort → CheckPort
  | .left => .word 1
  | .right => .cap
  | .tmp => .tmp
  | .out => .capTmp

private theorem capPorts_inj : Function.Injective capPorts := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

/-- Scan the eight word tags, compare cost against the cap, and push the running bit and field
validity bit. -/
def checkCode (present : Bool) : StackCode CheckPort CheckState
  | .tags (.done t) => .goto (.cap (valid present t true) (decide (t 0 = .one)) (.left true))
  | .tags q => (tagCode CheckPort.word .tmp q).rename id CheckState.tags
  | .cap ok run (.done withinCap) => .goto (.emit (ok && (!present || withinCap)) run)
  | .cap ok run q => (SuccessorCap.code q).rename capPorts (CheckState.cap ok run)
  | .emit good run => .push .running run (.verdict good)
  | .verdict good => .push .verdict good .done
  | .done => .halt true

/-- Push the supplied running bit and verdict onto their respective stacks, preserving the rest
of the bank. -/
def checkResult (s : Stacks CheckPort) (good run : Bool) : Stacks CheckPort :=
  Function.update (Function.update s .running (run :: s .running)) .verdict (good :: s .verdict)

theorem check_run {w : ℕ} (present : Bool) (s : Stacks CheckPort) (a : Fin 8 → Word w) (cap : Word w)
    (hw : ∀ i, s (.word i) = BurstRAM.wordBits (a i)) (hc : s .cap = BurstRAM.wordBits cap)
    (ht : s .tmp = []) (hu : s .capTmp = []) :
    StackRuns (checkCode present) (40 * w + 22) (.tags tagEntry) s .done
      (checkResult s (valid present (wordTags a) (decide ((a 1).val ≤ cap.val)))
        (decide ((wordTags a) 0 = .one))) := by
  let t := wordTags a
  let run := decide (t 0 = .one)
  let ok := valid present t true
  let withinCap := decide ((a 1).val ≤ cap.val)
  have hh := tag_run CheckPort.word .tmp (fun _ h ↦ by cases h) s ht a hw
  have hframe : installStacks id s s = s := funext fun i ↦ installStacks_at Function.injective_id s s i
  have htags := hh.lift id Function.injective_id CheckState.tags s (target := checkCode present)
    (by intro q hq; cases q <;> first | rfl | contradiction)
  rw [hframe] at htags
  have hstart : StackStep (checkCode present) (.tags (.done t)) s (.cap ok run (.left true)) s := .goto rfl
  have hcap := SuccessorCap.run_lift (target := checkCode present) capPorts capPorts_inj
    (CheckState.cap ok run) (by intro q hq; cases q <;> first | rfl | contradiction) s
    (by simp [capPorts, hw, hc]) ht hu
  simp only [capPorts, hw, hc, length_wordBits, value_wordBits] at hcap
  have hv : (ok && (!present || withinCap)) = valid present t withinCap := by
    cases present <;> cases withinCap <;> simp [ok, valid]
  have hfinal : StackRuns (checkCode present) 3 (.cap ok run (.done withinCap)) s .done
      (checkResult s (valid present t withinCap) run) := by
    rw [← hv]
    refine .cons (.goto rfl) (.cons (.push rfl) ?_)
    exact .cons (.push rfl) (.nil ..)
  have total := htags.trans (.cons hstart (hcap.trans hfinal))
  convert total using 1
  omega

/-- Install the successor checker on the caller's ports for a present field or an absent-edge
clamp. -/
def checkRoutine {K : Type} (ports : CheckPort → K) (present : Bool) : FiniteRoutine K :=
  FiniteRoutine.ofStackCode (checkCode present) ports (.tags tagEntry) (fun q ↦ decide (q = .done))

theorem checkRoutine_runs {K : Type} [DecidableEq K] {w : ℕ} (ports : CheckPort → K)
    (hp : Function.Injective ports) (present : Bool) (s : Stacks K) (a : Fin 8 → Word w) (cap : Word w)
    (hw : ∀ i, s (ports (.word i)) = BurstRAM.wordBits (a i))
    (hc : s (ports .cap) = BurstRAM.wordBits cap)
    (ht : s (ports .tmp) = []) (hu : s (ports .capTmp) = []) :
    (checkRoutine ports present).Runs (40 * w + 22) s
      (installStacks ports s (checkResult (s ∘ ports)
        (valid present (wordTags a) (decide ((a 1).val ≤ cap.val))) (decide ((wordTags a) 0 = .one)))) := by
  have h := FiniteRoutine.runs_ofStackCode (normal := fun q ↦ decide (q = .done)) hp
    (by decide) (by decide) (fun q h ↦ by simpa only [decide_eq_true_eq] using
      ((of_decide_eq_true h) ▸ (show ((checkCode present) .done).returns = true from rfl))) s
    (check_run present (s ∘ ports) a cap hw hc ht hu)
  rwa [installStacks_eq hp s (s ∘ ports) (fun _ ↦ rfl)] at h

end RAMTape.Successor

end VPVNP
end Computability
end OAI
