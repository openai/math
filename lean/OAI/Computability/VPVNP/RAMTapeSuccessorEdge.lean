import OAI.Computability.VPVNP.RAMTapeSuccessorControl
import OAI.Computability.VPVNP.RAMTapeSuccessorFields
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-!
# Executing one successor field check on the incident stack

Read the next eight words, check the successor or its boundary clamp, and
retain the five-word raw record for the final predecessor check. Every
fixed-length bit pattern returns both flags in the same number of steps.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorEdge

open BurstRAM RAMSerialization Successor

/-- Registers for reading an incident successor field, checking its cost and tags, and
retaining its record and flags. -/
inductive Port where
  | input | width | tmp | cap | capTmp | running | verdict | record | word (i : Fin 8)
  deriving DecidableEq, Fintype

private def readPorts : SuccessorFields.Port → Port
  | .input => .input
  | .width => .width
  | .tmp => .tmp
  | .word i => .word i

private def checkPorts : CheckPort → Port
  | .cap => .cap
  | .capTmp => .capTmp
  | .running => .running
  | .verdict => .verdict
  | .tmp => .tmp
  | .word i => .word i

private def recordPorts : SuccessorFields.RecordPort → Port
  | .tmp => .tmp
  | .record => .record
  | .word i => .word i

private theorem readPorts_inj : Function.Injective readPorts := by
  intro a b h
  cases a <;> cases b <;> simp_all [readPorts]

private theorem checkPorts_inj : Function.Injective checkPorts := by
  intro a b h
  cases a <;> cases b <;> simp_all [checkPorts]

private theorem recordPorts_inj : Function.Injective recordPorts := by
  intro a b h
  cases a <;> cases b <;> simp_all [recordPorts]

variable {w : ℕ}

/-- Raw little-endian bits of words 3 through 7. They are copied even for a
malformed record, so the boundary check sees the actual incident payload. -/
def recordBits (a : Fin 8 → Word w) : List Bool :=
  (List.ofFn fun i : Fin 5 => BurstRAM.wordBits (a (Fin.natAdd 3 i))).flatten

private theorem recordBits_words (a : Fin 8 → Word w) :
    recordBits a = BurstRAM.wordBits (a 3) ++ BurstRAM.wordBits (a 4) ++
      BurstRAM.wordBits (a 5) ++ BurstRAM.wordBits (a 6) ++ BurstRAM.wordBits (a 7) := by
  simp only [recordBits, List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]
  rfl

private def localEdge (present : Bool) : FiniteRoutine Port :=
  ((SuccessorFields.read readPorts).followedBy (checkRoutine checkPorts present)).followedBy
    (SuccessorFields.appendRecord recordPorts)

/-- A caller chooses the physical stacks for all inputs, scratch, and outputs. -/
def edge {K : Type} (ports : Port → K) (present : Bool) : FiniteRoutine K :=
  (localEdge present).onPorts ports

/-- Exact state at the return from one edge check. The input head now points
to the next field. The cap word and unary width are available for that field. -/
def edgeResult (s : Stacks Port) (present : Bool) (bits : Fin (8*w) → Bool) (cap : Word w)
    (suffix : List Bool) : Stacks Port :=
  let a := (arrayBits 8 w).symm bits
  fun p => match p with
    | .input => suffix
    | .word i => BurstRAM.wordBits (a i)
    | .record => recordBits a ++ s .record
    | .running => decide (wordTags a 0 = .one) :: s .running
    | .verdict => valid present (wordTags a) (decide ((a 1).val ≤ cap.val)) :: s .verdict
    | p => s p

private def extracted (s : Stacks Port) (a : Fin 8 → Word w) (suffix : List Bool) : Stacks Port
  | .input => suffix
  | .word i => BurstRAM.wordBits (a i)
  | p => s p

private def flagged (s : Stacks Port) (good run : Bool) : Stacks Port
  | .running => run :: s .running
  | .verdict => good :: s .verdict
  | p => s p

private theorem localEdge_runs (present : Bool) (s : Stacks Port) (bits : Fin (8*w) → Bool)
    (cap : Word w) (suffix : List Bool) (hin : s .input = List.ofFn bits ++ suffix)
    (hw : s .width = List.replicate w true) (hc : s .cap = BurstRAM.wordBits cap)
    (ht : s .tmp = []) (hu : s .capTmp = []) (hwords : ∀ i, s (.word i) = []) :
    (localEdge present).Runs (113*w+49) s (edgeResult s present bits cap suffix) := by
  let a := (arrayBits 8 w).symm bits
  let t := extracted s a suffix
  let good := valid present (wordTags a) (decide ((a 1).val ≤ cap.val))
  let run := decide (wordTags a 0 = .one)
  let u := flagged t good run
  have h₁ := SuccessorFields.read_raw_runs readPorts readPorts_inj s bits suffix hin hw ht
  have he : installStacks readPorts s
      (SuccessorFields.result (s ∘ readPorts) (fun i => BurstRAM.wordBits (a i)) suffix) = t := by
    apply installStacks_frame readPorts_inj
    · intro k
      cases k <;> simp [t, extracted, readPorts, SuccessorFields.result, hwords]
    · intro l hl
      cases l with
      | input => exact (hl .input rfl).elim
      | word i => exact (hl (.word i) rfl).elim
      | _ => rfl
  rw [he] at h₁
  have h₂ := checkRoutine_runs checkPorts checkPorts_inj present t a cap
    (fun _ => rfl) hc ht hu
  have he' : installStacks checkPorts t (checkResult (t ∘ checkPorts) good run) = u := by
    apply installStacks_frame checkPorts_inj
    · intro k
      cases k <;> simp [u, flagged, checkResult, checkPorts]
    · intro l hl
      cases l with
      | running => exact (hl .running rfl).elim
      | verdict => exact (hl .verdict rfl).elim
      | _ => rfl
  rw [he'] at h₂
  have h₃ := SuccessorFields.appendRecord_runs recordPorts_inj u (w := w) ht
    (fun i _ => BurstRAM.length_wordBits (a i))
  have hf : Function.update u (recordPorts .record)
      (u (recordPorts (.word 3)) ++ u (recordPorts (.word 4)) ++ u (recordPorts (.word 5)) ++
        u (recordPorts (.word 6)) ++ u (recordPorts (.word 7)) ++ u (recordPorts .record)) =
      edgeResult s present bits cap suffix := by
    funext p
    cases p <;> simp [edgeResult, u, t, extracted, flagged, recordPorts, recordBits_words, a, good, run]
  rw [hf] at h₃
  rw [show 113*w+49 = (8*(6*w+2)+1)+(40*w+22)+(25*w+10) by omega]
  exact (h₁.followedBy h₂).followedBy h₃

/-- On all wire values, the same exact stack cost covers extraction, testing,
and the copy needed for the predecessor condition. -/
theorem edge_runs {K : Type} [DecidableEq K] (ports : Port → K) (hp : Function.Injective ports)
    (present : Bool) (s : Stacks K) (bits : Fin (8*w) → Bool) (cap : Word w) (suffix : List Bool)
    (hin : s (ports .input) = List.ofFn bits ++ suffix)
    (hw : s (ports .width) = List.replicate w true) (hc : s (ports .cap) = BurstRAM.wordBits cap)
    (ht : s (ports .tmp) = []) (hu : s (ports .capTmp) = [])
    (hwords : ∀ i, s (ports (.word i)) = []) :
    (edge ports present).Runs (113*w+49) s
      (installStacks ports s (edgeResult (s ∘ ports) present bits cap suffix)) := by
  have h := (localEdge present).runs_onPorts hp s
    (localEdge_runs present (s ∘ ports) bits cap suffix hin hw hc ht hu hwords)
  rwa [installStacks_eq hp s (s ∘ ports) (fun _ => rfl)] at h

end RAMTape.SuccessorEdge

end VPVNP
end Computability
end OAI
