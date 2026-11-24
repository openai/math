import OAI.Computability.VPVNP.EvaluatorProgramInput
import OAI.Computability.VPVNP.EvaluatorInputBank

/-!
# Advice and exponent fields on a single binary input

The parser loads four header fields and the callback payload from the advice
prefix. The suffix carries the runtime exponent vector and three copies of
its unary width for the converter and the two scheduler counters. Scratch
ports start empty without consuming any input.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorProgramRawInput

open RAMTape EvaluatorRoutine EvaluatorProgramInput Evaluator.InputBank

variable {P : Type}

private def header : List (Port P) :=
  [.rowCount, .word .divisor, .sched (.addr .width), .sched .labels]

private def runtimePorts : List (Port P) :=
  [.width, .word .original, .sched (.addr .rounds), .sched .colsLeft]

private def workPort (p : P) : Port P := .sched (.work p)

/-- The parser's ordered ports depend only on the fixed callback register list. -/
def fields (ps : List P) := (header ++ ps.map workPort) ++ runtimePorts

private theorem fields_nodup {ps : List P} (hp : ps.Nodup) : (fields ps).Nodup := by
  have hinj : Function.Injective (workPort (P := P)) := fun _ _ h =>
    EvaluatorDigitFetch.Port.work.inj (Port.sched.inj h)
  rw [fields, List.nodup_append', List.nodup_append']
  refine ⟨⟨by simp [header], hp.map hinj, ?_⟩, by simp [runtimePorts], ?_⟩
  · intro k hk h
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    simp [header, workPort] at hk
  · intro k hk h
    rcases List.mem_append.mp hk with ha | hw
    · simp [header] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> simp [runtimePorts] at h
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hw
      simp [runtimePorts, workPort] at h

/-- Advice contains the fixed binary divisor, the dimensions which depend
on the label system, and the specified callback registers. -/
def advice (ps : List P) (t : ℕ) (d : List Bool) (payload : Stacks P) : List Bool :=
  fieldBits (List.replicate t true) ++ fieldBits d ++ fieldBits (List.replicate d.length true) ++
    fieldBits (List.replicate t true) ++ ps.flatMap (fun k => fieldBits (payload k))

/-- The runtime input depends only on the width and the native exponent array. -/
def runtime {t Z : ℕ} (e : Fin t → BurstRAM.Word Z) : List Bool :=
  fieldBits (List.replicate Z true) ++ fieldBits (List.ofFn (RAMSerialization.arrayBits t Z e)) ++
    fieldBits (List.replicate Z true) ++ fieldBits (List.replicate Z true)

theorem runtime_length {t Z : ℕ} (e : Fin t → BurstRAM.Word Z) :
    (runtime e).length = 2*(t*Z)+6*Z+4 := by
  simp only [runtime, List.length_append, length_fieldBits, List.length_replicate, List.length_ofFn]
  omega

theorem advice_length (ps : List P) (t : ℕ) (d : List Bool) (payload : Stacks P) :
    (advice ps t d payload).length =
      4*t + 4*d.length + 4 + (ps.map fun k => 2*(payload k).length+1).sum := by
  simp only [advice, List.length_append, List.length_replicate, length_fieldBits,
    List.length_flatMap]
  omega

/-- The advice bytes are independent of both the exponent values and their width. -/
theorem rawInput_eq {t Z : ℕ} (ps : List P) (e : Fin t → BurstRAM.Word Z) (d : List Bool)
    (payload : Stacks P) :
    rawInput (fields ps) (initial e d payload) = advice ps t d payload ++ runtime e := by
  simp only [fields, rawInput, List.flatMap_append, header, runtimePorts,
    List.flatMap_cons, List.flatMap_nil, List.flatMap_map, advice, runtime, List.append_assoc,
    List.append_nil]
  rfl

private theorem outside_empty {t Z : ℕ} (ps : List P) (hall : ∀ p, p ∈ ps)
    (e : Fin t → BurstRAM.Word Z) (d : List Bool) (payload : Stacks P) (k : Port P)
    (hk : k ∉ fields ps) : initial e d payload k = [] := by
  cases k with
  | sched k =>
    cases k with
    | addr k =>
      cases k <;> first | rfl | simp [fields, header, runtimePorts] at hk
    | work p => exact (hk (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨p, hall p, rfl⟩)))).elim
    | _ => first | rfl | simp [fields, header, runtimePorts] at hk
  | word k => cases k <;> first | rfl | simp [fields, header, runtimePorts] at hk
  | _ => first | rfl | simp [fields, header, runtimePorts] at hk

/-- The clock for loading the self-delimiting input fields, charging three instructions per
payload bit and one for each field terminator. -/
def readTicks {t Z : ℕ} (ps : List P) (e : Fin t → BurstRAM.Word Z) (d : List Bool)
    (payload : Stacks P) :=
  ((fields ps).map (fun k => 3*(initial e d payload k).length+1)).sum + 1

/-- Each encoded data bit and field terminator costs at most two parser steps. -/
theorem readTicks_le {t Z : ℕ} (ps : List P) (e : Fin t → BurstRAM.Word Z) (d : List Bool)
    (payload : Stacks P) :
    readTicks ps e d payload ≤ 2*((advice ps t d payload).length + (runtime e).length) + 1 := by
  let s := initial e d payload
  have bound (ks : List (Port P)) :
      (ks.map (fun k => 3*(s k).length+1)).sum ≤ 2*(rawInput ks s).length := by
    induction ks with
    | nil => simp [rawInput]
    | cons k ks ih =>
      simp only [rawInput, List.flatMap_cons, List.length_append, length_fieldBits,
        List.map_cons, List.sum_cons]
      change _ ≤ 2*(rawInput ks s).length at ih
      simp only [rawInput] at ih
      omega
  have h := bound (fields ps)
  dsimp only [s] at h
  rw [rawInput_eq, List.length_append] at h
  exact Nat.add_le_add_right h 1

theorem reader_runs [DecidableEq P] {t Z : ℕ} (ps : List P) (hp : ps.Nodup)
    (hall : ∀ p, p ∈ ps) (e : Fin t → BurstRAM.Word Z) (d : List Bool) (payload : Stacks P) :
    (reader (fields ps)).Runs (readTicks ps e d payload)
      (frame (advice ps t d payload ++ runtime e) (fun _ => [])) (frame [] (initial e d payload)) := by
  simpa only [readTicks, rawInput_eq] using load_selected_runs (fields ps) (fields_nodup hp)
    (initial e d payload) (outside_empty ps hall e d payload)

/-- Load the advice and exponents before calling the fixed physical machine. -/
def withReader (ps : List P) (r : FiniteRoutine (Port P)) : FiniteRoutine (Option (Port P)) :=
  (reader (fields ps)).followedBy (r.onPorts some)

theorem withReader_realizes [DecidableEq P] {t Z : ℕ} {S T : Type*}
    (ps : List P) (hp : ps.Nodup) (hall : ∀ p, p ∈ ps) (e : Fin t → BurstRAM.Word Z)
    (d : List Bool) (payload : S → Stacks P) (r : FiniteRoutine (Port P))
    {post : T → Stacks (Port P)} {B R : ℕ} {effect : (T → ℕ) → S → ℕ}
    (hR : ∀ x, readTicks ps e d (payload x) ≤ R)
    (h : Realizes r.body (initial e d ∘ payload) post B effect) :
    Realizes (withReader ps r).body
      (fun x => frame (advice ps t d (payload x) ++ runtime e) (fun _ => []))
      (frame [] ∘ post) (R+B) effect := by
  have hpref : Realizes (reader (fields ps)).body
      (fun x => frame (advice ps t d (payload x) ++ runtime e) (fun _ => []))
      (fun x => frame [] (initial e d (payload x))) R (fun f x => f x) := by
    apply Realizes.of_runs (g := id)
    intro x
    exact ⟨_, hR x, reader_runs ps hp hall e d (payload x)⟩
  apply hpref.followedBy
  intro extra fuel hf x f c hc
  rw [r.count_onPorts some (Option.some_injective _)]
  apply h extra fuel hf x f
  intro y n hn
  have he : installStacks some (frame [] (initial e d (payload x))) (post y) = frame [] (post y) := by
    apply installStacks_frame (small := post y) (target := frame [] (post y))
      (Option.some_injective _) (fun _ => rfl)
    intro k hk
    cases k with
    | none => rfl
    | some k => exact (hk k rfl).elim
  rw [he]
  exact hc y n hn

end EvaluatorProgramRawInput

end VPVNP
end Computability
end OAI
