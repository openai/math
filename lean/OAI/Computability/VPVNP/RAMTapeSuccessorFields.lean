import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.RAMWordBits

/-!
# Splitting the successor wire on the physical incident tape

One unary width stack supplies a count for each of the eight words. After each
word, the reader restores this count and reverses the saved bits into their
destination stack, preserving the least-significant-bit-first representation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorFields

/-- Stacks for extracting one fixed-width word from the incident bit stream. -/
inductive WordPort where
  | input | width | tmp | out
  deriving DecidableEq

instance : Fintype WordPort := derive_fintype% _

/-- Control states for collecting a word, restoring its unary width, and rejecting an exhausted
incident stream. -/
inductive Phase where
  | collect | readBit | save (bit : Bool) | restore | put (bit : Bool) | mark | done | reject
  deriving DecidableEq, Fintype

/-- Read one field of the width given in unary, then restore its markers for the next field. -/
def wordCode : StackCode WordPort Phase
  | .collect => .pop .width fun mark => mark.elim .restore fun _ => .readBit
  | .readBit => .pop .input fun b => b.elim .reject .save
  | .save b => .push .tmp b .collect
  | .restore => .pop .tmp fun b => b.elim .done .put
  | .put b => .push .out b .mark
  | .mark => .push .width true .restore
  | .done => .halt true
  | .reject => .halt false

private def wordStacks (input width tmp out : List Bool) : Stacks WordPort
  | .input => input
  | .width => width
  | .tmp => tmp
  | .out => out

private theorem update_wordStacks (input width tmp out new : List Bool) (k : WordPort) :
    Function.update (wordStacks input width tmp out) k new = match k with
      | .input => wordStacks new width tmp out
      | .width => wordStacks input new tmp out
      | .tmp => wordStacks input width new out
      | .out => wordStacks input width tmp new := by
  funext j
  cases k <;> cases j <;> rfl

local macro "field_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [wordStacks, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, update_wordStacks])

private theorem collect_runs (data suffix tmp out : List Bool) :
    StackRuns wordCode (3 * data.length + 1) .collect
      (wordStacks (data ++ suffix) (List.replicate data.length true) tmp out)
      .restore (wordStacks suffix [] (data.reverse ++ tmp) out) := by
  induction data generalizing tmp with
  | nil =>
    simp only [List.length_nil, List.nil_append, List.reverse_nil, List.replicate_zero,
      Nat.mul_zero, Nat.zero_add]
    field_step
    exact .nil ..
  | cons b data ih =>
    simp only [List.length_cons, List.cons_append, List.replicate_succ, List.reverse_cons,
      List.append_assoc, Nat.mul_succ]
    field_step
    field_step
    field_step
    exact ih (b :: tmp)

private theorem restore_runs (input width tmp out : List Bool) :
    StackRuns wordCode (3 * tmp.length + 1) .restore (wordStacks input width tmp out)
      .done (wordStacks input (List.replicate tmp.length true ++ width) [] (tmp.reverse ++ out)) := by
  induction tmp generalizing width out with
  | nil =>
    simp only [List.length_nil, List.nil_append, List.reverse_nil, List.replicate_zero,
      Nat.mul_zero, Nat.zero_add]
    field_step
    exact .nil ..
  | cons b tmp ih =>
    simp only [List.length_cons, List.replicate_succ', List.reverse_cons, List.append_assoc,
      List.singleton_append, Nat.mul_succ]
    field_step
    field_step
    field_step
    exact ih (true :: width) (b :: out)

/-- Extract the given word in its original order, restoring its unary width. -/
theorem word_runs (s : Stacks WordPort) (data suffix : List Bool)
    (hin : s .input = data ++ suffix) (hw : s .width = List.replicate data.length true)
    (ht : s .tmp = []) :
    StackRuns wordCode (6 * data.length + 2) .collect s .done
      (Function.update (Function.update s .input suffix) .out (data ++ s .out)) := by
  have hc := collect_runs data suffix [] (s .out)
  simp only [List.append_nil] at hc
  have hr := restore_runs suffix [] data.reverse (s .out)
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at hr
  have hs : wordStacks (data ++ suffix) (List.replicate data.length true) [] (s .out) = s := by
    funext k
    cases k <;> simp [wordStacks, hin, hw, ht]
  have hf : wordStacks suffix (List.replicate data.length true) [] (data ++ s .out) =
      Function.update (Function.update s .input suffix) .out (data ++ s .out) := by
    funext k
    cases k <;> simp [wordStacks, hw, ht]
  rw [hs] at hc
  rw [hf] at hr
  convert hc.trans hr using 1
  omega

/-- Shared input, width, and scratch stacks and the eight individual successor word stacks. -/
inductive Port where
  | input | width | tmp | word (index : Fin 8)
  deriving DecidableEq, Fintype

private def wordPorts (i : Fin 8) : WordPort → Port
  | .input => .input
  | .width => .width
  | .tmp => .tmp
  | .out => .word i

private theorem wordPorts_injective (i : Fin 8) : Function.Injective (wordPorts i) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

private def wordReturn (q : Phase) := decide (q = .done)

private def one (i : Fin 8) : FiniteRoutine Port :=
  FiniteRoutine.ofStackCode wordCode (wordPorts i) .collect wordReturn

private theorem one_runs (i : Fin 8) (s : Stacks Port) (data suffix : List Bool)
    (hin : s .input = data ++ suffix) (hw : s .width = List.replicate data.length true)
    (ht : s .tmp = []) : (one i).Runs (6 * data.length + 2) s
      (Function.update (Function.update s .input suffix) (.word i) (data ++ s (.word i))) := by
  let small := s ∘ wordPorts i
  apply FiniteRoutine.runs_ofStackCode_framed (wordPorts_injective i) (normal := wordReturn)
    (entry := .collect) (exit := .done) rfl rfl
    (fun q h => by have hq : q = .done := of_decide_eq_true h; subst q; rfl)
    (word_runs small data suffix hin hw ht) (fun _ => rfl)
  · intro k
    cases k <;> simp [wordPorts, small]
  · intro l hl
    have ho : l ≠ .word i := Ne.symm (hl .out)
    have hi : l ≠ .input := Ne.symm (hl .input)
    simp [ho, hi]

/-- The indices of the eight words are fixed in the finite control. -/
private def indices := List.ofFn (id : Fin 8 → Fin 8)

private def readList : List (Fin 8) → FiniteRoutine Port
  | [] => FiniteRoutine.ret
  | i :: is => (one i).followedBy (readList is)

private def afterList (s : Stacks Port) (data : Fin 8 → List Bool)
    (is : List (Fin 8)) (suffix : List Bool) : Stacks Port
  | .input => suffix
  | .word i => if i ∈ is then data i ++ s (.word i) else s (.word i)
  | .tmp => s .tmp
  | .width => s .width

private theorem readList_runs
    (w : ℕ) (data : Fin 8 → List Bool) (hdata : ∀ i, (data i).length = w)
    (is : List (Fin 8)) (hd : is.Nodup) (s : Stacks Port) (suffix : List Bool)
    (hin : s .input = is.flatMap data ++ suffix) (hw : s .width = List.replicate w true)
    (ht : s .tmp = []) :
    (readList is).Runs (is.length * (6*w+2) + 1) s (afterList s data is suffix) := by
  induction is generalizing s with
  | nil =>
    have he : afterList s data [] suffix = s := by
      funext k
      cases k <;> simp_all [afterList]
    rw [he]
    rw [List.length_nil, Nat.zero_mul, Nat.zero_add]
    exact Routine.runs_ret s
  | cons i is ih =>
    let rest := is.flatMap data ++ suffix
    let mid := Function.update (Function.update s .input rest) (.word i) (data i ++ s (.word i))
    have h₁ : (one i).Runs (6*w+2) s mid := by
      rw [← hdata i]
      exact one_runs i s (data i) rest (by simpa [rest, List.append_assoc] using hin)
        (by simpa [hdata] using hw) ht
    have h₂ := ih (List.nodup_cons.mp hd).2 mid (by simp [mid, rest])
      (by simpa [mid] using hw) (by simpa [mid] using ht)
    have he : afterList mid data is suffix = afterList s data (i :: is) suffix := by
      have hi := (List.nodup_cons.mp hd).1
      funext k
      cases k with
      | word j =>
        by_cases hj : j = i
        · subst j
          simp [afterList, mid, hi]
        · simp [afterList, mid, hj]
      | input | width | tmp => simp [afterList, mid]
    rw [he] at h₂
    change ((one i).followedBy (readList is)).Runs ((is.length+1)*(6*w+2)+1) s _
    rw [Nat.succ_mul, show is.length * (6*w+2) + (6*w+2) + 1 =
      (6*w+2) + (is.length * (6*w+2) + 1) by omega]
    exact h₁.followedBy h₂

/-- After reading, the next field starts at the top of the input stack. The
public width and the scratch stack have their original contents. -/
def result (s : Stacks Port) (data : Fin 8 → List Bool) (suffix : List Bool) : Stacks Port
  | .input => suffix
  | .word i => data i ++ s (.word i)
  | .width => s .width
  | .tmp => s .tmp

private theorem readEight_runs
    (w : ℕ) (data : Fin 8 → List Bool) (hdata : ∀ i, (data i).length = w)
    (s : Stacks Port) (suffix : List Bool) (hin : s .input = (List.ofFn data).flatten ++ suffix)
    (hw : s .width = List.replicate w true) (ht : s .tmp = []) :
    (readList indices).Runs (8*(6*w+2)+1) s (result s data suffix) := by
  have hi : indices.flatMap data = (List.ofFn data).flatten := by
    rw [List.flatMap_def, indices, List.map_ofFn]
    rfl
  have he : afterList s data indices suffix = result s data suffix := by
    funext k
    cases k with
    | word i =>
      have hm : i ∈ indices := List.mem_ofFn.mpr ⟨i, rfl⟩
      simp [afterList, result, hm]
    | input | tmp | width => rfl
  have h := readList_runs w data hdata indices (by decide) s suffix (hi ▸ hin) hw ht
  rwa [he, show indices.length = 8 from List.length_ofFn] at h

/-- The eight-word program is independent of the bit width and of all wire values. -/
def read {K : Type} (ports : Port → K) : FiniteRoutine K := (readList indices).onPorts ports

/-- Read an arbitrary successor field, including noncanonical encodings. The
same instruction count applies to every input with the public field lengths. -/
theorem read_runs {K : Type} [DecidableEq K] (ports : Port → K) (hp : Function.Injective ports)
    (s : Stacks K) (w : ℕ) (data : Fin 8 → List Bool) (suffix : List Bool)
    (hdata : ∀ i, (data i).length = w)
    (hin : s (ports .input) = (List.ofFn data).flatten ++ suffix)
    (hw : s (ports .width) = List.replicate w true) (ht : s (ports .tmp) = []) :
    (read ports).Runs (8*(6*w+2)+1) s (installStacks ports s (result (s ∘ ports) data suffix)) := by
  have run := (readList indices).runs_onPorts hp s
    (readEight_runs w data hdata (s ∘ ports) suffix hin hw ht)
  rwa [installStacks_eq hp s (s ∘ ports) (fun _ => rfl)] at run

/-- The physical input tape is the row-major concatenation of fixed-width fields. -/
theorem raw_eq_flatten {α : Type*} {k w : ℕ} (b : Fin (k * w) → α) :
    List.ofFn b = (List.ofFn fun i : Fin k =>
      List.ofFn fun j : Fin w => b (finProdFinEquiv (i, j))).flatten := by
  simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm w, Nat.add_comm] using List.ofFn_mul b

/-- Decoding the word array preserves every bit, including for malformed successor messages. -/
theorem raw_eq_flatten_words {k w : ℕ} (b : Fin (k * w) → Bool) :
    List.ofFn b = (List.ofFn fun i : Fin k =>
      BurstRAM.wordBits ((RAMSerialization.arrayBits k w).symm b i)).flatten := by
  rw [raw_eq_flatten]
  congr 1
  apply congrArg List.ofFn
  funext i
  unfold BurstRAM.wordBits
  apply congrArg List.ofFn
  funext j
  simpa only [Equiv.apply_symm_apply] using
    RAMSerialization.arrayBits_at ((RAMSerialization.arrayBits k w).symm b) i j

/-- Specialization to a successor wire in the serial transcript. -/
theorem read_raw_runs {K : Type} [DecidableEq K] (ports : Port → K) (hp : Function.Injective ports)
    (s : Stacks K) {w : ℕ} (bits : Fin (8*w) → Bool) (suffix : List Bool)
    (hin : s (ports .input) = List.ofFn bits ++ suffix)
    (hw : s (ports .width) = List.replicate w true) (ht : s (ports .tmp) = []) :
    (read ports).Runs (8*(6*w+2)+1) s (installStacks ports s (result (s ∘ ports)
      (fun i => BurstRAM.wordBits ((RAMSerialization.arrayBits 8 w).symm bits i)) suffix)) := by
  apply read_runs ports hp s w _ suffix (fun _ => BurstRAM.length_wordBits _)
  · rwa [← raw_eq_flatten_words]
  · exact hw
  · exact ht

open RAMLayout

/-- The incident stack exposes its send field, then its receive field, then
the unchanged sorting wires. This includes both zero-clamped boundary fields. -/
theorem incident_prefix {α : Type*} {d H w : ℕ} (inc : Fin (width d H w) → α) :
    List.ofFn inc =
      List.ofFn (fun j => inc (offset d H w (.inl (0, j)))) ++
      List.ofFn (fun j => inc (offset d H w (.inl (1, j)))) ++
      (List.ofFn inc).drop (16*w) := by
  let head := fun i : Fin (2*(8*w)) => inc (Fin.castAdd (layerCount d * (2*blockBits H w)) i)
  let tail := fun i : Fin (layerCount d * (2*blockBits H w)) => inc (Fin.natAdd (2*(8*w)) i)
  have hs : List.ofFn inc = List.ofFn head ++ List.ofFn tail := List.ofFn_add
  have hd : (List.ofFn inc).drop (16*w) = List.ofFn tail := by
    rw [hs, show 16*w = (List.ofFn head).length by simp [head]; omega, List.drop_left]
  rw [hd, hs, raw_eq_flatten head]
  simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

end RAMTape.SuccessorFields

end VPVNP
end Computability
end OAI
