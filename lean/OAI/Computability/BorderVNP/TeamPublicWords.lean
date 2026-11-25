import OAI.Computability.BorderVNP.TeamTapeInputEntry
import OAI.Computability.VPVNP.RAMTapeSuccessorFields
import OAI.Computability.VPVNP.RAMTapeISAPorts

/-! # Loading the fixed public operands from the team literal

Immediately after the length and initialization fields, the literal holds one logical
width-`w` word per public operand in increasing register order. A fixed finite parser
consumes exactly these bits, retaining the remainder for the subsequent routing and handoff
checks. These same bits already occur in the time-zero memory records.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPublicWords

open VPVNP VPVNP.RAMTape VPVNP.BurstRAM

/-- Input, logical width tally, scratch, and public register stacks. -/
inductive Port (k : ℕ) | input | width | tmp | pub (i : Fin k)
  deriving DecidableEq, Fintype

variable {k w : ℕ}

private def onePort (i : Fin k) : SuccessorFields.WordPort → Port k
  | .input => .input | .width => .width | .tmp => .tmp | .out => .pub i

private theorem inj (i : Fin k) : Function.Injective (onePort i) := by
  intro a b eq; cases a <;> cases b <;> first | rfl | cases eq

private def one (i : Fin k) : FiniteRoutine (Port k) :=
  FiniteRoutine.ofStackCode SuccessorFields.wordCode (onePort i) .collect (fun q => decide (q = .done))

private theorem one_runs (i : Fin k) (s : Stacks (Port k)) (xs rest : List Bool)
    (hi : s .input = xs ++ rest) (hw : s .width = List.replicate xs.length true) (ht : s .tmp = []) :
    (one i).Runs (6*xs.length+2) s (Function.update (Function.update s .input rest) (.pub i) (xs ++ s (.pub i))) := by
  let small := s ∘ onePort i
  unfold one
  apply FiniteRoutine.runs_ofStackCode_framed (src := SuccessorFields.wordCode) (s := s) (inj i) (normal := fun q : SuccessorFields.Phase => decide (q = .done))
    (entry := .collect) (exit := .done) rfl rfl (fun q h => by have := of_decide_eq_true h; subst q; rfl)
    (SuccessorFields.word_runs small xs rest hi hw ht) (fun _ => rfl)
  · intro j; cases j <;> simp [small, onePort]
  · intro j hj
    have h1 := Ne.symm (hj .out)
    have h2 := Ne.symm (hj .input)
    change j ≠ Port.pub i at h1
    change j ≠ Port.input at h2
    simp [h1, h2]

private def read : List (Fin k) → FiniteRoutine (Port k)
  | [] => .ret
  | i :: is => (one i).followedBy (read is)

private def loaded (s : Stacks (Port k)) (is : List (Fin k)) (pub : Fin k → Word w) (tail : List Bool) : Stacks (Port k)
  | .input => tail
  | .pub i => if i ∈ is then wordBits (pub i) ++ s (.pub i) else s (.pub i)
  | p => s p

private theorem read_runs (s : Stacks (Port k)) (is : List (Fin k)) (hd : is.Nodup) (pub : Fin k → Word w)
    (tail : List Bool) (hin : s .input = is.flatMap (wordBits ∘ pub) ++ tail)
    (hw : s .width = List.replicate w true) (ht : s .tmp = []) :
    (read is).Runs (is.length*(6*w+2)+1) s (loaded s is pub tail) := by
  induction is generalizing s with
  | nil =>
    have hl : loaded s [] pub tail = s := by funext p; cases p <;> simp_all [loaded]
    rw [hl, List.length_nil, Nat.zero_mul, Nat.zero_add]; exact Routine.runs_ret s
  | cons i is ih =>
    let rest := is.flatMap (wordBits ∘ pub) ++ tail
    let mid := Function.update (Function.update s .input rest) (.pub i) (wordBits (pub i) ++ s (.pub i))
    have step : (one i).Runs (6*w+2) s mid := by
      simpa only [length_wordBits] using one_runs i s (wordBits (pub i)) rest
        (by simpa only [List.flatMap_cons, List.append_assoc, Function.comp_apply, rest] using hin)
        (by simpa using hw) ht
    have next := ih mid hd.of_cons (by simp [mid, rest]) (by simpa [mid] using hw) (by simpa [mid] using ht)
    have hl : loaded mid is pub tail = loaded s (i :: is) pub tail := by
      funext p
      cases p with
      | pub j => by_cases e : j = i <;> simp [loaded, mid, e, hd.notMem]
      | input | width | tmp => simp [loaded, mid]
    rw [hl] at next
    simpa only [read, List.length_cons, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using step.followedBy next

/-- Fixed table for the `k` public register operands of a RAM template. -/
def program (k : ℕ) : FiniteRoutine (Port k) := read (List.finRange k)

/-- Actual public-word bytes embedded in the processor literal. -/
def bytes (pub : Fin k → Word w) : List Bool := (List.finRange k).flatMap (wordBits ∘ pub)

theorem bytes_length (pub : Fin k → Word w) : (bytes pub).length = k*w := by
  simp [bytes, List.length_flatMap, List.map_const', Function.comp_def]

/-- The decoder fills all initially empty public registers with the literal word values. -/
theorem runs (s : Stacks (Port k)) (pub : Fin k → Word w) (tail : List Bool)
    (hin : s .input = bytes pub ++ tail) (hw : s .width = List.replicate w true) (ht : s .tmp = [])
    (empty : ∀ i, s (.pub i) = []) :
    let out : Stacks (Port k) := fun | .input => tail | .pub i => wordBits (pub i) | p => s p
    (program k).Runs (k*(6*w+2)+1) s out := by
  have h := read_runs s (List.finRange k) (List.nodup_finRange k) pub tail hin hw ht
  have eq : loaded s (List.finRange k) pub tail = _ := show _ =
    (fun | .input => tail | .pub i => wordBits (pub i) | p => s p) from by
      funext p; cases p <;> simp [loaded, empty]
  simpa only [program, List.length_finRange, eq] using h

end TeamPublicWords

end BorderVNP
end Computability
end OAI
