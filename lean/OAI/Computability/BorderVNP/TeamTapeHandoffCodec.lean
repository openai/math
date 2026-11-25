import OAI.Computability.BorderVNP.TeamTapeHandoffFrame
import OAI.Computability.VPVNP.RAMTapeSuccessorFields
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-!
# Physical decoding and serialization of a team successor frame

The status occupies one bit. The finite register count fixes the field order
in the control table. A reusable unary width stack delimits each field, so the
same table handles every word width. Both routines leave the following link
data at the indicated suffix.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeHandoff.Codec

open VPVNP RAMTape BurstRAM

/-- Physical link, unary word width, scratch space, status and individual word stacks. -/
inductive Port (k : ℕ) where
  | wire | width | tmp | tag | field (i : Fin (k + 2))
  deriving DecidableEq, Fintype

variable {w k : ℕ}

private theorem words_length (f : Frame w k) : f.words.length = k + 2 := by
  cases f <;> simp [Frame.words]

/-- The word held on an individual field stack after decoding. -/
def fields (f : Frame w k) (i : Fin (k + 2)) : List Bool :=
  wordBits (f.words.get (Fin.cast (words_length f).symm i))

theorem fields_length (f : Frame w k) (i : Fin (k + 2)) : (fields f i).length = w :=
  length_wordBits _

theorem fields_flatten (f : Frame w k) :
    (List.ofFn (fields f)).flatten = f.words.flatMap wordBits := by
  have h := List.ofFn_congr (words_length f) (fun i => wordBits (f.words.get i))
  unfold fields
  rw [← h, List.ofFn_comp', List.ofFn_get, List.flatMap_def]

/-- The wire before decoding, with the unary width and empty destination stacks. -/
def incoming (k w : ℕ) (raw : List Bool) : Stacks (Port k)
  | .wire => raw
  | .width => List.replicate w true
  | _ => []

/-- Physical status and words of a frame, with subsequent wire bits ready to read. -/
def bank (f : Frame w k) (suffix : List Bool) : Stacks (Port k)
  | .wire => suffix
  | .width => List.replicate w true
  | .tmp => []
  | .tag => [f.halted]
  | .field i => fields f i

private def wordPorts (i : Fin (k + 2)) : SuccessorFields.WordPort → Port k
  | .input => .wire
  | .width => .width
  | .tmp => .tmp
  | .out => .field i

private theorem wordPorts_injective (i : Fin (k + 2)) : Function.Injective (wordPorts i) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

private def readWord (i : Fin (k + 2)) : FiniteRoutine (Port k) :=
  .ofStackCode SuccessorFields.wordCode (wordPorts i) .collect (fun q => decide (q = .done))

private theorem readWord_runs (i : Fin (k + 2)) (s : Stacks (Port k)) (data tail : List Bool)
    (hin : s .wire = data ++ tail) (hw : s .width = List.replicate data.length true)
    (ht : s .tmp = []) : (readWord i).Runs (6 * data.length + 2) s
      (Function.update (Function.update s .wire tail) (.field i) (data ++ s (.field i))) := by
  let small := s ∘ wordPorts i
  apply FiniteRoutine.runs_ofStackCode_framed (wordPorts_injective i)
    (src := SuccessorFields.wordCode) (normal := fun q => decide (q = .done))
    (entry := .collect) (exit := .done) rfl rfl
    (fun q h => by obtain rfl := of_decide_eq_true h; rfl)
    (SuccessorFields.word_runs small data tail hin hw ht) (fun _ => rfl)
  · intro j
    cases j <;> simp [wordPorts, small]
  · intro j hj
    have hi : j ≠ .wire := Ne.symm (hj .input)
    have ho : j ≠ .field i := Ne.symm (hj .out)
    simp [hi, ho]

private def readWords : List (Fin (k + 2)) → FiniteRoutine (Port k)
  | [] => .ret
  | i :: is => (readWord i).followedBy (readWords is)

private def afterRead (s : Stacks (Port k)) (data : Fin (k + 2) → List Bool)
    (is : List (Fin (k + 2))) (tail : List Bool) : Stacks (Port k)
  | .wire => tail
  | .field i => if i ∈ is then data i ++ s (.field i) else s (.field i)
  | p => s p

private theorem readWords_runs (data : Fin (k + 2) → List Bool) (hdata : ∀ i, (data i).length = w)
    (is : List (Fin (k + 2))) (hd : is.Nodup) (s : Stacks (Port k)) (tail : List Bool)
    (hin : s .wire = is.flatMap data ++ tail) (hw : s .width = List.replicate w true)
    (ht : s .tmp = []) :
    (readWords is).Runs (is.length * (6 * w + 2) + 1) s (afterRead s data is tail) := by
  induction is generalizing s with
  | nil =>
    have he : afterRead s data [] tail = s := by
      funext p
      cases p <;> simp_all [afterRead]
    rw [he, List.length_nil, Nat.zero_mul, Nat.zero_add]
    exact Routine.runs_ret s
  | cons i is ih =>
    let rest := is.flatMap data ++ tail
    let mid := Function.update (Function.update s .wire rest) (.field i) (data i ++ s (.field i))
    have first : (readWord i).Runs (6 * w + 2) s mid := by
      rw [← hdata i]
      exact readWord_runs i s (data i) rest (by simpa [rest, List.append_assoc] using hin)
        (by simpa [hdata] using hw) ht
    obtain ⟨hni, hdis⟩ := List.nodup_cons.mp hd
    have last := ih hdis mid (by simp [mid, rest])
      (by simpa [mid] using hw) (by simpa [mid] using ht)
    have he : afterRead mid data is tail = afterRead s data (i :: is) tail := by
      funext p
      cases p with
      | field j => by_cases hj : j = i <;> simp_all [afterRead, mid]
      | wire | tag | width | tmp => simp [afterRead, mid]
    rw [he] at last
    rw [List.length_cons, Nat.add_mul, Nat.one_mul,
      show is.length * (6 * w + 2) + (6 * w + 2) + 1 =
        (6 * w + 2) + (is.length * (6 * w + 2) + 1) by omega]
    exact first.followedBy last

private def readTag (k : ℕ) : FiniteRoutine (Port k) :=
  .ofRoutine (Routine.popCase .wire (Routine.halt false)
    (Routine.push .tag false) (Routine.push .tag true))

private theorem readTag_runs (b : Bool) (s : Stacks (Port k)) (tail : List Bool)
    (hin : s .wire = b :: tail) :
    (readTag k).Runs 2 s (Function.update (Function.update s .wire tail) .tag (b :: s .tag)) := by
  have push := Routine.runs_push (.tag : Port k) b (Function.update s .wire tail)
  simp only [Function.update_of_ne (show (Port.tag : Port k) ≠ .wire by simp)] at push
  cases b with
  | false => exact Routine.runs_popCase_false _ _ _ _ hin push
  | true => exact Routine.runs_popCase_true _ _ _ _ hin push

/-- Pop the status and then the fixed number of word fields. A missing tag or
premature end in a word reaches a rejecting halt. -/
def decode (k : ℕ) : FiniteRoutine (Port k) :=
  (readTag k).followedBy (readWords (List.finRange (k + 2)))

private theorem field_order (f : Frame w k) :
    (List.finRange (k + 2)).flatMap (fields f) = f.words.flatMap wordBits := by
  rw [List.flatMap_def, ← List.ofFn_eq_map, fields_flatten]

/-- Decode the actual checked link bits, including canonical zero PC and
registers for a halted predecessor. The width stack is restored even at width zero. -/
theorem decode_runs (f : Frame w k) (suffix : List Bool) :
    (decode k).Runs ((k + 2) * (6 * w + 2) + 3)
      (incoming k w (f.bits ++ suffix)) (bank f suffix) := by
  let raw := incoming k w (f.bits ++ suffix)
  let tail := f.words.flatMap wordBits ++ suffix
  let mid := Function.update (Function.update raw .wire tail) .tag [f.halted]
  have first : (readTag k).Runs 2 raw mid := readTag_runs f.halted raw tail rfl
  have last := readWords_runs (fields f) (fields_length f) (List.finRange (k + 2))
    (List.nodup_finRange _) mid suffix (by simp [mid, tail, field_order])
    (by simp [mid, raw, incoming]) (by simp [mid, raw, incoming])
  have he : afterRead mid (fields f) (List.finRange (k + 2)) suffix = bank f suffix := by
    funext p
    cases p <;> simp [afterRead, bank, mid, raw, incoming]
  rw [he, List.length_finRange] at last
  rw [show (k + 2) * (6 * w + 2) + 3 = 2 + ((k + 2) * (6 * w + 2) + 1) by omega]
  exact first.followedBy last

private def prependWords : List (Fin (k + 2)) → FiniteRoutine (Port k)
  | [] => .ret
  | i :: is => (prependWords is).followedBy (SuccessorFields.prependCopy (.field i) .wire .tmp)

private theorem prependWords_runs (is : List (Fin (k + 2))) (s : Stacks (Port k))
    (ht : s .tmp = []) (hw : ∀ i, (s (.field i)).length = w) :
    (prependWords is).Runs (is.length * (5 * w + 2) + 1) s
      (Function.update s .wire (is.flatMap (fun i => s (.field i)) ++ s .wire)) := by
  induction is with
  | nil =>
    simp only [prependWords, List.length_nil, Nat.zero_mul, Nat.zero_add, List.flatMap_nil,
      List.nil_append, Function.update_eq_self]
    exact Routine.runs_ret s
  | cons i is ih =>
    let tail := is.flatMap (fun j => s (.field j)) ++ s .wire
    let mid := Function.update s .wire tail
    have first : (prependWords is).Runs (is.length * (5 * w + 2) + 1) s mid := ih
    have last := SuccessorFields.prependCopy_runs (Port.field i) .wire .tmp
      (by simp) (by simp) (by simp) mid (by simpa [mid] using ht)
    simp only [mid, Function.update_of_ne (show Port.field i ≠ .wire by simp), hw,
      Function.update_self, Function.update_idem] at last
    rw [List.length_cons, Nat.add_mul, Nat.one_mul,
      show is.length * (5 * w + 2) + (5 * w + 2) + 1 =
        is.length * (5 * w + 2) + 1 + (5 * w + 2) by omega]
    simp only [List.flatMap_cons, List.append_assoc]
    exact first.followedBy last

/-- Restore each source field while serializing onto the outgoing link, then prepend the status. -/
def serialize (k : ℕ) : FiniteRoutine (Port k) :=
  (prependWords (List.finRange (k + 2))).followedBy (SuccessorFields.prependCopy .tag .wire .tmp)

/-- The outgoing wire contains the canonical successor frame followed by its original suffix. -/
theorem serialize_runs (f : Frame w k) (suffix : List Bool) :
    (serialize k).Runs ((k + 2) * (5 * w + 2) + 8) (bank f suffix)
      (Function.update (bank f suffix) .wire (f.bits ++ suffix)) := by
  let mid := Function.update (bank f suffix) .wire (f.words.flatMap wordBits ++ suffix)
  have first : (prependWords (List.finRange (k + 2))).Runs
      ((k + 2) * (5 * w + 2) + 1) (bank f suffix) mid := by
    simpa only [List.length_finRange, bank, field_order, mid] using
      prependWords_runs (List.finRange (k + 2)) (bank f suffix) rfl (fields_length f)
  have last := SuccessorFields.prependCopy_runs (Port.tag : Port k) .wire .tmp
    (by simp) (by simp) (by simp) mid (by simp [mid, bank])
  simpa [serialize, mid, bank, Frame.bits, Nat.add_assoc] using first.followedBy last

end TeamTapeHandoff.Codec

end BorderVNP
end Computability
end OAI
