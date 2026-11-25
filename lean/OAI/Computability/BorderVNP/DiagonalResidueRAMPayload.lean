import OAI.Computability.BorderVNP.DiagonalResidueRAMGather
import OAI.Computability.BorderVNP.DiagonalResidueRAMEvaluate
import OAI.Computability.BorderVNP.DiagonalTallyBitsPack

/-! # The finite payload of gate records, public operands, and query addresses -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM VPVNP.BooleanTranscript RoutingISA

variable {w u v k : ℕ}

/-- The six word operands consumed by the fixed entry evaluator. -/
def headerWords (w : ℕ) (d : Frame) : List (Word w) :=
  [word w d.gates,word w d.guesses,word w d.advice,word w d.base,word w d.output,word w d.query]

/-- The single packed literal payload: frame words, gate records, gather addresses. -/
def payload (w base start : ℕ) (c : Circuit (Fin u ⊕ Fin v) k) (src : Fin u → ℕ) : List (Word w) :=
  headerWords w (frame base (start+6) c) ++
    adviceData (List.ofFn (rows base c.program)) ++ List.ofFn (word w ∘ src)

/-- Literal length is independent of query values and private guesses. -/
theorem payload_length (base start : ℕ) (c : Circuit (Fin u ⊕ Fin v) k) (src : Fin u → ℕ) :
    (payload w base start c src).length = 6+3*k+u := by
  simp [payload,headerWords,adviceData_length]; omega

/-- All words are present in memory at successive addresses. -/
def Words (m : Memory w) (start : ℕ) (xs : List (Word w)) : Prop :=
  ∀ i : Fin xs.length, m (start+i.val) = xs[i.val]

/-- Split a contiguous word array at the known first-block length. -/
theorem Words.append {m : Memory w} {start : ℕ} {xs ys : List (Word w)}
    (h : Words m start (xs++ys)) : Words m start xs ∧ Words m (start+xs.length) ys := by
  constructor
  · intro i
    exact (h ⟨i.val,by simp; omega⟩).trans (List.getElem_append_left i.isLt)
  · intro i
    have hx := h ⟨xs.length+i.val, by simp⟩
    simpa [Nat.add_assoc,List.getElem_append_right] using hx

/-- The bit packing routine reproduces the original word array. -/
theorem words_after_pack (m : Memory w) (start : ℕ) (xs : List (Word w)) :
    Words (DiagonalTallyBits.outputMemory m start (xs.map BurstRAM.wordBits)) start xs := by
  intro i
  rw [DiagonalTallyBits.outputMemory_word m start _ i.val (by simp), List.getElem_map,
    TapeWord.value_wordBits]
  exact Fin.ext (word_val w _ xs[i.val].isLt)

/-- The advised words split into a valid six-word header, the circuit's
three-word records, and the address of each public bit. -/
theorem payload_parts {m : Memory w} {base start : ℕ} {c : Circuit (Fin u ⊕ Fin v) k}
    {src : Fin u → ℕ} (h : Words m start (payload w base start c src)) :
    Words m start (headerWords w (frame base (start+6) c)) ∧ hasAdvice m base (start+6) c ∧
      (∀ i, m (start+6+3*k+i.val) = word w (src i)) := by
  obtain ⟨h₁,hs⟩ := h.append
  obtain ⟨hh,hg⟩ := h₁.append
  refine ⟨hh,hg,?_⟩
  intro i
  have h' := hs ⟨i.val, by simp⟩
  simp [headerWords,adviceData_length] at h'
  convert h' using 2; omega

/-- The list of address/bit pairs is independent of private branch choices. -/
def pairs (src : Fin u → ℕ) (x : Fin u → Bool) : List (ℕ × Bool) :=
  List.ofFn (fun i => (src i,x i))

/-- Reconstruct the semantic source-list contract from real memory words. -/
theorem sourcesAt_of_words (m : Memory w) (ip : ℕ) (xs : List (ℕ × Bool))
    (ha : Words m ip (xs.map (word w ∘ Prod.fst)))
    (hb : ∀ t ∈ xs, t.1 < 2^w ∧ m t.1 = wordBit w t.2) : sourcesAt m ip xs := by
  induction xs generalizing ip with
  | nil => trivial
  | cons t ts ih =>
    obtain ⟨a,b⟩ := t
    have h₀ := ha ⟨0,by simp⟩
    have h := hb (a,b) (by simp)
    refine ⟨by simpa using h₀,h.1,h.2,ih (ip+1) ?_ (fun t ht => hb _ (by simp [ht]))⟩
    intro i
    have h' := ha ⟨i.val+1,by simpa using i.isLt⟩
    simpa [Nat.add_assoc,Nat.add_comm 1] using h'

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
