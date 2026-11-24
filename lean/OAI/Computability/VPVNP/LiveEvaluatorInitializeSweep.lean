import OAI.Computability.VPVNP.LiveEvaluatorInitialize
import OAI.Computability.VPVNP.LiveHeaderRuns

/-!
# Complete native scan of the evaluator's initial tape

The initialized state bank occupies consecutive words for the control and
both tapes. A state write is followed by one native burst per input bit on a
running evaluator. An initially halted evaluator and the final accepting
endpoint each use a single state write.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorInitialize

open UniversalMachine (Program)
open LiveEvaluatorEncoding
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Number of input bits to copy into the initial tape, zero for an evaluator that starts
halted. -/
def activeLength (p : Program) (raw : UniversalMachine.Word) : ℕ :=
  if p.extra = 0 then 0 else raw.length

/-- The initial control word, one for an initially accepting evaluator and two for its first
running state. -/
def controlTag (p : Program) : Word 2 := if p.extra = 0 then 1 else 2

/-- A complete word image of the code in the contiguous memory region. -/
def Stores {extra M : ℕ} (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w) (base : ℕ)
    (m : Memory w) (c : Code extra M) : Prop :=
  ∀ k : Fin (fieldWords M), m (base + k.val) = words hw hs c k

/-- Each configuration word is the control field or one indexed tape symbol. -/
theorem field_cases {M : ℕ} (k : Fin (fieldWords M)) :
    k = stateField M ∨ (∃ i, k = firstField i) ∨ (∃ i, k = secondField i) := by
  have hk := k.isLt
  unfold fieldWords at hk
  by_cases h₀ : k.val = 0
  · exact Or.inl (Fin.ext h₀)
  by_cases h₁ : k.val < 1 + (2 * M + 1)
  · exact Or.inr (Or.inl ⟨⟨k.val - 1, by omega⟩, Fin.ext (by dsimp [firstField]; omega)⟩)
  · exact Or.inr (Or.inr ⟨⟨k.val - (1 + (2 * M + 1)), by omega⟩,
      Fin.ext (by dsimp [secondField]; omega)⟩)

/-- The natural address of the head cell of the first tape, where copying the initial input
begins. -/
def firstData (pub : Fin 4 → Word w) : ℕ := (pub 1).val + 1 + (pub 0).val

/-- Precisely the first `cursor` symbols have been written. -/
structure Copied (raw : UniversalMachine.Word) (base cursor : ℕ) (original m : Memory w) : Prop where
  symbols : ∀ j < cursor, m (base + j) = PrimedInputRAM.encodeBit w (raw[j]?.getD false) + 1
  outside : ∀ a, a < base ∨ base + cursor ≤ a → m a = original a

private theorem word_add_val (a b : Word w) (h : a.val + b.val < 2 ^ w) :
    (a + b).val = a.val + b.val := by rw [Fin.val_add, Nat.mod_eq_of_lt h]

/-- The native run over every input bit, including the empty run when
the evaluator starts in its accepting state. The source words may be on
either side of the writable input interval. -/
theorem copy_segment (hw : 2 ≤ w) (pub : Fin 4 → Word w) (width : (pub 3).val = w)
    (p : Program) (raw : UniversalMachine.Word) (original : Memory w)
    (fit : firstData pub + activeLength p raw ≤ 2 ^ w)
    (packed : ∀ j < activeLength p raw,
      original (sourceAddress pub (j : Word w)).val = inputWord w raw (j / w))
    (disjoint : ∀ j < activeLength p raw, (sourceAddress pub (j : Word w)).val < firstData pub ∨
      firstData pub + activeLength p raw ≤ (sourceAddress pub (j : Word w)).val) :
    let P := ((template copyBit 29).instantiate w pub).program
    ∃ reports, runSegment P 19 (some 0) original (List.replicate (activeLength p raw) []) = some reports ∧
      endState (some 0) reports = some (activeLength p raw : Word w) ∧
      Copied raw (firstData pub) (activeLength p raw) original (after original (eventLog reports)) ∧
      reports.length = activeLength p raw ∧ ∀ r ∈ reports, countProbes r.events ≤ 2 := by
  apply LiveHeader.run_cursor_segment _ 19 _ 2 (fun n => Copied raw (firstData pub) n original) original
  · exact ⟨fun _ hj => (Nat.not_lt_zero _ hj).elim, fun _ _ => rfl⟩
  intro j hj m h
  have hval : (j : Word w).val = j := Fin.val_cast_of_lt (by omega)
  have hraw : j < raw.length := by unfold activeLength at hj; split at hj <;> omega
  have hread := h.outside _ ((disjoint j hj).imp_right fun ha => by omega)
  have hadd := fit
  unfold firstData at hadd
  have hOne : (1 : Word w).val = 1 := by simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega : w ≠ 0))]
  have haddr : (targetAddress pub (j : Word w)).val = firstData pub + j := by
    unfold targetAddress firstData
    have h₁ := word_add_val (pub 1) 1 (by rw [hOne]; omega)
    have h₂ := word_add_val (pub 1 + 1) (pub 0) (by rw [h₁, hOne]; omega)
    rw [word_add_val _ _ (by rw [h₂, h₁, hOne, hval]; omega), h₂, h₁, hOne, hval]
  obtain ⟨es, he, hm, _, hp, _⟩ := copyBit_native hw pub width (j : Word w) m raw
    (by rw [hval]; exact hraw) (by rw [hread, packed j hj, hval])
  refine ⟨es, by simpa only [Nat.cast_add, Nat.cast_one] using he, ?_, hp.le⟩
  rw [hm]
  constructor
  · intro i hi
    by_cases hij : i = j
    · subst i
      simp [writeMemory, haddr, hval, List.getElem?_eq_getElem hraw]
    · simp [writeMemory, haddr, hij, h.symbols i (by omega)]
  · intro a ha
    have hn : a ≠ firstData pub + j := by omega
    simp [writeMemory, haddr, hn, h.outside a (by omega)]

private theorem encodeBit_add_one (hw : 2 ≤ w) (b : Bool) :
    (PrimedInputRAM.encodeBit w b + 1 : Word w).val = (bitSymbol b).val := by
  have h4 : 4 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  cases b <;> simp [PrimedInputRAM.encodeBit, bitSymbol, Fin.val_add,
    Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w), Nat.mod_eq_of_lt (by omega : 2 < 2 ^ w)]

private theorem tagWord_val (hw : 2 ≤ w) (tag : Word 2) : (Fin.ofNat (2 ^ w) tag.val).val = tag.val :=
  (Fin.val_ofNat ..).trans (Nat.mod_eq_of_lt (tag.isLt.trans_le (Nat.pow_le_pow_right (by decide) hw)))

/-- After the last burst the entire two-tape bank is the canonical initial
code. The untouched left side, second tape, and right padding use zero-default
memory. An empty program has only its state word. -/
theorem copied_stores (hw : 2 ≤ w) (pub : Fin 4 → Word w) (p : Program)
    (hs : p.extra + 2 ≤ 2 ^ w) (raw : UniversalMachine.Word) (blank m : Memory w)
    (space : raw.length ≤ (pub 0).val + 1)
    (zero : ∀ k : Fin (fieldWords (pub 0).val), blank ((pub 1).val + k.val) = 0)
    (h : Copied raw (firstData pub) (activeLength p raw)
      (writeMemory blank (pub 1) (Fin.ofNat _ (controlTag p).val)) m) :
    Stores hw hs (pub 1).val m (LiveEvaluatorTail.initialCode (pub 0).val (UniversalMachine.initial p raw)) := by
  intro k
  apply Fin.ext
  rcases field_cases k with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [words_state, initial_state]
    simp only [stateField, Nat.add_zero]
    rw [h.outside _ (Or.inl (by dsimp [firstData]; omega))]
    rw [writeMemory, ite_eq_left rfl, tagWord_val hw]
    split <;> simp_all [controlTag]
  · rw [words_first, initial_first]
    let M := (pub 0).val
    let addr := (pub 1).val + (firstField i).val
    have ha : addr = (pub 1).val + (1 + i.val) := rfl
    change (m addr).val = _
    by_cases active : p.extra ≠ 0 ∧ M ≤ i.val ∧ i.val - M < raw.length
    · obtain ⟨he, hi, hj⟩ := active
      have eq : addr = firstData pub + (i.val - M) := by dsimp [firstData, M] at *; omega
      rw [eq, h.symbols _ (by simpa [activeLength, he]), encodeBit_add_one hw, ite_eq_right he]
      simp [inputCell, M, Nat.not_lt_of_ge hi, List.getElem?_eq_getElem hj]
    · have outside : addr < firstData pub ∨ firstData pub + activeLength p raw ≤ addr := by
        dsimp [firstData, activeLength, M] at *
        split <;> omega
      have ha' : addr ≠ (pub 1).val := by omega
      rw [h.outside _ outside, writeMemory, ite_eq_right ha', zero (firstField i)]
      by_cases he : p.extra = 0
      · simp [he]
      · by_cases hi : i.val < M
        · simp [he, inputCell, hi, M] at *
        · have hj : raw.length ≤ i.val - M := by omega
          simp [he, inputCell, M, List.getElem?_eq_none (by exact hj)]
  · rw [words_second, initial_second]
    have hoff : firstData pub + activeLength p raw ≤ (pub 1).val + (secondField i).val := by
      simp only [firstData, activeLength, secondField]
      split <;> omega
    have hne : (pub 1).val + (secondField i).val ≠ (pub 1).val := by dsimp [secondField]; omega
    rw [h.outside _ (Or.inr hoff), writeMemory, ite_eq_right hne, zero (secondField i)]
    rfl

/-- At the last group the outgoing scratch bank is the accepting sentinel.
Only one control word is written. There is no outgoing physical cut. -/
theorem final_stores {extra M : ℕ} (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w)
    (base : Word w) (blank : Memory w)
    (zero : ∀ k : Fin (fieldWords M), blank (base.val + k.val) = 0) :
    Stores hw hs base.val (writeMemory blank base 1) (.accepted : Code extra M) := by
  intro k
  apply Fin.ext
  rcases field_cases k with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [words_state]
    simp [writeMemory, stateField, Code.stateWord,
      Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega : w ≠ 0))]
  · rw [words_first, writeMemory, ite_eq_right (by dsimp [firstField]; omega), zero (firstField i)]
    rfl
  · rw [words_second, writeMemory, ite_eq_right (by dsimp [secondField]; omega), zero (secondField i)]
    rfl

/-- The control-write call and all input-bit calls together prepare the actual
initial evaluator bank. The packed input buffer must survive the control write
and lie outside the writable tape interval. -/
theorem prepare_native (hw : 2 ≤ w) (pub : Fin 4 → Word w) (width : (pub 3).val = w)
    (p : Program) (hs : p.extra + 2 ≤ 2 ^ w) (raw : UniversalMachine.Word) (blank : Memory w)
    (space : raw.length ≤ (pub 0).val + 1)
    (fit : firstData pub + activeLength p raw ≤ 2 ^ w)
    (zero : ∀ k : Fin (fieldWords (pub 0).val), blank ((pub 1).val + k.val) = 0)
    (packed : ∀ j < activeLength p raw, blank (sourceAddress pub (j : Word w)).val = inputWord w raw (j / w))
    (disjoint : ∀ j < activeLength p raw, let a := (sourceAddress pub (j : Word w)).val
      a ≠ (pub 1).val ∧ (a < firstData pub ∨ firstData pub + activeLength p raw ≤ a)) :
    let tag := controlTag p
    let S := ((template (putState tag) 29).instantiate w pub).program
    let P := ((template copyBit 29).instantiate w pub).program
    ∃ es reports, execute S 5 (S.start 0) blank [] = some ⟨es, some 0⟩ ∧
      runSegment P 19 (some 0) (after blank es) (List.replicate (activeLength p raw) []) = some reports ∧
      endState (some 0) reports = some (activeLength p raw : Word w) ∧
      Stores hw hs (pub 1).val (after (after blank es) (eventLog reports))
        (LiveEvaluatorTail.initialCode (pub 0).val (UniversalMachine.initial p raw)) ∧
      es.length = 4 ∧ countProbes es = 1 ∧ choiceBits es = [] ∧
      reports.length = activeLength p raw ∧ ∀ r ∈ reports, countProbes r.events ≤ 2 := by
  obtain ⟨es, he, hm, hel, hep, heb⟩ := putState_native pub 0 blank (controlTag p)
  have saved (j : ℕ) (hj : j < activeLength p raw) : after blank es (sourceAddress pub (j : Word w)).val = inputWord w raw (j / w) := by
    rw [hm, writeMemory, ite_eq_right (disjoint j hj).1, packed j hj]
  obtain ⟨reports, hr, hend, hcopy, hlen, hprobes⟩ := copy_segment hw pub width p raw
    (after blank es) fit saved (fun j hj => (disjoint j hj).2)
  refine ⟨es, reports, he, hr, hend, ?_, hel, hep, heb, hlen, hprobes⟩
  apply copied_stores hw pub p hs raw blank _ space zero
  rw [hm] at hcopy ⊢
  exact hcopy

/-- The last tail group compares against a native-prepared canonical accept
bank without receiving an outgoing cut from a nonexistent neighbor. -/
theorem final_native {extra M : ℕ} (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w)
    (pub : Fin 4 → Word w) (pos : Word w) (blank : Memory w)
    (zero : ∀ k : Fin (fieldWords M), blank ((pub 1).val + k.val) = 0) :
    let S := ((template (putState 1) 29).instantiate w pub).program
    ∃ es, execute S 5 (S.start pos) blank [] = some ⟨es, some pos⟩ ∧
      Stores hw hs (pub 1).val (after blank es) (.accepted : Code extra M) ∧
      es.length = 4 ∧ countProbes es = 1 ∧ choiceBits es = [] := by
  obtain ⟨es, he, hm, hl, hp, hb⟩ := putState_native pub pos blank 1
  refine ⟨es, he, ?_, hl, hp, hb⟩
  rw [hm]
  exact final_stores hw hs (pub 1) blank zero

end LiveEvaluatorInitialize

end VPVNP
end Computability
end OAI
