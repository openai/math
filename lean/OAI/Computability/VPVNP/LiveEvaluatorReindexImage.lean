import OAI.Computability.VPVNP.LiveEvaluatorReindex

/-!
# Memory invariant for the evaluator's exponent scatter

Each dense exponent bit has a distinct destination in the first tape. The
invariant describes exactly the visited payload slots and preserves every
other address. At completion the initial zero-exponent bank has become the
bank for the actual evaluator input in formal-coordinate order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorReindex

open LiveEvaluatorEncoding LiveEvaluatorInitialize EvaluatorProgramRawInput
open BurstRAM (Word Memory writeMemory)
open RAMSerialization
open scoped Fin.CommRing

variable {d t Z w : ℕ}

/-- Physical word address of an exponent payload symbol. -/
def symbolAddress (stateBase M adviceLength Z : ℕ) {T : ℕ} (q : Fin T) : ℕ :=
  stateBase + 1 + M + rawSlot adviceLength Z q

private theorem address_injective {base M A : ℕ} {T : ℕ} :
    Function.Injective (symbolAddress base M A Z (T := T)) := by
  intro i j he
  exact payload_injective (by simpa [symbolAddress, rawSlot] using he)

/-- Dense source `q` has been read if its position precedes the cursor. -/
structure Image (perm : Fin d ≃ Fin t) (dense : Fin d → Word Z)
    (base M adviceLength cursor : ℕ) (before after : Memory w) : Prop where
  copied : ∀ q : Fin (d*Z), q.val < cursor →
    after (symbolAddress base M adviceLength Z (bitOrder perm Z q)) =
      PrimedInputRAM.encodeBit w (arrayBits d Z dense q) + 1
  outside : ∀ addr, (∀ q : Fin (d*Z), q.val < cursor →
    addr ≠ symbolAddress base M adviceLength Z (bitOrder perm Z q)) → after addr = before addr

theorem Image.zero (perm : Fin d ≃ Fin t) (dense : Fin d → Word Z) (base M A : ℕ) (m : Memory w) :
    Image perm dense base M A 0 m m :=
  ⟨fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩

theorem Image.write {perm : Fin d ≃ Fin t} {dense : Fin d → Word Z} {base M A : ℕ}
    {before m : Memory w} (q : Fin (d*Z)) (h : Image perm dense base M A q.val before m)
    (addr : Word w) (ha : addr.val = symbolAddress base M A Z (bitOrder perm Z q)) :
    Image perm dense base M A (q.val+1) before
      (writeMemory m addr (PrimedInputRAM.encodeBit w (arrayBits d Z dense q) + 1)) := by
  constructor
  · intro q' hq'
    by_cases he : q' = q
    · subst q'
      simp [writeMemory, ha]
    · have hne : symbolAddress base M A Z (bitOrder perm Z q') ≠ addr.val := by
        rw [ha]
        exact fun eq => he ((bitOrder perm Z).injective (address_injective eq))
      rw [writeMemory, ite_eq_right hne, h.copied q' (by have h' : q'.val ≠ q.val := fun eq => he (Fin.ext eq); omega)]
  · intro a hn
    rw [writeMemory, ite_eq_right (ha ▸ hn q (by omega))]
    exact h.outside a (fun q' hq' => hn q' (by omega))

private theorem slot_lt (A : List Bool) (e : Fin t → Word Z) (q : Fin (t*Z)) :
    rawSlot A.length Z q < (A ++ runtime e).length := by
  have h := raw_at A e q
  by_contra! hn
  rw [List.getElem?_eq_none hn] at h
  contradiction

private theorem wordBit_symbol (hw : 2 ≤ w) (b : Bool) :
    (PrimedInputRAM.encodeBit w b + 1 : Word w).val = (bitSymbol b).val := by
  have h4 : 4 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  cases b <;> simp [PrimedInputRAM.encodeBit, bitSymbol, Fin.val_add,
    Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w), Nat.mod_eq_of_lt (by omega : 2 < 2 ^ w)]

/-- The completed scatter gives every word of the initialized evaluator on
the real exponent vector, including all unchanged advice, width tags, padding,
state and second-tape words. -/
theorem stores_formal (p : UniversalMachine.Program) (hr : p.extra ≠ 0)
    (hw : 2 ≤ w) (hs : p.extra + 2 ≤ 2 ^ w) (perm : Fin d ≃ Fin t)
    (dense : Fin d → Word Z) (formal : Fin t → Word Z) (order : ∀ i, formal (perm i) = dense i)
    (A : List Bool) (base M : ℕ) (space : (A ++ runtime formal).length ≤ M+1)
    (before after : Memory w) (prepared : Stores hw hs base before
      (LiveEvaluatorTail.initialCode M (UniversalMachine.initial p (A ++ runtime (fun _ : Fin t => (0 : Word Z))))))
    (finished : Image perm dense base M A.length (d*Z) before after) :
    Stores hw hs base after (LiveEvaluatorTail.initialCode M (UniversalMachine.initial p (A ++ runtime formal))) := by
  intro k
  apply Fin.ext
  rcases field_cases k with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [finished.outside _ (by intro q _; dsimp [stateField, symbolAddress]; omega),
      prepared (stateField M), words_state, words_state, initial_state, initial_state]
  · let addr := base + (firstField i).val
    by_cases hit : ∃ q, addr = symbolAddress base M A.length Z (bitOrder perm Z q)
    · obtain ⟨q, he⟩ := hit
      have hidx : i.val = M + rawSlot A.length Z (bitOrder perm Z q) := by
        dsimp [addr, firstField, symbolAddress] at he
        omega
      change (after addr).val = _
      rw [he, finished.copied _ q.isLt, wordBit_symbol hw, words_first, initial_first, ite_eq_right hr]
      simp [inputCell, hidx, raw_dense_at A perm dense formal order]
    · have hne (q : Fin (d*Z)) : addr ≠ symbolAddress base M A.length Z (bitOrder perm Z q) :=
        fun he => hit ⟨q, he⟩
      rw [finished.outside _ (fun q _ => hne q), prepared (firstField i), words_first, words_first,
        initial_first, initial_first, ite_eq_right hr, ite_eq_right hr]
      by_cases hi : i.val < M
      · simp [inputCell, hi]
      · have hout (f : Fin (t*Z)) : i.val - M ≠ rawSlot A.length Z f := by
          obtain ⟨q, rfl⟩ := (bitOrder perm Z).surjective f
          intro eq
          apply hne q
          dsimp [addr, firstField, symbolAddress]
          omega
        simp only [inputCell, hi, ite_false]
        rw [raw_else A _ formal _ hout]
  · rw [finished.outside _ (by
      intro q _
      have hlt := slot_lt A formal (bitOrder perm Z q)
      dsimp [secondField, symbolAddress]
      omega), prepared (secondField i), words_second, words_second, initial_second, initial_second]

end LiveEvaluatorReindex

end VPVNP
end Computability
end OAI
