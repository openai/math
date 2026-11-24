import OAI.Computability.VPVNP.LiveHeaderRuns
import OAI.Computability.VPVNP.LiveHeaderFields

/-!
# Native payload scans of the incident cuts

Each completed field scan copies exactly the specified interval to the
designated buffer. Every word outside that buffer still has its input value.
Source intervals refer to the original packed processor headers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- The prefix written to scratch, together with a frame for all other cells. -/
structure FieldCopy (original : Memory w) (slot : Fin 4) (src dst cursor : ℕ) (m : Memory w) : Prop where
  copied : ∀ j < cursor, m (dst+j) = PrimedInputRAM.encodeBit w ((original (src+j)).val.testBit slot.val)
  frame : ∀ a, a < dst ∨ dst+cursor ≤ a → m a = original a

theorem FieldCopy.initial (original : Memory w) (slot : Fin 4) (src dst : ℕ) :
    FieldCopy original slot src dst 0 original := ⟨by simp, fun _ _ => rfl⟩

private theorem word_val_add (a b : Word w) (h : a.val + b.val < 2 ^ w) :
    (a+b).val = a.val+b.val := by rw [Fin.val_add, Nat.mod_eq_of_lt h]

private theorem cursor_sub (pub : Fin 3 → Word w) (j : ℕ) :
    (((pub 0).val + j : ℕ) : Word w) - pub 0 = (j : Word w) := by
  rw [Nat.cast_add, Fin.cast_val_eq_self, add_sub_cancel_left]

/-- A fixed, fifteen-instruction table copies every bit of the occupied source
field and preserves all memory outside the destination. Each step has three
probes. Empty fields have the empty execution and leave all cells intact. -/
theorem copy_field_native (hw : 4 ≤ w) (slot : Fin 4) (pub : Fin 3 → Word w)
    (original : Memory w) (len : ℕ) (hsrc : (original (pub 1).val).val + len ≤ (pub 2).val)
    (hdesc : (pub 1).val < (pub 2).val ∨ (pub 2).val + len ≤ (pub 1).val)
    (hfit : (pub 2).val + len ≤ 2 ^ w) :
    let P := ((template (copyFieldCell slot) 7).instantiate w pub).program
    ∃ rs, runSegment P 16 (some (pub 0)) original (List.replicate len []) = some rs ∧
      endState (some (pub 0)) rs = some (pub 0 + (len : Word w)) ∧
      FieldCopy original slot (original (pub 1).val).val (pub 2).val len
        (after original (eventLog rs)) ∧ rs.length = len ∧ ∀ x ∈ rs, countProbes x.events ≤ 3 := by
  let P := ((template (copyFieldCell slot) 7).instantiate w pub).program
  let src := (original (pub 1).val).val
  let dst := (pub 2).val
  let inv := FieldCopy original slot src dst
  have hi := FieldCopy.initial original slot src dst
  have step (j : ℕ) (hj : j < len) (m : Memory w) (h : inv j m) : ∃ es,
      execute P 16 (P.start (((pub 0).val+j : ℕ) : Word w)) m [] =
        some ⟨es, some (((pub 0).val+(j+1) : ℕ) : Word w)⟩ ∧
      inv (j+1) (after m es) ∧ countProbes es ≤ 3 := by
    let state : Word w := ((pub 0).val + j : ℕ)
    have hΔ : state - pub 0 = (j : Word w) := cursor_sub pub j
    have hjval : (j : Word w).val = j := (Fin.val_natCast ..).trans (Nat.mod_eq_of_lt (by omega))
    have hd : (pub 2 + (state - pub 0)).val = dst+j := by
      rw [hΔ, word_val_add _ _ (by rw [hjval]; omega), hjval]
    have hreadDesc := h.frame (pub 1).val (hdesc.imp_right (by dsimp [dst]; omega))
    have hs : (sourceSite pub state m).val = src+j := by
      simp only [sourceSite, hΔ, hreadDesc]
      rw [word_val_add _ _ (by rw [hjval]; omega), hjval]
    have hbefore : src+j < dst := by dsimp [src,dst]; omega
    have hreadSite := h.frame (src+j) (Or.inl hbefore)
    obtain ⟨es, rs, ht, hr, _, hp, _⟩ := copyFieldCell_trace hw slot pub state (fun _ => 0) m
    refine ⟨es, ?_, ?_, hp.le⟩
    · change execute ((template (copyFieldCell slot) 7).instantiate w pub).program
        (1 + (copyFieldCell slot).length) ⟨_,state,fun _ => 0,fun _ => 0⟩ m [] = _
      rw [execute_template, run_eq_trace, ht]
      simp [hr,state,add_assoc]
    · rw [trace_after ht,hs,hreadSite]
      constructor
      · intro k hk
        simp only [writeMemory,hd]
        by_cases he : k = j
        · simp [he]
        · simp [he,h.copied k (by omega)]
      · intro a ha
        have hne : a ≠ dst+j := by omega
        simp [writeMemory,hd,hne,h.frame a (by omega)]
  simpa only [Nat.cast_add, Fin.cast_val_eq_self] using
    run_cursor_segment_at P (pub 0).val 16 len 3 inv original hi step

/-- The guard reads two words and returns the next cursor precisely on a zero
bit. Its successful trace leaves memory untouched. -/
theorem padding_step (hw : 4 ≤ w) (slot : Fin 4) (pub : Fin 3 → Word w) (s : Word w) (m : Memory w) :
    let P := ((template (checkPaddingCell slot) 7).instantiate w pub).program
    if (m (sourceSite pub s m).val).val.testBit slot.val then
      execute P 15 (P.start s) m [] = none
    else ∃ es, execute P 15 (P.start s) m [] = some ⟨es, some (s+1)⟩ ∧ after m es = m ∧
      countProbes es = 2 := by
  dsimp only
  change (if _ then execute ((template (checkPaddingCell slot) 7).instantiate w pub).program (1 + (checkPaddingCell slot).length) ⟨_,s,fun _ => 0,fun _ => 0⟩ m [] = _
    else ∃ es, execute ((template (checkPaddingCell slot) 7).instantiate w pub).program (1 + (checkPaddingCell slot).length) ⟨_,s,fun _ => 0,fun _ => 0⟩ m [] = _ ∧ _)
  have ht := checkPaddingCell_trace hw slot pub s (fun _ => 0) m
  split_ifs with hb
  · simp only [hb,↓reduceIte] at ht
    rw [execute_template,run_eq_trace,ht]
    rfl
  · simp only [hb] at ht
    obtain ⟨es, rs, ht, hr, _, hp, _⟩ := ht
    refine ⟨es, ?_, trace_after ht, hp⟩
    rw [execute_template,run_eq_trace,ht]
    simp [hr]

/-- On arbitrary cut input, the full padding scan succeeds exactly if every
padding bit is zero. It touches only the specified interval, even on malformed input. -/
theorem padding_native_iff (hw : 4 ≤ w) (slot : Fin 4) (pub : Fin 3 → Word w) (m : Memory w)
    (len : ℕ) (hfit : (m (pub 1).val).val + len ≤ 2 ^ w) :
    let P := ((template (checkPaddingCell slot) 7).instantiate w pub).program
    (runSegment P 15 (some (pub 0)) m (List.replicate len [])).isSome = true ↔
      ∀ j < len, (m ((m (pub 1).val).val+j)).val.testBit slot.val = false := by
  let P := ((template (checkPaddingCell slot) 7).instantiate w pub).program
  have go (n k : ℕ) (hkn : k+n ≤ len) :
      (runSegment P 15 (some (pub 0 + (k : Word w))) m (List.replicate n [])).isSome = true ↔
        ∀ j, k ≤ j → j < k+n → (m ((m (pub 1).val).val+j)).val.testBit slot.val = false := by
    induction n generalizing k with
    | zero => simp [runSegment]; intro j hj hlt; omega
    | succ n ih =>
      have hk : k < len := by omega
      have hkval : (k : Word w).val = k := Fin.val_cast_of_lt (by omega)
      let s := pub 0 + (k : Word w)
      have hs : (sourceSite pub s m).val = (m (pub 1).val).val+k := by
        dsimp [s,sourceSite]
        rw [add_sub_cancel_left, word_val_add _ _ (by rw [hkval]; omega), hkval]
      have ht := padding_step hw slot pub s m
      dsimp only at ht
      rw [hs] at ht
      cases hbit : (m ((m (pub 1).val).val+k)).val.testBit slot.val with
      | true =>
        simp only [hbit,↓reduceIte] at ht
        rw [List.replicate_succ,runSegment]
        change (match execute P 15 (P.start s) m [] with
          | none => none
          | some r => (runSegment P 15 r.result (after m r.events) (List.replicate n [])).map (r :: ·)).isSome = true ↔ _
        rw [ht]
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
        exact fun hn => Bool.noConfusion ((hn k le_rfl (by omega)).symm.trans hbit)
      | false =>
        simp only [hbit,Bool.false_eq_true,↓reduceIte] at ht
        obtain ⟨es, he, hm, _⟩ := ht
        rw [List.replicate_succ,runSegment]
        change (match execute P 15 (P.start s) m [] with
          | none => none
          | some r => (runSegment P 15 r.result (after m r.events) (List.replicate n [])).map (r :: ·)).isSome = true ↔ _
        rw [he]
        simp only [hm,Option.isSome_map]
        have hnext : s+1 = pub 0 + ((k+1 : ℕ) : Word w) := by simp [s,add_assoc]
        rw [hnext,ih (k+1) (by omega)]
        constructor
        · intro hn j hj hlt
          rcases eq_or_lt_of_le hj with heq | hlt'
          · simpa [← heq] using hbit
          · exact hn j (by omega) (by omega)
        · intro hn j hj hlt
          exact hn j (by omega) (by omega)
  simpa using go len 0 (by simp)

/-- Every successful padding call has precisely two probes, and its entire
segment preserves every cell. -/
theorem padding_native (hw : 4 ≤ w) (slot : Fin 4) (pub : Fin 3 → Word w) (m : Memory w)
    (len : ℕ) (hfit : (m (pub 1).val).val + len ≤ 2 ^ w)
    (hz : ∀ j < len, (m ((m (pub 1).val).val+j)).val.testBit slot.val = false) :
    let P := ((template (checkPaddingCell slot) 7).instantiate w pub).program
    ∃ rs, runSegment P 15 (some (pub 0)) m (List.replicate len []) = some rs ∧
      endState (some (pub 0)) rs = some (pub 0 + (len : Word w)) ∧ after m (eventLog rs) = m ∧
      rs.length = len ∧ ∀ x ∈ rs, countProbes x.events ≤ 2 := by
  let P := ((template (checkPaddingCell slot) 7).instantiate w pub).program
  have h := run_cursor_segment_at P (pub 0).val 15 len 2 (fun _ mem => mem = m) m rfl
  apply (by simpa only [Nat.cast_add,Fin.cast_val_eq_self] using h)
  intro j hj mem hm
  subst mem
  let s : Word w := ((pub 0).val+j : ℕ)
  have hs : (sourceSite pub s m).val = (m (pub 1).val).val+j := by
    have hjval : (j : Word w).val = j := Fin.val_cast_of_lt (by omega)
    rw [sourceSite,cursor_sub,word_val_add _ _ (by rw [hjval]; omega),hjval]
  have ht := padding_step hw slot pub s m
  simp only [hs,hz j hj,Bool.false_eq_true,↓reduceIte] at ht
  obtain ⟨es, he, hm, hp⟩ := ht
  exact ⟨es, by simpa [s,P,add_assoc] using he, hm, hp.le⟩

end LiveHeader

end VPVNP
end Computability
end OAI
