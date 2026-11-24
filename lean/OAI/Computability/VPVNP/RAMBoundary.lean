import OAI.Computability.VPVNP.RAMMemory
import Mathlib.Data.List.OfFn

/-!
# Last-record fields in the distributed RAM transcript

In Lemma 10.1 each interior successor link carries the final physical slot of its
source's sorted block. The receiving validator uses this slot as the predecessor
of its first record. Flattening the blocks gives precisely the same read checks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMBoundary

open RAMMemory

variable {S B : ℕ} {Word : Type*}

/-- Each interior successor edge has one shared last-record field. -/
abbrev Sends (S : ℕ) (Word : Type*) := Fin (S - 1) → Option (Record Word)

/-- Physical slots in site-major order. -/
def flat (blocks : Fin S → Fin B → Option (Record Word)) : List (Option (Record Word)) :=
  (List.ofFn fun v ↦ List.ofFn (blocks v)).flatten

/-- Last slot of a nonempty block, including its padding if present. -/
def lastSlot (hB : 0 < B) (block : Fin B → Option (Record Word)) : Option (Record Word) :=
  block ⟨B - 1, by omega⟩

/-- The fields prescribed by the final sorted blocks. -/
def actual (hB : 0 < B) (blocks : Fin S → Fin B → Option (Record Word)) : Sends S Word :=
  fun i ↦ lastSlot hB (blocks ⟨i.val, by have := i.isLt; omega⟩)

/-- The physical send at the final site is clamped. -/
def outgoing (sent : Sends S Word) (v : Fin S) : Option (Record Word) :=
  if h : v.val + 1 < S then sent ⟨v.val, by omega⟩ else none

private def receiveFrom (initial : Option (Record Word)) (sent : Sends S Word) :
    Fin S → Option (Record Word)
  | ⟨0, _⟩ => initial
  | ⟨i + 1, _⟩ => sent ⟨i, by omega⟩

/-- An incoming field is the preceding site's shared send. The first receive
has the clamped value, so a read with no preceding write must return zero. -/
def receive (sent : Sends S Word) (v : Fin S) : Option (Record Word) :=
  receiveFrom none sent v

@[simp] theorem receive_first (sent : Sends (S + 1) Word) : receive sent 0 = none := rfl

@[simp] theorem outgoing_last (sent : Sends (S + 1) Word) :
    outgoing sent (Fin.last S) = none := by simp [outgoing]

theorem receive_succ (sent : Sends (S + 1) Word) (v : Fin S) :
    receive sent v.succ = outgoing sent v.castSucc := by
  simp only [outgoing, Fin.val_castSucc, Nat.add_lt_add_iff_right, v.isLt, dite_true]
  rfl

/-- At a singleton site both endpoint fields are clamped and there are no interior sends. -/
theorem singleton_clamps (sent : Sends 1 Word) :
    outgoing sent 0 = none ∧ receive sent 0 = none := ⟨rfl, rfl⟩

variable [Zero Word]

/-- The validator checks each read using its incoming field and, when a successor
exists, checks its outgoing field against its own final physical slot. -/
def checkAt (hB : 0 < B) (sent : Sends S Word) (v : Fin S)
    (block : Fin B → Option (Record Word)) : Prop :=
  PaddedCheck (receive sent v) (List.ofFn block) ∧
    (v.val + 1 < S → outgoing sent v = lastSlot hB block)

/-- Apply the one-site validator to the corresponding block of the sorted array. -/
def checks (hB : 0 < B) (blocks : Fin S → Fin B → Option (Record Word))
    (sent : Sends S Word) (v : Fin S) : Prop := checkAt hB sent v (blocks v)

omit [Zero Word] in
private theorem block_last (hB : 0 < B) (block : Fin B → Option (Record Word)) :
    (List.ofFn block).getLast? = some (lastSlot hB block) := by
  have hne : List.ofFn block ≠ [] := mt List.ofFn_eq_nil_iff.mp (Nat.ne_of_gt hB)
  rw [List.getLast?_eq_some_getLast hne, List.getLast_ofFn]
  rfl

private theorem paddedCheck_flat_iff (hB : 0 < B) (blocks : Fin S → Fin B → Option (Record Word))
    (previous : Option (Record Word)) :
    PaddedCheck previous (flat blocks) ↔
      ∀ v, PaddedCheck (receiveFrom previous (actual hB blocks) v) (List.ofFn (blocks v)) := by
  induction S generalizing previous with
  | zero => simp [flat, PaddedCheck]
  | succ S ih =>
    let rest := fun v : Fin S ↦ blocks v.succ
    have hflat : flat blocks = List.ofFn (blocks 0) ++ flat rest := by
      unfold flat
      rw [List.ofFn_succ, List.flatten_cons]
    rw [hflat, paddedCheck_append, block_last hB, Option.getD_some, ih rest, Fin.forall_fin_succ]
    refine and_congr Iff.rfl (forall_congr' fun v ↦ ?_)
    have hreceive : receiveFrom (lastSlot hB (blocks 0)) (actual hB rest) v =
        receiveFrom previous (actual hB blocks) v.succ := by
      rcases v with ⟨i, hi⟩
      cases i <;> rfl
    rw [hreceive]

/-- The outgoing checks force the complete assignment of interior fields.
The remaining site checks are equivalent to one scan of the physical array. -/
theorem checks_iff (hB : 0 < B) (blocks : Fin S → Fin B → Option (Record Word))
    (sent : Sends S Word) :
    (∀ v, checks hB blocks sent v) ↔ PaddedCheck none (flat blocks) ∧ sent = actual hB blocks := by
  constructor
  · intro hv
    have he : sent = actual hB blocks := by
      funext i
      have hi : i.val + 1 < S := by have := i.isLt; omega
      let v : Fin S := ⟨i.val, by omega⟩
      simpa only [v, outgoing, hi, dite_eq_left, actual] using (hv v).2 hi
    subst sent
    exact ⟨(paddedCheck_flat_iff hB blocks none).mpr (fun v ↦ (hv v).1), rfl⟩
  · rintro ⟨hp, rfl⟩ v
    refine ⟨(paddedCheck_flat_iff hB blocks none).mp hp v, fun hv ↦ ?_⟩
    simp [outgoing, hv, actual]

/-- Exactly one shared last-record assignment passes all the local checks
when the flattened physical array passes its global predecessor check. -/
theorem existsUnique_checks_iff (hB : 0 < B) (blocks : Fin S → Fin B → Option (Record Word)) :
    (∃! sent : Sends S Word, ∀ v, checks hB blocks sent v) ↔ PaddedCheck none (flat blocks) := by
  constructor
  · rintro ⟨sent, h, _⟩
    exact ((checks_iff hB blocks sent).mp h).1
  · intro h
    exact ⟨actual hB blocks, (checks_iff ..).mpr ⟨h, rfl⟩,
      fun sent hs ↦ ((checks_iff ..).mp hs).2⟩

end RAMBoundary

end VPVNP
end Computability
end OAI
