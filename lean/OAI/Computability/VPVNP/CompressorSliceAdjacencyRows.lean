import OAI.Computability.VPVNP.CompressorRecordTable
import Mathlib.Data.Finset.Card

/-!
# Endpoint rows of the copy-slice scan

A bounded row records all nonempty frame identifiers at an endpoint in scan order.
For a rectangular table the opposite coordinate injects the retained frames of
one row into its slot range.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SliceRAM

open BurstRAM

variable {w : ℕ}

/-- Nonempty frames incident to endpoint `v` among the first `k` frames. -/
def adjPrefix (w : ℕ) (length owner : ℕ → ℕ) (v k : ℕ) : List (Word w) :=
  ((List.range k).filter fun t => length t ≠ 0 ∧ owner t = v).map (Fin.ofNat (2^w))

theorem adjPrefix_succ (length owner : ℕ → ℕ) (v k : ℕ) :
    adjPrefix w length owner v (k+1) = adjPrefix w length owner v k ++
      (if length k ≠ 0 ∧ owner k = v then [Fin.ofNat (2^w) k] else []) := by
  by_cases h : length k ≠ 0 ∧ owner k = v <;> simp [adjPrefix, List.range_succ, h]

private theorem adjPrefix_le {length owner : ℕ → ℕ} {v k cap : ℕ} (slot : ℕ → ℕ)
    (hfit : ∀ t, t < k → owner t = v → slot t < cap)
    (hinj : ∀ a b, owner a = v → owner b = v → slot a = slot b → a = b) :
    (adjPrefix w length owner v k).length ≤ cap := by
  let xs := (List.range k).filter fun t => decide (length t ≠ 0 ∧ owner t = v)
  have hs {t : ℕ} (h : t ∈ xs.toFinset) : t < k ∧ owner t = v := by
    have ht : t < k ∧ length t ≠ 0 ∧ owner t = v := by simpa [xs] using h
    exact ⟨ht.1, ht.2.2⟩
  simp only [adjPrefix, List.length_map]
  change xs.length ≤ cap
  rw [← List.toFinset_card_of_nodup (l := xs) (List.nodup_range.filter _), ← Finset.card_range cap]
  exact Finset.card_le_card_of_injOn slot
    (fun t ht => Finset.mem_range.mpr (hfit t (hs ht).1 (hs ht).2))
    (fun a ha b hb h => hinj a b (hs ha).2 (hs hb).2 h)

/-- At an old endpoint, remainders are distinct slots below the number of new endpoints. -/
theorem adjPrefix_old_le (length : ℕ → ℕ) {m n v k : ℕ} (hk : k ≤ m*n) :
    (adjPrefix w length (· / n) v k).length ≤ n := by
  apply adjPrefix_le (fun t => t % n)
  · intro t ht _
    exact Nat.mod_lt _ (by by_contra! h; simp [show n = 0 by omega] at hk; omega)
  · intro a b ha hb he
    simpa only [Nat.mod_add_div] using
      (show a % n + n * (a / n) = b % n + n * (b / n) by rw [ha, hb, he])

/-- At a new endpoint, quotients are distinct slots below the number of old endpoints. -/
theorem adjPrefix_new_le (length : ℕ → ℕ) {m n v k : ℕ} (hk : k ≤ m*n) :
    (adjPrefix w length (· % n) v k).length ≤ m := by
  apply adjPrefix_le (fun t => t / n)
  · intro t ht _
    exact (Nat.div_lt_iff_lt_mul (by by_contra! h; simp [show n = 0 by omega] at hk; omega)).mpr
      (lt_of_lt_of_le ht hk)
  · intro a b ha hb he
    calc a = a % n + n * (a / n) := (Nat.mod_add_div ..).symm
         _ = b % n + n * (b / n) := by rw [ha, hb, he]
         _ = b := Nat.mod_add_div ..

/-- The counter array followed by the fixed-capacity rows of one endpoint class. -/
structure AdjBank (w : ℕ) where
  /-- Base address of the per-endpoint reference counts. -/
  countHead : Word w
  /-- Base address of the rectangular array of frame-reference rows. -/
  refHead : Word w
  /-- Number of endpoints represented by this adjacency directory. -/
  size : Word w
  /-- Number of reference slots reserved for each endpoint. -/
  cap : Word w

namespace AdjBank

/-- Address of endpoint `v`'s live reference count. -/
def count (B : AdjBank w) (v : Word w) := B.countHead + v
/-- Address of the first reference slot for endpoint `v`. -/
def row (B : AdjBank w) (v : Word w) := B.refHead + v * B.cap
/-- Exclusive natural-number end address of the reference array. -/
def stop (B : AdjBank w) := B.refHead.val + B.size.val * B.cap.val

/-- The counter and reference arrays may have an unrelated table between them. -/
def Inside (B : AdjBank w) (x : ℕ) : Prop :=
  (B.countHead.val ≤ x ∧ x < B.countHead.val + B.size.val) ∨
    (B.refHead.val ≤ x ∧ x < B.stop)

/-- The count array ends before the reference array and the reference array fits in the address
space. -/
structure Fits (B : AdjBank w) : Prop where
  countsBeforeRows : B.countHead.val + B.size.val ≤ B.refHead.val
  rowsFit : B.stop ≤ 2^w

/-- Each endpoint row contains exactly its positive-length frame ordinals among the first `k`
candidates, in scan order. -/
def Represents (B : AdjBank w) (mem : Memory w) (length owner : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ v : Word w, v < B.size → rowRepresents mem (B.count v) (B.row v) (adjPrefix w length owner v.val k)

theorem count_val {B : AdjBank w} (h : B.Fits) {v : Word w} (hv : v < B.size) :
    (B.count v).val = B.countHead.val + v.val := by
  have := h.countsBeforeRows
  have := B.refHead.isLt
  change v.val < B.size.val at hv
  rw [count, Fin.val_add, Nat.mod_eq_of_lt (by omega)]

private theorem row_bound {B : AdjBank w} {v : Word w} (hv : v < B.size) :
    B.refHead.val + v.val * B.cap.val + B.cap.val ≤ B.stop := by
  have h := Nat.mul_le_mul_right B.cap.val (show v.val+1 ≤ B.size.val from hv)
  rw [Nat.succ_mul] at h
  dsimp [stop]
  omega

theorem row_val {B : AdjBank w} (h : B.Fits) {v : Word w} (hv : v < B.size) :
    (B.row v).val = B.refHead.val + v.val * B.cap.val := by
  have h1 := row_bound hv
  have h2 := h.rowsFit
  by_cases hc : B.cap.val = 0
  · simp [row, Fin.val_add, Fin.val_mul, hc, Nat.mod_eq_of_lt B.refHead.isLt]
  · rw [row, Fin.val_add, Fin.val_mul, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]

/-- Cells outside the bank do not enter its row interpretation. -/
theorem represents_congr {B : AdjBank w} (hf : B.Fits) {length owner : ℕ → ℕ} {k : ℕ}
    {mem mem' : Memory w} (h : B.Represents mem length owner k)
    (cap : ∀ v : Word w, v < B.size → (adjPrefix w length owner v.val k).length ≤ B.cap.val)
    (heq : ∀ x, B.Inside x → mem' x = mem x) :
    B.Represents mem' length owner k := by
  intro v hv
  have hr := h v hv
  have hc := cap v hv
  have h1 := hf.countsBeforeRows
  have h2 := row_bound hv
  have h3 := count_val hf hv
  have h4 := row_val hf hv
  change v.val < B.size.val at hv
  constructor
  · rw [heq _ (Or.inl ⟨by omega, by omega⟩)]
    exact hr.1
  · intro i
    have := i.isLt
    rw [heq _ (Or.inr ⟨by omega, by omega⟩)]
    exact hr.2 i

/-- Appending to one row preserves the other rows and every external cell. -/
theorem append_step {B : AdjBank w} (hf : B.Fits) {length owner : ℕ → ℕ} {k : ℕ}
    {mem : Memory w} (h : B.Represents mem length owner k) {v id : Word w}
    (hv : v < B.size) (ho : owner k = v.val) (hid : id = Fin.ofNat (2^w) k)
    (hne : length k ≠ 0)
    (cap : ∀ u : Word w, u < B.size → (adjPrefix w length owner u.val (k+1)).length ≤ B.cap.val) :
    let newMem := writeMemory (writeMemory mem (B.row v + mem (B.count v).val) id)
      (B.count v) (mem (B.count v).val + 1)
    B.Represents newMem length owner (k+1) ∧
      ∀ x, ¬ B.Inside x → newMem x = mem x := by
  dsimp only
  have hprefix : adjPrefix w length owner v.val (k+1) = adjPrefix w length owner v.val k ++ [id] := by
    rw [adjPrefix_succ, ite_eq_left ⟨hne, ho⟩, hid]
  have hc := cap v hv
  simp only [hprefix, List.length_append, List.length_singleton] at hc
  have hr := h v hv
  have hcap : (mem (B.count v).val).val < B.cap.val := by rw [hr.1]; omega
  have hcount := count_val hf hv
  have hrow := row_val hf hv
  have hmax := row_bound hv
  have hfit := hf.rowsFit
  have hsep := hf.countsBeforeRows
  have hv' := Fin.lt_def.mp hv
  have hslot : (B.row v + mem (B.count v).val).val = (B.row v).val + (mem (B.count v).val).val := by
    rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  constructor
  · intro u hu
    by_cases he : u = v
    · subst u
      rw [hprefix]
      exact appendRecord_represents (cap := B.cap) hr (by omega) (by omega) (Or.inl (by omega))
    · have huv : v.val ≠ u.val := fun eq => he (Fin.ext eq.symm)
      have huPrefix : adjPrefix w length owner u.val (k+1) = adjPrefix w length owner u.val k := by
        simp [adjPrefix_succ, ho, huv]
      rw [huPrefix]
      have huCap := cap u hu
      rw [huPrefix] at huCap
      have huC := count_val hf hu
      have huR := row_val hf hu
      have hu' := Fin.lt_def.mp hu
      have hpre := h u hu
      constructor
      · simpa only [writeMemory, ite_eq_right (show (B.count u).val ≠ (B.count v).val by omega),
          ite_eq_right (show (B.count u).val ≠ (B.row v + mem (B.count v).val).val by omega)] using hpre.1
      · intro i
        have hi := i.isLt
        have apart : u.val * B.cap.val + B.cap.val ≤ v.val * B.cap.val ∨
            v.val * B.cap.val + B.cap.val ≤ u.val * B.cap.val := by
          rcases lt_or_gt_of_ne huv with hlt | hlt
          · exact Or.inr (by simpa [Nat.succ_mul] using Nat.mul_le_mul_right B.cap.val (Nat.succ_le_of_lt hlt))
          · exact Or.inl (by simpa [Nat.succ_mul] using Nat.mul_le_mul_right B.cap.val (Nat.succ_le_of_lt hlt))
        simpa only [writeMemory, ite_eq_right (show (B.row u).val + i.val ≠ (B.count v).val by omega),
          ite_eq_right (show (B.row u).val + i.val ≠ (B.row v + mem (B.count v).val).val by omega)] using hpre.2 i
  · intro x hx
    simp only [Inside, not_or, not_and_or, not_le, not_lt] at hx
    simp only [writeMemory, ite_eq_right (show x ≠ (B.count v).val by omega),
      ite_eq_right (show x ≠ (B.row v + mem (B.count v).val).val by omega)]

end AdjBank

end CompressorRecords.SliceRAM

end VPVNP
end Computability
end OAI
