import OAI.Computability.BorderVNP.ParseBatchVerifierCountRanks
import OAI.Computability.BorderVNP.ParseBatchSortBounds
import Mathlib.Data.Fin.Tuple.Sort

/-! # Binary sort keys for use rows and end markers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchCounts

open ParseBatchSort VPVNP.VerifierNetwork

/-- The standard numerical enumeration of fixed-width, most-significant-first words. -/
noncomputable def numberWords (w : ℕ) : (Fin w → Bool) ≃ Fin (2^w) :=
  Equiv.ofBijective (fun v => ⟨value v, value_lt v⟩) <|
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ e => value_injective w (congrArg Fin.val e), by simp⟩

@[simp] theorem value_encode {w : ℕ} (i : Fin (2^w)) :
    value ((numberWords w).symm i) = i.val :=
  congrArg Fin.val ((numberWords w).apply_symm_apply i)

private def cat {T : Type*} {w : ℕ} : {a : ℕ} → (Fin a → T) → (Fin w → T) → Fin (w+a) → T
  | 0, _, tail => tail
  | _+1, head, tail => Fin.cons (head 0) (cat (fun i => head i.succ) tail)

private theorem value_cat {a w : ℕ} (v : Fin a → Bool) (t : Fin w → Bool) :
    value (cat v t) = value v * 2^w + value t := by
  induction a with
  | zero => simp [value, cat]
  | succ a ih =>
    simp only [value, cat, Fin.cons_zero, Fin.cons_succ]
    change (v 0).toNat * 2^(w+a) + value (cat (fun i => v i.succ) t) = _
    rw [ih, pow_add]; ring

private def suffix {w : ℕ} : (a : ℕ) → Fin w → Fin (w+a)
  | 0, i => i
  | a+1, i => (suffix a i).succ

private theorem cat_suffix {T : Type*} {a w : ℕ} (v : Fin a → T) (t : Fin w → T) (j : Fin w) :
    cat v t (suffix a j) = t j := by
  induction a with
  | zero => rfl
  | succ a ih => simpa [cat, suffix] using ih (fun i => v i.succ)

private theorem cat_map {T E : Type*} (f : T → E) {a w : ℕ} (v : Fin a → T) (t : Fin w → T) :
    f ∘ cat v t = cat (f ∘ v) (f ∘ t) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simpa [cat, Function.comp_def] using congrFun (ih (fun i => v i.succ)) j

/-- Padding tag, parameter label, end-marker tag, and claimed sorted position. -/
def word {T : Type*} {a b : ℕ} (pad : T) (label : Fin a → T) (endTag : T) (pos : Fin b → T) :
    Fin ((b+1+a)+1) → T := Fin.cons pad (cat label (Fin.cons endTag pos))

/-- The end marker bit sits just after the label. -/
def tagPin (a b : ℕ) : Fin ((b+1+a)+1) := (suffix a (0 : Fin (b+1))).succ

/-- Payload bits carry the candidate position within the complete sorted array. -/
def positionPin (a b : ℕ) (j : Fin b) : Fin ((b+1+a)+1) := (suffix a j.succ).succ

@[simp] theorem word_tag {T : Type*} {a b : ℕ} (p : T) (l : Fin a → T) (m : T) (v : Fin b → T) :
    word p l m v (tagPin a b) = m := by simp [word, tagPin, cat_suffix]

@[simp] theorem word_position {T : Type*} {a b : ℕ} (p : T) (l : Fin a → T) (m : T)
    (v : Fin b → T) (j : Fin b) : word p l m v (positionPin a b j) = v j := by
  simp [word, positionPin, cat_suffix]

/-- Reading a symbolic record through a pin assignment reads each of its fields. -/
theorem word_map {T E : Type*} (f : T → E) {a b : ℕ} (p : T) (l : Fin a → T)
    (m : T) (v : Fin b → T) : f ∘ word p l m v = word (f p) (f ∘ l) (f m) (f ∘ v) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  have e := cat_map f l (Fin.cons m v)
  rw [Fin.comp_cons] at e
  exact congrFun e j

/-- Discarding the position field leaves the lexicographic label and row kind. -/
theorem word_key {a b : ℕ} (p : Bool) (l : Fin a → Bool) (m : Bool) (v : Fin b → Bool) :
    value (word p l m v) / 2^b = 2*(p.toNat * 2^a + value l) + m.toNat := by
  have h : value (word p l m v) =
      value v + (2*(p.toNat * 2^a + value l) + m.toNat) * 2^b := by
    simp only [word, value, Fin.cons_zero, Fin.cons_succ, value_cat, pow_add, pow_one]
    ring
  rw [h, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (value_lt _), zero_add]

/-- Sorting the physical rows reindexes the complete binary words by a permutation. -/
theorem phases_order {σ : Type*} [Fintype σ] {b w : ℕ} (f : Frame σ (Pins b w))
    (x : σ → Bool) : ∃ π : Equiv.Perm (Fin (2^b)), ∀ i j,
      (phases b le_rfl f).eval x (i,j) = f.eval x (π i,j) := by
  let raw (i : Fin (2^b)) := value (fun j => f.eval x (i,j))
  let sorted (i : Fin (2^b)) := value (fun j => (phases b le_rfl f).eval x (i,j))
  let π := Tuple.sort raw
  have hp : (List.ofFn sorted).Perm (List.ofFn raw) := by
    simpa only [List.map_ofFn, Function.comp_def, sorted, raw] using (phases_perm f x).map value
  have hmono : Monotone (raw ∘ π) := Tuple.monotone_sort _
  have eq : sorted = raw ∘ π := List.ofFn_injective <|
    (hp.trans (π.ofFn_comp_perm raw).symm).eq_of_pairwise'
      (phases_monotone f x).sortedLE_ofFn.pairwise hmono.sortedLE_ofFn.pairwise
  exact ⟨π, fun i j => congrFun (value_injective w (congrFun eq i)) j⟩

end ParseBatchCounts

end BorderVNP
end Computability
end OAI
