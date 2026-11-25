import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import OAI.LinearAlgebra.MatrixExponent.Lookup.Scan
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Control.Address

section
/-! # Occurrence ranks in a finite sequence -/

namespace OAI.LinearAlgebra.MatrixExponent.Control
open Finset

variable {n : ℕ} {A : Type} [DecidableEq A]

/-- Count occurrences at earlier positions, or in the whole sequence for `none`. -/
def histogram (x : Fin n → A) (z : A) (j : Option (Fin n)) : ℕ :=
  (univ.filter fun i => x i = z ∧ ∀ k, j = some k → i < k).card

def rank (x : Fin n → A) (i : Fin n) : ℕ := histogram x (x i) (some i)

variable (x : Fin n → A)

theorem histogram_some (z : A) (j : Fin n) :
    histogram x z (some j) = (univ.filter fun i => x i = z ∧ i < j).card := by
  simp [histogram]

theorem histogram_none (z : A) :
    histogram x z none = (univ.filter fun i => x i = z).card := by
  simp [histogram]

theorem histogram_le (z : A) (j : Option (Fin n)) : histogram x z j ≤ n := by
  unfold histogram
  exact (card_filter_le ..).trans_eq (card_fin n)

theorem rank_lt (i : Fin n) : rank x i < histogram x (x i) none := by
  rw [rank, histogram_some, histogram_none]
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro j hj
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2.1⟩
  · intro he
    have := congrArg (i ∈ ·) he
    simp at this

theorem rank_mono {i j : Fin n} (he : x i = x j) (h : i < j) : rank x i < rank x j := by
  rw [rank, rank, histogram_some, histogram_some, he]
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨_, hz, hi⟩ := mem_filter.mp hl
    exact mem_filter.mpr ⟨mem_univ _, hz, hi.trans h⟩
  · intro hh
    have := congrArg (i ∈ ·) hh
    simp [h, he] at this

theorem rank_injective : Function.Injective (fun i => (x i, rank x i)) := by
  intro i j he
  obtain ⟨hz, hr⟩ := Prod.mk.inj he
  rcases lt_trichotomy i j with hij | hij | hij
  · exact ((rank_mono x hz hij).ne hr).elim
  · exact hij
  · exact ((rank_mono x hz.symm hij).ne hr.symm).elim

theorem rank_range (z : A) (r : ℕ) :
    (∃ i, x i = z ∧ rank x i = r) ↔ r < histogram x z none := by
  let S := univ.filter (fun i => x i = z)
  have hi : Set.InjOn (rank x) ↑S := by
    intro i h₁ j h₂ h
    exact rank_injective x (Prod.ext ((mem_filter.mp h₁).2.trans (mem_filter.mp h₂).2.symm) h)
  have he : S.image (rank x) = range (histogram x z none) := by
    apply eq_of_subset_of_card_le
    · rintro k hk
      obtain ⟨i, hz, rfl⟩ := mem_image.mp hk
      exact mem_range.mpr ((mem_filter.mp hz).2 ▸ rank_lt x i)
    · rw [card_range, card_image_of_injOn hi, histogram_none]
  simpa [S] using congrArg (r ∈ ·) he

end OAI.LinearAlgebra.MatrixExponent.Control
end

section
/-!
# Binary prefix counts

At each bit, keep the old count and send the updated one to the next
position. Only that counter is connected between two blocks.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Control

private def run (t : ℕ) :
    (h : ℕ) → Val (.pair (word t) (tree h .bit)) → Val (.pair (tree h (word t)) (word t))
  | 0, x => (x.1, if x.2 then Lookup.inc t x.1 else x.1)
  | h + 1, x =>
    let l := run t h (x.1, x.2.1)
    let r := run t h (l.2, x.2.2)
    ((l.1, r.1), r.2)

private theorem run_net (F : Type) [Field F] (t h : ℕ) :
    DNet F (.pair (word t) (tree h .bit)) (.pair (tree h (word t)) (word t))
      (run t h) (2 ^ h * (200 * (1 + t))) := by
  induction h with
  | zero =>
    have a := DNet.fst F (word t) .bit
    have b := DNet.snd F (word t) .bit
    have next := (((a.comp (Lookup.inc_net F t)).pair a).pair b).comp (selectWord F t)
    exact (a.pair next).mono (by simp only [pow_zero, one_mul, wd_word, wd]; omega)
  | succ h ih =>
    rw [pow_succ, mul_two, add_mul]
    exact ((ih.plug ih).pre (.assoc' _ _ _)).post (.assoc' _ _ _)

private def counts (t k : ℕ) : List Bool → List (Val (word t))
  | [] => []
  | b::bs => Lookup.bits t k :: counts t (k + b.toNat) bs

private theorem counts_append (t k : ℕ) (xs ys : List Bool) :
    counts t k (xs ++ ys) = counts t k xs ++ counts t (k + xs.count true) ys := by
  induction xs generalizing k with
  | nil => simp [counts]
  | cons b xs ih => cases b <;> simp [counts, ih, Nat.add_left_comm, Nat.add_comm]

private theorem run_eq (t h k : ℕ) (x : Val (tree h .bit)) :
    flatten h (run t h (Lookup.bits t k, x)).1 = counts t k (flatten h x) ∧
    (run t h (Lookup.bits t k, x)).2 = Lookup.bits t (k + (flatten h x).count true) := by
  induction h generalizing k with
  | zero =>
    cases x <;> simp [flatten, counts, run, Lookup.bits, Function.iterate_succ_apply']
  | succ h ih =>
    simp only [run, flatten, counts_append, List.count_append, (ih _ x.1).1, (ih _ x.1).2,
      (ih _ x.2).1, (ih _ x.2).2, Nat.add_assoc, and_self]

private theorem histogram_succ {n : ℕ} (x : Fin (n + 1) → Bool) (i : Fin n) :
    histogram x true (some i.succ) = (x 0).toNat + histogram (fun j => x j.succ) true (some i) := by
  rw [histogram_some, histogram_some, Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  cases x 0 <;> simp

private theorem counts_ofFn {n : ℕ} (x : Fin n → Bool) (t k : ℕ) :
    counts t k (List.ofFn x) =
      List.ofFn (fun i => Lookup.bits t (k + histogram x true (some i))) ∧
    (List.ofFn x).count true = histogram x true none := by
  induction n generalizing k with
  | zero => simp [counts, histogram_none]
  | succ n ih =>
    obtain ⟨h, he⟩ := ih (fun i => x i.succ) (k + (x 0).toNat)
    have hz : histogram x true (some 0) = 0 := by simp [histogram_some]
    constructor
    · rw [List.ofFn_succ, List.ofFn_succ, counts, h]
      simp only [hz, Nat.add_zero, histogram_succ, Nat.add_assoc]
    · rw [List.ofFn_succ, List.count_cons, he, histogram_none, histogram_none,
        Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
      cases x 0 <;> simp [add_comm]

def bitPrefix (h : ℕ) (x : Val (tree h .bit)) :
    Val (.pair (tree h (word (h + 1))) (word (h + 1))) :=
  run (h + 1) h (Lookup.zero _, x)

theorem prefix_net (F : Type) [Field F] (h : ℕ) :
    DNet F (tree h .bit) (.pair (tree h (word (h + 1))) (word (h + 1)))
      (bitPrefix h) (500 * 2 ^ h * (h + 1)) := by
  have init := ((Lookup.const_net F (word (h + 1)) (Lookup.zero _)).par (DNet.id F (tree h .bit))).pre
    ((Rewire.unit' _).comp (.swap _ _))
  apply (init.comp (run_net F (h + 1) h)).mono
  simp only [wd_tree, wd, wd_word]
  have hh := Nat.one_le_pow h 2 (by decide)
  nlinarith [Nat.mul_le_mul_right h hh]

theorem prefix_eq (h : ℕ) (x : Val (tree h .bit)) (r : Fin (2 ^ h) → Bool)
    (he : List.ofFn r = flatten h x) :
    flatten h (bitPrefix h x).1 = List.ofFn (fun i => Lookup.bits (h + 1) (histogram r true (some i))) ∧
    (bitPrefix h x).2 = Lookup.bits (h + 1) (histogram r true none) := by
  have hh := run_eq (h + 1) h 0 x
  obtain ⟨ha, hb⟩ := counts_ofFn r (h + 1) 0
  rw [← he, ha, hb] at hh
  simpa only [Nat.zero_add, bitPrefix, Lookup.bits, Function.iterate_zero_apply] using hh

theorem equal_net (F : Type) [Field F] (a : Wire) (z : Val a) :
    DNet F a .bit (fun y => decide (y = z)) (10 * wd a + 1) := by
  obtain ⟨e, he, hi⟩ := Rewire.exists_of_width (wd_word (wd a)).symm
  have h := ((DNet.id F a).par (Lookup.const_net F a z)).pre (.unit' _)
  have cmp := h.comp ((Lookup.eq_net F (wd a)).pre (he.par he))
  simpa only [hi.eq_iff] using cmp.mono (n := 10 * wd a + 1) (by omega)

theorem histogram_net (F : Type) [Field F] (a : Wire) (h : ℕ) (z : Val a) :
    ∃ f, DNet F (tree h a) (.pair (tree h (word (h + 1))) (word (h + 1)))
      f (2 ^ h * (wd a * 20 + 1000 * (h + 1))) ∧
      ∀ (x : Val (tree h a)) (r : Fin (2 ^ h) → Val a), List.ofFn r = flatten h x →
        flatten h (f x).1 = List.ofFn (fun i => Lookup.bits (h + 1) (histogram r z (some i))) ∧
        (f x).2 = Lookup.bits (h + 1) (histogram r z none) := by
  have hn := (Tagged.mapRows_net (equal_net F a z) h).comp (prefix_net F h)
  refine ⟨_, hn.mono (by ring_nf; omega), fun x r he => ?_⟩
  have hh := prefix_eq h (Tagged.mapRows (b := .bit) (fun y => decide (y = z)) h x)
    (fun i => decide (r i = z)) (by rw [Tagged.flatten_mapRows, ← he, List.map_ofFn]; rfl)
  simpa only [histogram, decide_eq_true_eq] using hh

def bitLayout {h : ℕ} (L : Layout .bit (tree h .bit) (Fin (2 ^ h))) :
    Fin (2 ^ h) ≃ slots (tree h .bit) :=
  (Equiv.prodUnique _ Unit).symm.trans L.positions

private def outputs {a : Wire} {h : ℕ} (L : Layout a (tree h a) (Fin (2 ^ h))) :
    Option (Fin (2 ^ h)) × slots a ≃ slots (.pair (tree h a) a) :=
  ((Equiv.optionEquivSumPUnit _).prodCongr (.refl _)).trans
    ((Equiv.sumProdDistrib _ Unit _).trans (L.positions.sumCongr (Equiv.uniqueProd _ Unit)))

theorem prefix_bnet (F : Type) [Field F] (h : ℕ) :
    Install.BNet F (fun (x : Fin (2 ^ h) → Bool) (p : Option (Fin (2 ^ h)) × slots (word (h + 1))) =>
      bits (word (h + 1)) (Lookup.bits (h + 1) (histogram x true p.1)) p.2)
      (1000 * 2 ^ h * (h + 1)) := by
  obtain ⟨L, hL⟩ := Layout.exists_tree .bit h
  obtain ⟨P, hP⟩ := Layout.exists_tree (word (h + 1)) h
  apply Install.BNet.of_layout (bitLayout L) (outputs P)
  convert (prefix_net F h).mono (n := 1000 * 2 ^ h * (h + 1)) (by gcongr; decide) using 1
  funext x
  apply (bits _).injective
  rw [Equiv.apply_symm_apply]
  obtain ⟨hs, hn⟩ := prefix_eq h x (L.read x) (hL _)
  have hs' := List.ofFn_injective ((hP _).trans hs)
  funext z
  obtain ⟨⟨i, k⟩, rfl⟩ := (outputs P).surjective z
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  change bits (word (h + 1)) (Lookup.bits (h + 1) (histogram (L.read x) true i)) k = _
  cases i with
  | none => rw [← hn]; rfl
  | some i =>
    have hp := congrFun hs' i
    rw [← hp, Layout.read, Equiv.apply_symm_apply]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Control
end

section
/-!
# Selecting positions by occurrence rank

Dividing a little-endian count by a power of two discards leading wires.
A comparison with a constant selects the required bucket.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Control

private theorem value_test (F : Type) [Field F] (t j : ℕ) :
    DNet F (word t) .bit (fun x => decide (Lookup.value t x = j)) (10 * t + 1) := by
  by_cases h : j < 2 ^ t
  · have e (x) : Lookup.value t x = j ↔ x = Lookup.bits t j := by
      rw [← (value_injective t).eq_iff, Lookup.value_bits h]
    simpa only [e, wd_word] using equal_net F (word t) (Lookup.bits t j)
  · have e (x) : Lookup.value t x ≠ j := (value_lt t x).trans_le (le_of_not_gt h) |>.ne
    have hs := (DNet.discard F (word t)).comp (Lookup.const_net F .bit false)
    simpa only [e, decide_false] using hs.mono (n := 10 * t + 1) (by simp [wd]; omega)

theorem quotient_test (F : Type) [Field F] (t q j : ℕ) :
    DNet F (word t) .bit (fun x => decide (Lookup.value t x / 2 ^ q = j)) (10 * t + 1) := by
  induction t generalizing q with
  | zero => exact DNet.table F _ _ _ (by decide)
  | succ t ih =>
    cases q with
    | zero => simpa only [pow_zero, Nat.div_one] using value_test F (t + 1) j
    | succ q =>
      have hs := ((DNet.discard F .bit).par (ih q)).post ((Rewire.swap _ _).comp (.unit _))
      convert hs.mono (n := 10 * (t + 1) + 1) (by simp only [wd]; omega) using 1
      funext x
      have he : Lookup.value (t + 1) x / 2 = Lookup.value t x.2 := by
        obtain ⟨b, x⟩ := x
        cases b <;> simp [Lookup.value]
        omega
      rw [pow_succ', ← Nat.div_div_eq_div_mul, he]

theorem flatten_zip {a b c : Wire} (f : Val a → Val b → Val c)
    (h : ℕ) (x : Val (tree h a)) (y : Val (tree h b)) :
    flatten h (Tagged.zipRows f h x y) = List.zipWith f (flatten h x) (flatten h y) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [flatten, Tagged.zipRows, ih]
    rw [List.zipWith_append (by simp [Tagged.length_flatten])]

theorem zip_ofFn {A B C : Type} {n : ℕ} (f : A → B → C) (x : Fin n → A) (y : Fin n → B) :
    List.zipWith f (List.ofFn x) (List.ofFn y) = List.ofFn (fun i => f (x i) (y i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ, ih]

theorem bucket_bnet (F : Type) [Field F] (h q j : ℕ) :
    Install.BNet F (fun (x : Fin (2 ^ h) → Bool) (i : Fin (2 ^ h)) =>
      x i && decide (histogram x true (some i) / 2 ^ q = j)) (1000 * 2 ^ h * (h + 1)) := by
  let test (b : Bool) (v : Val (word (h + 1))) := b && decide (Lookup.value _ v / 2 ^ q = j)
  have ht := ((DNet.id F .bit).par (quotient_test F (h + 1) q j)).comp
    (DNet.table F (.pair .bit .bit) .bit (fun x => x.1 && x.2) (by decide))
  have hp := (prefix_net F h).comp (DNet.fst F _ _)
  have hs := ((DNet.id F (tree h .bit)).pair hp).comp
    (Tagged.zipRows_net (a := .bit) (b := word (h + 1)) (c := .bit) (f := test) ht h)
  have hc := hs.mono (n := 1000 * 2 ^ h * (h + 1)) (by
    simp only [wd, wd_tree, wd_word]
    have := Nat.one_le_pow h 2 (by decide)
    nlinarith [Nat.mul_le_mul_right h this])
  obtain ⟨L, hL⟩ := Layout.exists_tree .bit h
  apply Install.BNet.of_layout (bitLayout L) (bitLayout L)
  convert hc using 1
  funext x
  have hx := (prefix_eq h x (L.read x) (hL _)).1
  apply L.injective
  apply List.ofFn_injective
  rw [hL (Tagged.zipRows ..), flatten_zip, hx, ← hL x, zip_ofFn]
  congr 1
  funext i
  have hv : histogram (L.read x) true (some i) < 2 ^ (h + 1) :=
    (histogram_le ..).trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  simp only [test, Lookup.value_bits hv]
  change bits (tree h .bit) ((bits (tree h .bit)).symm _) (bitLayout L i) = _
  rw [Equiv.apply_symm_apply, Function.comp_apply, Equiv.symm_apply_apply]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Control
end
