import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.LinearAlgebra.MatrixExponent.Tagged.Tags
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute
import OAI.LinearAlgebra.MatrixExponent.Tagged.ColumnNetwork
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortOne
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortBack
import OAI.LinearAlgebra.MatrixExponent.Tagged.Hard

section
/-! # Width and sorting costs for many independent lists -/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

open Filter

/-- Two sorting lifts pay for each doubling of the record width. -/
private theorem lift_range {w v k : ℕ} (hw : 5 ≤ w) (h : 2 * (w + v) ≤ 2 ^ k * (w + 1)) :
    2 ^ (2 * k) * (w + v - 2) ≤ 3 ^ (2 * k) * (w - 2) := by
  have hb : w + v - 2 ≤ 2 ^ k * (w - 2) := by
    have hm := h.trans (Nat.mul_le_mul_left (2 ^ k) (show w + 1 ≤ 2 * (w - 2) by omega))
    rw [mul_left_comm (2 ^ k)] at hm
    omega
  calc
    _ ≤ 2 ^ (2 * k) * (2 ^ k * (w - 2)) := Nat.mul_le_mul_left _ hb
    _ = 8 ^ k * (w - 2) := by rw [pow_mul, ← mul_assoc, ← mul_pow]; rfl
    _ ≤ 3 ^ (2 * k) * (w - 2) := by rw [pow_mul]; gcongr; decide

/-- Reserve enough exponent slack to absorb both width doubling and
parallel sort lifting, uniformly in the logarithm `v` of the batch size. -/
theorem parameters {s : ℝ} (hs : 0 < s) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ w : ℕ in atTop, ∀ v : ℕ,
      (v : ℝ) ≤ ((w + 1 : ℕ) : ℝ) ^ (1 + η) →
      ∃ k j : ℕ, 2 * (w + v) ≤ 2 ^ k * (w + 1) ∧ 2 ^ j * (w + v - 2) ≤ 3 ^ j * (w - 2) ∧
        (4 : ℝ) ^ k * 4 ^ j * 100000000 * ((w + 1 : ℕ) : ℝ) ^ η ≤ (w : ℝ) ^ s := by
  let η := s / 15
  have hη : 0 < η := by positivity
  refine ⟨η, hη, ?_⟩
  have ht : Tendsto (fun w : ℕ => (w : ℝ) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 5, ht.eventually_ge_atTop (8 ^ 6 * 100000000)] with w hw hlarge
  intro v hv
  have hw' : 5 ≤ (w : ℝ) := by exact_mod_cast hw
  let A := ((w + 1 : ℕ) : ℝ) ^ η
  let z := (w : ℝ) ^ η
  have hA : 1 ≤ A := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ w + 1)) hη.le
  have hAz : A ≤ z ^ 2 := by
    calc
      A ≤ ((w : ℝ) ^ 2) ^ η := Real.rpow_le_rpow (by positivity) (by push_cast; nlinarith) hη.le
      _ = z ^ 2 := by
        rw [← Real.rpow_natCast_mul (by positivity), mul_comm, Real.rpow_mul_natCast (by positivity)]
  obtain ⟨l, hlo, hhi⟩ := exists_nat_pow_near (by linarith : 1 ≤ 4 * A) (by norm_num : 1 < (2 : ℝ))
  let k := l + 1
  have hk : (2 : ℝ) ^ k ≤ 8 * A := by unfold k; rw [pow_succ]; linarith
  have hwidth : 2 * (w + v) ≤ 2 ^ k * (w + 1) := by
    rw [Real.rpow_add (by positivity), Real.rpow_one] at hv
    change (v : ℝ) ≤ ((w + 1 : ℕ) : ℝ) * A at hv
    have hp := mul_le_mul_of_nonneg_right hhi.le (by positivity : (0 : ℝ) ≤ w + 1)
    have : (2 : ℝ) * (w + v) ≤ (2 : ℝ) ^ k * (w + 1) := by
      push_cast at hv
      unfold k
      nlinarith only [hw', hv, hp, hA]
    exact_mod_cast this
  refine ⟨k, 2 * k, hwidth, lift_range hw hwidth, ?_⟩
  calc
    _ = ((2 : ℝ) ^ k) ^ 6 * 100000000 * A := by
      rw [pow_mul, ← mul_pow, pow_right_comm]
      norm_num [A]
    _ ≤ (8 * z ^ 2) ^ 6 * 100000000 * z ^ 2 := by
      gcongr
      exact hk.trans (by gcongr)
    _ = (8 ^ 6 * 100000000) * z ^ 14 := by ring
    _ ≤ z * z ^ 14 := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = (w : ℝ) ^ s := by
      rw [← pow_succ', ← Real.rpow_mul_natCast (by positivity : 0 ≤ (w : ℝ))]
      congr 1
      unfold η
      ring

end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-!
# Signed distinctness and permutation verification

Each row of the first list either remains real (weight `-1`) or
receives a dummy flag (weight `1`). If a row is absent from the
second list, summing over its flag gives zero in every characteristic.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable (F : Type) [Field F] {a b : Wire} (E : Val .bit → Val a → Val b)
  (hE : Function.Injective (Function.uncurry E))

include hE in
private theorem enc_eq (p q : Bool) (x y : Val a) :
    E p x = E q y ↔ p = q ∧ x = y := by
  exact (hE.eq_iff (a := (p, x)) (b := (q, y))).trans Prod.ext_iff

open Classical in
private noncomputable def term (B : List (Val a)) (w : ℕ) (A : Val (tree w a)) (z : Val (tree w .bit)) : F :=
  sign F w z * if (B.map (E false)).Disjoint (flatten w (zipRows E w z A)) then 1 else 0

open Classical in
include hE in
private theorem sum_term (B : List (Val a)) (w : ℕ) (A : Val (tree w a)) :
    (∑ z, term F E B w A z) = if flatten w A ⊆ B then 1 else 0 := by
  induction w with
  | zero =>
    rw [Fintype.sum_bool]
    by_cases h : A ∈ B <;>
      simp [term, sign, flatten, zipRows, List.disjoint_singleton, enc_eq E hE, h]
  | succ w ih =>
    have split (z : Val (tree (w + 1) .bit)) :
        term F E B (w + 1) A z = term F E B w A.1 z.1 * term F E B w A.2 z.2 := by
      simp only [term, sign, flatten, zipRows, List.disjoint_append_right, ite_and,
        mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
      simp only [← ite_and, and_comm]
    simp_rw [split]
    rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, ih, ih]
    simp only [flatten, List.append_subset, ite_and, ite_mul, one_mul, zero_mul]

include hE in
/-- A signed test of distinctness on twice as many rows checks a permutation.
The first list must have distinct rows, as it does when tagged by position. -/
theorem cancel (w : ℕ) (A B : Val (tree w a)) (hA : (flatten w A).Nodup) :
    (∑ z : Val (tree w .bit), sign F w z *
      (if (flatten (w + 1) (tested E w A B z)).Nodup then 1 else 0)) = permuted F w A B := by
  classical
  have row (p q : Bool) (x y : Val a) (h : E p x = E q y) : x = y :=
    ((enc_eq E hE p q x y).mp h).2
  have inj : Function.Injective (E false) := row false false
  have hd (z : Val (tree w .bit)) := nodup_zipRows E row w z A hA
  simp only [tested, flatten, flatten_mapRows, List.nodup_append', List.nodup_map_iff inj,
    hd, true_and, permuted]
  by_cases hB : (flatten w B).Nodup
  · have hp : (flatten w B).Perm (flatten w A) ↔ flatten w A ⊆ flatten w B :=
      ⟨fun h => h.symm.subset,
       fun h => ((hA.subperm h).perm_of_length_le (by simp [length_flatten])).symm⟩
    simpa only [hB, true_and, hp, term] using sum_term F E hE (flatten w B) w A
  · have hp : ¬ (flatten w B).Perm (flatten w A) := fun h => hB (h.symm.nodup hA)
    simp [hB, hp]

end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-! # Tagged permutation queries from element distinctness -/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {F : Type} [Field F] {a b : Wire} {w t m : ℕ}

private def distinct (F : Type) [Field F] (w : ℕ) (a : Wire) (x : Val (tree w a))
    (_ : Val .unit) : F :=
  if (flatten w x).Nodup then 1 else 0

private theorem batch_distinct (h : Realizes F w t m) :
    Batch (distinct F w (word (2 * w))) t m := by
  obtain ⟨v, hv, rfl⟩ := h
  refine ⟨v, Nat.le_add_right _ _, hv.rewire (.listCopies w t) (.unitCopies t) ?_⟩
  intro x y
  exact power_distinct F w t x _

private theorem prepare_comp (E : Val .bit → Val (row w a) → Val b)
    (h : Function.Injective (Function.uncurry E)) :
    (fun x y => ∑ z, prepare E F x z * distinct F (w + 1) b z y) = tag F w a := by
  funext x y
  simp only [prepare, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ite_mul, one_mul, zero_mul, ← Finset.mul_sum, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  exact cancel F E h w _ _ (label_nodup w x.1)

/-- A network testing `t` lists on independent inputs gives one checking
`t` independently specified permutations. The extra cost is linear in
the total input length and does not depend on the coefficient field. -/
theorem tag_of_distinct (h : Realizes F (w + 1) t m) :
    Batch (tag F w (word (w + 1))) t (m + 3 * t * listBits (w + 1)) := by
  obtain ⟨f, hf, hi⟩ := Rewire.exists_of_width
    (a := .pair .bit (row w (word (w + 1)))) (b := word (2 * (w + 1)))
    (by simp only [wd, wd_word]; omega)
  let E : Val .bit → Val (row w (word (w + 1))) → Val (word (2 * (w + 1))) := fun i x => f (i, x)
  obtain ⟨v, hv, hg⟩ := prepare_net (F := F) E hf
  have hp := (Batch.of_net hg t).comp (batch_distinct h)
  rw [prepare_comp E hi] at hp
  apply hp.mono
  calc
    t * v + m ≤ t * (2 ^ w * (5 * w + 6 * wd (word (w + 1)) + 4)) + m :=
      Nat.add_le_add_right (Nat.mul_le_mul_left t hv) m
    _ ≤ m + 3 * t * listBits (w + 1) := by
      rw [wd_word, listBits, pow_succ]
      ring_nf
      omega

end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-! # Restricting a batch by fixing extra inputs to accepting constants -/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {F : Type} [Field F] {a : Wire} {s t m : ℕ}

private def repeatRow (x : Val a) : (n : ℕ) → Val (copies a n)
  | 0 => ()
  | n + 1 => (x, repeatRow x n)

private theorem repeat_ok {k : Val a → Val .unit → F} {x : Val a} (h : k x () = 1)
    (n : ℕ) : power k n (repeatRow x n) (unitCopies n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [power, repeatRow, unitCopies, h, ih, mul_one]

theorem Batch.truncate {k : Val a → Val .unit → F} (h : Batch k t m) (hst : s ≤ t)
    (x : Val a) (hx : k x () = 1) : Batch k s (m + t * wd a) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hst
  obtain ⟨v, hv, h⟩ := h
  let z := repeatRow x u
  have p := ((literal_net F _ z).par (DNet.id F (copies a s))).pre
    ((Rewire.unit' _).comp (.swap _ _))
  obtain ⟨n, hn, g⟩ := p.post (.appendCopies a u s)
  have out := (Rewire.copiesUnit s).comp (Rewire.unitCopies (s + u))
  refine ⟨n + v, ?_, ?_⟩
  · simp only [wd_copies, add_mul] at hn ⊢
    omega
  · convert g.comp (h.post out) using 1
    funext y r
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← eq_unitCopies _ (appendCopies .unit u s (unitCopies u, r)), power_append]
    rw [repeat_ok hx, one_mul]

theorem tag_truncate {w : ℕ} (h : Batch (tag F w a) t m) (hst : s ≤ t) :
    Batch (tag F w a) s (m + t * 2 ^ w * (w + 2 * wd a)) := by
  let A := (bits (tree w a)).symm (fun _ => false)
  have h' := h.truncate hst (A, label w A) (by simp [tag, permuted])
  apply h'.mono
  simp only [wd, wd_tree, row, wd_word]
  exact le_of_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-! # Transferring a distinctness batch to one large permutation verifier -/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {F : Type} [Field F] {w t m v k j : ℕ}

private theorem bit_cost (h : Realizes F (w + 1) t m) :
    t * 2 ^ w * (w + 1) ≤ m := by
  obtain ⟨z, _, rfl⟩ := h
  rw [listBits, pow_succ]
  ring_nf
  omega

private theorem small_tags (h : Realizes F (w + 1) t m) (ht : 2 ^ v ≤ t) :
    Batch (tag F w (word (w + 1))) (2 ^ v) (5 * m) := by
  apply (tag_truncate (tag_of_distinct h) ht).mono
  obtain ⟨z, _, rfl⟩ := h
  rw [wd_word, listBits, pow_succ]
  ring_nf
  omega

private theorem slice_cost (k : ℕ) : (6 * k + 2) * 2 ^ k ≤ 8 * 4 ^ k := by
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  calc
    _ ≤ (8 * 2 ^ k) * 2 ^ k := by gcongr; omega
    _ = _ := by rw [mul_assoc, ← mul_pow]; rfl

/-- The replication exponent is `v`. Using `2^k` slices and `j` column
lifts costs at most a constant times `4^k 4^j` times the initial size. -/
theorem transfer (h : Realizes F (w + 1) t m) (hw : 2 ≤ w) (ht : 2 ^ v ≤ t)
    (hk : 2 * (w + v) ≤ 2 ^ k * (w + 1)) (hj : 2 ^ j * (w + v - 2) ≤ 3 ^ j * (w - 2)) :
    ∃ l ≤ 1000000 * 4 ^ k * 4 ^ j * m,
      Net F (inputs (w + v) (word (w + v))) .unit (tag F (w + v) (word (w + v))) l := by
  let a := row (w + v) (word (w + v))
  have hwidth : wd a = 2 * (w + v) := by simp only [a, wd, wd_word]; omega
  have hpow : 2 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by decide) _
  have hunit : w + 1 ≤ 4 ^ k * (w + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  have hwide : wd a ≤ 4 ^ k * (w + 1) := hwidth.le.trans
    (hk.trans (Nat.mul_le_mul_right _ hpow))
  have hbits : 2 ^ v * 2 ^ w * (w + 1) ≤ m :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ht)).trans (bit_cost h)
  have htag : Batch (tag F w a) (2 ^ v) (21 * 4 ^ k * m) := by
    refine (tag_slices (small_tags h ht) k (by rw [wd_word, hwidth]; exact hk)).mono ?_
    rw [wd_word]
    calc
      _ ≤ 4 ^ k * (5 * m) + (8 * 4 ^ k) * 2 ^ v * 2 ^ w * (2 * (w + 1)) := by
        have := slice_cost k
        gcongr
        omega
      _ = 4 ^ k * (5 * m) + 16 * 4 ^ k * (2 ^ v * 2 ^ w * (w + 1)) := by ring
      _ ≤ 4 ^ k * (5 * m) + 16 * 4 ^ k * m := by gcongr
      _ = _ := by ring
  obtain ⟨o, cmp⟩ := exists_comparator F a
  let : LinearOrder (Val a) := o
  have hs := Columns.sort_lift_iterate hw j hj (sort_of_tag htag cmp)
  have H : wd a + w + 100 * (wd a + 1) + 1 ≤ 203 * (4 ^ k * (w + 1)) := by omega
  have hs' := hs.mono (n := 203021 * 4 ^ k * 4 ^ j * m) (by
    calc
      _ ≤ 4 ^ j * (21 * 4 ^ k * m + 1000 * 2 ^ v * 2 ^ w * (203 * (4 ^ k * (w + 1)))) := by gcongr
      _ = 4 ^ j * (21 * 4 ^ k * m + 203000 * 4 ^ k * (2 ^ v * 2 ^ w * (w + 1))) := by ring
      _ ≤ 4 ^ j * (21 * 4 ^ k * m + 203000 * 4 ^ k * m) := by gcongr
      _ = _ := by ring)
  obtain ⟨l, hl, hl'⟩ := tag_of_sort hs'
  refine ⟨l, hl.trans ?_, hl'⟩
  have he : w + v + wd (word (w + v)) ≤ 4 ^ k * (w + 1) := by rw [wd_word]; omega
  calc
    _ ≤ 2 * (203021 * 4 ^ k * 4 ^ j * m) + 3 * 2 ^ (w + v) * (4 ^ k * (w + 1)) := by gcongr
    _ = 2 * (203021 * 4 ^ k * 4 ^ j * m) + 3 * 4 ^ k * (2 ^ v * 2 ^ w * (w + 1)) := by rw [pow_add]; ring
    _ ≤ 2 * (203021 * 4 ^ k * 4 ^ j * m) + 3 * 4 ^ k * (4 ^ j * m) := by
      have : m ≤ 4 ^ j * m := Nat.le_mul_of_pos_left _ (by positivity)
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hbits.trans this)) _
    _ ≤ _ := by ring_nf; omega

end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-!
# From tagged permutations to independent lists

A batch of size `t` gives one permutation verifier on
`2^(w + floor (log₂ t))` rows at list width `w+1`. The cost of
lifting the sort and slicing the payload is absorbed by the assumed
power-of-logarithm lower bound.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

open Filter

private theorem space {w v t : ℕ} (hw : 2 ≤ w) (ht : t < 2 ^ (v + 1)) :
    t * listBits (w + 1) < 100 * 2 ^ (w + v) * (w + v) := by
  calc
    _ < 2 ^ (v + 1) * listBits (w + 1) := Nat.mul_lt_mul_of_pos_right ht (by unfold listBits; positivity)
    _ = 2 ^ (w + v) * (8 * (w + 1)) := by unfold listBits; rw [pow_add, pow_add, pow_add]; ring
    _ ≤ 2 ^ (w + v) * (100 * (w + v)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

variable {F : Type} [Field F]

/-- The exact-network lower bound with a superpolynomial range of batch sizes. -/
theorem manyList_full (h : Hard F) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ,
      1 ≤ t → (t : ℝ) ≤ (2 : ℝ) ^ ((w : ℝ) ^ (1 + η)) → Realizes F w t m →
      (t : ℝ) * listBits w * (w : ℝ) ^ η < m := by
  obtain ⟨σ, hs, hlower⟩ := h
  obtain ⟨η, hη, hparam⟩ := parameters hs
  obtain ⟨W, hW⟩ := eventually_atTop.mp (hlower.and hparam)
  refine ⟨η, hη, ?_⟩
  filter_upwards [eventually_ge_atTop (W + 3)] with n hn t m ht hmax hnet
  obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let v := Nat.log 2 t
  have hv : 2 ^ v ≤ t := Nat.pow_log_le_self _ (by omega)
  have hv' : (v : ℝ) ≤ ((w + 1 : ℕ) : ℝ) ^ (1 + η) := by
    apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp
    rw [Real.rpow_natCast]
    exact (show (2 : ℝ) ^ v ≤ t by exact_mod_cast hv).trans hmax
  obtain ⟨k, j, hk, hj, he⟩ := (hW w (by omega)).2 v hv'
  obtain ⟨l, hl, hperm⟩ := transfer hnet (by omega) hv hk hj
  have hsize : (t : ℝ) * listBits (w + 1) < 100 * (2 : ℝ) ^ (w + v) * (w + v : ℕ) := by
    exact_mod_cast space (by omega : 2 ≤ w) (Nat.lt_pow_succ_log_self (by decide : 1 < 2) t)
  let C := 1000000 * (4 : ℝ) ^ k * 4 ^ j
  have hC : 0 < C := by unfold C; positivity
  apply (mul_lt_mul_iff_right₀ hC).mp
  calc
    _ < C * (100 * (2 : ℝ) ^ (w + v) * (w + v : ℕ) * ((w + 1 : ℕ) : ℝ) ^ η) := by gcongr
    _ = (2 : ℝ) ^ (w + v) * (w + v : ℕ) *
        ((4 : ℝ) ^ k * 4 ^ j * 100000000 * ((w + 1 : ℕ) : ℝ) ^ η) := by unfold C; ring
    _ ≤ (2 : ℝ) ^ (w + v) * (w + v : ℕ) * (w : ℝ) ^ σ := by gcongr
    _ ≤ (2 : ℝ) ^ (w + v) * (w + v : ℕ) * ((w + v : ℕ) : ℝ) ^ σ := by gcongr; omega
    _ ≤ l := (hW (w + v) (by omega)).1 l hperm
    _ ≤ C * m := by unfold C; exact_mod_cast hl

/-- Restrict the batch sizes to those needed by the compression iteration. -/
theorem manyList_of_tag (h : Hard F) : ManyList (Realizes F) := by
  obtain ⟨η, he, hl⟩ := manyList_full h
  refine ⟨η, he, ?_⟩
  have grow := (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  filter_upwards [hl, eventually_ge_atTop 1, grow.eventually_ge_atTop 3] with w hlow hw hg t m ht hi hr
  have hw' : 0 < (w : ℝ) := by exact_mod_cast hw
  have ht' : t ≤ 2 ^ (w + w + w) := by
    apply hi.trans
    unfold listBits
    rw [pow_add, pow_add]
    gcongr
    · exact Nat.le_pow hw
    · exact Nat.lt_two_pow_self.le
  have hmax : (t : ℝ) ≤ (2 : ℝ) ^ ((w : ℝ) ^ (1 + η)) := by
    calc
      _ ≤ (2 : ℝ) ^ (w + w + w) := by exact_mod_cast ht'
      _ ≤ _ := by
        rw [← Real.rpow_natCast, Real.rpow_add hw', Real.rpow_one]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        push_cast
        change 3 ≤ (w : ℝ) ^ η at hg
        nlinarith
  exact (hlow t m ht hmax hr).trans_le (by linarith)

end OAI.LinearAlgebra.MatrixExponent.Tagged
end
