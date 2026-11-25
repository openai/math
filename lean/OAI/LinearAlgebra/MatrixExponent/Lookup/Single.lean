import OAI.LinearAlgebra.MatrixExponent.Lookup.Counter
import OAI.LinearAlgebra.MatrixExponent.Lookup.Scan
import OAI.LinearAlgebra.MatrixExponent.Diagram.Wide

section
/-! # Uniqueness of the guessed multiplicities and their product -/

namespace OAI.LinearAlgebra.MatrixExponent.Lookup

variable {F : Type} [Field F]

def expected (a : Wire) (xs : List (Val a)) :
    (l : ℕ) → Val (tree l a) → Val (tree l (count a))
  | 0, z => bits _ (xs.count z)
  | l + 1, z => (expected a xs l z.1, expected a xs l z.2)

def weight (a : Wire) (f : Val a → F) :
    (l : ℕ) → Val (tree l a) → Val (tree l (count a)) → F
  | 0, z, c => f z ^ value _ c
  | l + 1, z, c => weight a f l z.1 c.1 * weight a f l z.2 c.2

private theorem fold_queries (a : Wire) (z : Val a) (ok : Bool) (k : ℕ) :
    (List.replicate k (query a z)).foldl (step a) (ok, zero _) = (ok, bits _ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', List.foldl_append, ih]
    simp [step, query, bits, Function.iterate_succ_apply']

theorem fold_dict (a : Wire) (xs : List (Val a)) (l : ℕ)
    (z : Val (tree l a)) (c : Val (tree l (count a))) (ok : Bool) :
    ((flatten l (dict a l z c)).flatMap (group a xs)).foldl (step a) (ok, zero _) =
      (ok && decide (expected a xs l z = c), zero _) := by
  induction l generalizing ok with
  | zero =>
    simp only [flatten, dict, List.flatMap_singleton, group, List.foldl_append]
    rw [fold_queries a z ok]
    rfl
  | succ l ih =>
    simp only [flatten, dict, List.flatMap_append, List.foldl_append, ih, expected]
    simp [Prod.ext_iff, Bool.and_assoc]

private theorem product_counts (a : Wire) (xs zs : List (Val a)) (f : Val a → F)
    (hn : zs.Nodup) (hall : ∀ z, z ∈ zs) :
    (zs.map fun z => f z ^ xs.count z).prod = (xs.map f).prod := by
  rw [← List.prod_toFinset _ hn, Finset.prod_list_map_count xs f]
  symm
  apply Finset.prod_subset
  · exact fun i _ => List.mem_toFinset.mpr (hall i)
  · intro i _ hi
    rw [List.count_eq_zero_of_not_mem (mt List.mem_toFinset.mpr hi), pow_zero]

private theorem weight_expected (a : Wire) (f : Val a → F) (xs : List (Val a))
    (hxs : xs.length < 2 ^ (wd a + 1)) (l : ℕ) (z : Val (tree l a)) :
    weight a f l z (expected a xs l z) = ((flatten l z).map fun x => f x ^ xs.count x).prod := by
  induction l with
  | zero =>
    simp only [weight, expected, flatten, List.map_singleton, List.prod_singleton]
    rw [value_bits (List.count_le_length.trans_lt hxs)]
  | succ l ih =>
    simp only [weight, expected, flatten, List.map_append, List.prod_append, ih]

theorem weight_lookup (a : Wire) (f : Val a → F) (x z : Val (tree (wd a) a))
    (hn : (flatten (wd a) z).Nodup) (hall : ∀ y : Val a, y ∈ flatten (wd a) z) :
    weight a f (wd a) z (expected a (flatten (wd a) x) (wd a) z) =
      ((flatten (wd a) x).map f).prod := by
  have len (l : ℕ) (x : Val (tree l a)) : (flatten l x).length = 2 ^ l := by
    induction l with
    | zero => rfl
    | succ l ih => simp [flatten, ih, pow_succ, mul_two]
  have hxs : (flatten (wd a) x).length < 2 ^ (wd a + 1) := by
    rw [len, pow_succ]
    have := pow_pos (by decide : 0 < 2) (wd a)
    omega
  rw [weight_expected a f _ hxs, product_counts _ _ _ _ hn hall]

end OAI.LinearAlgebra.MatrixExponent.Lookup
end

section
/-!
# Simultaneous evaluation at all query positions

One sorting call handles query rows and a fixed dictionary carrying
guessed counts. The trace contracts the count wires with binary weights.
Exactly one assignment passes the scan, including in positive characteristic.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Lookup

variable (K : Type) [Field K] (a : Wire)

theorem queries_net (l : ℕ) :
    DNet K (tree l a) (tree l (row a)) (queries a l) (2 ^ l * wd (row a)) := by
  induction l with
  | zero =>
    rw [pow_zero, one_mul]
    exact ((DNet.id K a).par (const_net K (state a) (false, zero _))).pre (.unit' _)
  | succ l ih =>
    rw [pow_succ, mul_two, add_mul]
    exact ih.par ih

theorem dict_net (l : ℕ) (z : Val (tree l a)) :
    DNet K (tree l (count a)) (tree l (row a)) (dict a l z) (2 ^ l * wd (row a)) := by
  induction l with
  | zero =>
    rw [pow_zero, one_mul]
    have payload := ((const_net K .bit true).par (DNet.id K (count a))).pre
      ((Rewire.unit' _).comp (.swap _ _))
    exact ((const_net K a z).par payload).pre ((Rewire.unit' _).comp (.swap _ _))
  | succ l ih =>
    rw [pow_succ, mul_two, add_mul]
    exact (ih z.1).par (ih z.2)

theorem weights_net (f : Val a → K) (l : ℕ) (z : Val (tree l a)) :
    Net K .unit (tree l (count a)) (fun _ y => weight a f l z y) (2 ^ l * (wd a + 1)) := by
  induction l with
  | zero =>
    rw [pow_zero, one_mul]
    exact weight_net K _ (f z)
  | succ l ih =>
    rw [pow_succ, mul_two, add_mul]
    exact ((ih z.1).par (ih z.2)).pre (.unit' .unit)

private theorem batch (f : Val a → K) (z : Val (tree (wd a) a))
    (hn : (flatten (wd a) z).Nodup) (hall : ∀ y : Val a, y ∈ flatten (wd a) z)
    {sort : Val (tree (wd a + 1) (row a)) → Val (tree (wd a + 1) (row a))} {m : ℕ}
    (hs : DNet K (tree (wd a + 1) (row a)) (tree (wd a + 1) (row a)) sort m)
    (he : ∀ x c, flatten (wd a + 1) (sort (queries a (wd a) x, dict a (wd a) z c)) =
      (flatten (wd a) (dict a (wd a) z c)).flatMap (group a (flatten (wd a) x))) :
    ∃ v ≤ m + 2006 * 2 ^ (wd a) * (1 + wd a),
      Net K (tree (wd a) a) .unit (fun x _ => ((flatten (wd a) x).map f).prod) v := by
  let t := wd a
  have prep := (queries_net K a t).par (dict_net K a t z)
  obtain ⟨v, hv, accept⟩ := (prep.comp hs).comp (scan_net K a (t + 1))
  have pin := Net.table (F := K) .bit .unit (fun b _ => if b then 1 else 0) (by decide)
  have test := accept.comp pin
  have valid : Net K (.pair (tree t a) (tree t (count a))) .unit
      (fun y _ => if expected a (flatten t y.1) t z = y.2 then 1 else 0) (v + 1) := by
    convert test using 1
    funext y u
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have eqn : scan a (t + 1) (sort (queries a t y.1, dict a t z y.2)) =
        decide (expected a (flatten t y.1) t z = y.2) := by
      unfold scan
      rw [he, fold_dict a (flatten t y.1) t z y.2 true, Bool.true_and]
    simp only [eqn, decide_eq_true_eq]
  have out := ((valid.par (weights_net K a f t z)).pre (.unit' _)).trace
  refine ⟨v + 1 + 2 ^ t * (wd a + 1), ?_, ?_⟩
  · have h2 : 0 < 2 ^ t := pow_pos (by decide) _
    simp only [wd, wd_word, pow_succ] at hv
    change v + 1 + 2 ^ t * (wd a + 1) ≤ m + 2006 * 2 ^ t * (1 + wd a)
    nlinarith only [h2, hv]
  · simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      t, weight_lookup a f _ z hn hall] using out

/-- The constant is uniform over extensions, table arities and entries. -/
theorem lookup_net {F : Type} [Field F] {p : ℝ} (hp : 1 ≤ p) (hs : Sorting F p) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Type) (_ : Field K) (_ : Algebra F K) (a : Wire) (f : Val a → K),
      ∃ v : ℕ, Net K (tree (wd a) a) .unit (fun x _ => ((flatten (wd a) x).map f).prod) v ∧
        (v : ℝ) ≤ C * (2 : ℝ) ^ wd a * (1 + (wd a : ℝ)) ^ p := by
  obtain ⟨C, hC⟩ := hs
  refine ⟨max C 0 + 2006, by linarith [le_max_right C 0], ?_⟩
  intro K _ _ a f
  obtain ⟨z, sort, m, hn, hall, ⟨w, hw, hsort⟩, hm, he⟩ := hC a
  have hsort' : DNet K (tree (wd a + 1) (row a)) (tree (wd a + 1) (row a)) sort m := by
    refine ⟨w, hw, ?_⟩
    simpa only [apply_ite (algebraMap F K), map_one, map_zero] using hsort.map (algebraMap F K)
  obtain ⟨v, hv, hnet⟩ := batch K a f z hn hall hsort' he
  refine ⟨v, hnet, ?_⟩
  have h : (1 + (wd a : ℝ)) ≤ (1 + (wd a : ℝ)) ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1 + (wd a : ℝ) by simp) hp
  calc
    (v : ℝ) ≤ m + 2006 * (2 : ℝ) ^ wd a * (1 + (wd a : ℝ)) := by exact_mod_cast hv
    _ ≤ C * (2 : ℝ) ^ wd a * (1 + (wd a : ℝ)) ^ p +
        2006 * (2 : ℝ) ^ wd a * (1 + (wd a : ℝ)) ^ p :=
      add_le_add hm (mul_le_mul_of_nonneg_left h (by positivity))
    _ = (C + 2006) * (2 : ℝ) ^ wd a * (1 + (wd a : ℝ)) ^ p := by ring
    _ ≤ _ := by gcongr; exact le_max_left _ _

end OAI.LinearAlgebra.MatrixExponent.Lookup
end
