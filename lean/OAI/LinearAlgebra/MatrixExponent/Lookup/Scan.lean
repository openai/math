import OAI.LinearAlgebra.MatrixExponent.Lookup.Defs
import OAI.LinearAlgebra.MatrixExponent.Lookup.Counter
import OAI.LinearAlgebra.MatrixExponent.CompareExchange
import OAI.LinearAlgebra.MatrixExponent.AdjacentDuplicates
import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortOne
import OAI.LinearAlgebra.MatrixExponent.BitonicMerge
import OAI.LinearAlgebra.MatrixExponent.Lookup.ShortTag
import Mathlib.Data.Finset.Sort

section
/-! # Grouping the queries gives a sorted permutation of the input rows -/

namespace OAI.LinearAlgebra.MatrixExponent.Lookup

private theorem flatten_queries (a : Wire) (l : ℕ) (x : Val (tree l a)) :
    flatten l (queries a l x) = (flatten l x).map (query a) := by
  induction l with
  | zero => rfl
  | succ l ih => simp [flatten, queries, ih]

private theorem dict_keys (a : Wire) (l : ℕ) (z : Val (tree l a))
    (c : Val (tree l (count a))) :
    (flatten l (dict a l z c)).map Prod.fst = flatten l z := by
  induction l with
  | zero => rfl
  | succ l ih => simp [flatten, dict, ih]

private theorem dict_marker (a : Wire) (l : ℕ) (z : Val (tree l a))
    (c : Val (tree l (count a))) (r : Val (row a))
    (hr : r ∈ flatten l (dict a l z c)) : r.2.1 = true := by
  induction l with
  | zero => rw [List.mem_singleton.mp hr]; rfl
  | succ l ih =>
    rcases List.mem_append.mp hr with hr | hr
    · exact ih _ _ hr
    · exact ih _ _ hr

private theorem perm_repeats (a : Wire) (xs zs : List (Val a)) (hn : zs.Nodup)
    (hall : ∀ y, y ∈ zs) :
    (zs.flatMap fun y => List.replicate (xs.count y) y).Perm xs := by
  apply List.perm_iff_count.mpr
  intro y
  rw [List.count_flatMap, ← List.sum_toFinset _ hn]
  simp [List.count_replicate, hall]

theorem group_perm (a : Wire) (l : ℕ) (x z : Val (tree l a)) (c : Val (tree l (count a)))
    (hn : (flatten l z).Nodup) (hall : ∀ y : Val a, y ∈ flatten l z) :
    ((flatten l (dict a l z c)).flatMap (group a (flatten l x))).Perm
      (flatten (l + 1) (a := row a) (queries a l x, dict a l z c)) := by
  let rs := flatten l (dict a l z c)
  let xs := flatten l x
  have h := (perm_repeats a xs (flatten l z) hn hall).map (query a)
  rw [← dict_keys a l z c, List.map_flatMap, List.flatMap_map] at h
  simp only [List.map_replicate] at h
  have p := List.flatMap_append_perm rs (fun r => List.replicate (xs.count r.1) (query a r.1))
    (fun r => [r])
  rw [flatten, flatten_queries]
  exact p.symm.trans (h.append (by simp [rs]))

private theorem key_eq (a : Wire) {xs : List (Val a)} {r q : Val (row a)}
    (h : q ∈ group a xs r) : q.1 = r.1 := by
  rcases List.mem_append.mp h with h | h
  · rw [List.eq_of_mem_replicate h]; rfl
  · rw [List.mem_singleton.mp h]

theorem group_sorted (a : Wire) [LinearOrder (Val a)] (l : ℕ) (x z : Val (tree l a))
    (c : Val (tree l (count a))) (R : Val (row a) → Val (row a) → Prop)
    (hr : ∀ i, R i i) (hq : ∀ y u, R (query a y) (y, true, u))
    (hkey : ∀ i j, i.1 < j.1 → R i j) (hs : (flatten l z).Pairwise (· < ·)) :
    ((flatten l (dict a l z c)).flatMap (group a (flatten l x))).Pairwise R := by
  refine List.pairwise_flatMap.mpr ⟨?_, ?_⟩
  · intro r hm
    have he := dict_marker a l z c r hm
    refine List.pairwise_append.mpr ⟨List.pairwise_replicate.mpr (.inr (hr _)), by simp, ?_⟩
    intro q hq' d hd
    rw [List.eq_of_mem_replicate hq', List.mem_singleton.mp hd]
    simpa only [← he, Prod.eta] using hq r.1 r.2.2
  · rw [← dict_keys a l z c, List.pairwise_map] at hs
    refine hs.imp fun h i hi j hj => hkey i j ?_
    rw [key_eq a hi, key_eq a hj]
    exact h

end OAI.LinearAlgebra.MatrixExponent.Lookup
end

section
/-!
# Scanning dictionary rows

Two adjacent blocks share only a counter and a validity bit. Joining their
networks along those wires avoids copying either block of rows.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Lookup

variable (F : Type) [Field F]

theorem const_net (a : Wire) (x : Val a) : DNet F .unit a (fun _ => x) (wd a) := by
  induction a with
  | unit => exact DNet.id F .unit
  | bit => exact DNet.table F _ _ _ (by decide)
  | pair a b ha hb => exact ((ha x.1).par (hb x.2)).pre (.unit' .unit)

theorem eq_net (n : ℕ) :
    DNet F (.pair (word n) (word n)) .bit (fun x => decide (x.1 = x.2)) (2 * n + 1) := by
  induction n with
  | zero => exact DNet.table F _ _ _ (by decide)
  | succ n ih =>
    have head := DNet.table F (.pair .bit .bit) .bit (fun x => decide (x.1 = x.2)) (by decide)
    have both := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 && x.2) (by decide)
    have h := ((head.par ih).pre (.middle .bit (word n) .bit (word n))).comp both
    convert h.mono (n := 2 * (n + 1) + 1) (by omega) using 1
    funext ⟨x, y⟩
    simp [Prod.ext_iff]

private theorem step_net (a : Wire) :
    DNet F (.pair (state a) (row a)) (state a) (fun x => step a x.1 x.2)
      (500 * (1 + wd a)) := by
  have old := DNet.fst F (state a) (row a)
  have payload := (DNet.snd F (state a) (row a)).comp (DNet.snd F a (state a))
  have flag := DNet.fst F .bit (count a)
  have counter := DNet.snd F .bit (count a)
  have check := ((old.comp counter).pair (payload.comp counter)).comp (eq_net F (wd a + 1))
  have both := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 && x.2) (by decide)
  have reset := (DNet.discard F (.pair (state a) (row a))).comp
    (const_net F (count a) (zero _))
  have yes := (((old.comp flag).pair check).comp both).pair reset
  have no := old.comp ((DNet.id F .bit).par (inc_net F (wd a + 1)))
  have h := ((yes.pair no).pair (payload.comp flag)).comp (selectWord F (wd a + 2))
  exact h.mono (by simp only [wd, wd_word]; omega)

theorem fold_net {a s : Wire} {f : Val s → Val a → Val s} {m : ℕ}
    (h : DNet F (.pair s a) s (fun x => f x.1 x.2) m) (l : ℕ) :
    DNet F (.pair s (tree l a)) s (fun x => (flatten l x.2).foldl f x.1) (2 ^ l * m) := by
  induction l with
  | zero => simpa [flatten] using h
  | succ l ih =>
    have left := ih.post ((Rewire.unit' s).comp (.swap _ _))
    have h' := ((left.plug ih).pre (.assoc' _ _ _)).post ((Rewire.swap _ _).comp (.unit _))
    simpa only [flatten, List.foldl_append, pow_succ, mul_two, add_mul] using h'

theorem scan_net (a : Wire) (l : ℕ) :
    DNet F (tree l (row a)) .bit (scan a l) (1000 * 2 ^ l * (1 + wd a)) := by
  have start := const_net F (state a) (true, zero _)
  have seed := (start.par (DNet.id F (tree l (row a)))).pre
    ((Rewire.unit' _).comp (.swap _ _))
  have h := (seed.comp (fold_net F (step_net F a) l)).comp (DNet.fst F .bit (count a))
  apply h.mono
  simp only [wd_tree, wd, wd_word]
  have hp : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by decide)
  nlinarith [Nat.mul_le_mul_right (wd a) hp]

end OAI.LinearAlgebra.MatrixExponent.Lookup
end

/-!
# Ordering the dictionary and query rows

Read a key's wire positions in a fixed order. After the key comes the
dictionary marker, then the count payload. The marker places every query
before the dictionary row for that same key.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Lookup

private theorem key_encoding (a : Wire) :
    ∃ f, Rewire a (word (wd a)) f ∧ Function.Injective f :=
  Rewire.exists_of_width (wd_word _).symm

abbrev keyOrder (a : Wire) : LinearOrder (Val a) :=
  LinearOrder.lift' (key_encoding a).choose (key_encoding a).choose_spec.2

abbrev rowOrder (a : Wire) : LinearOrder (Val (row a)) :=
  @Prod.Lex.instLinearOrder _ _ (keyOrder a) (wordOrder (wd a + 2))

theorem row_key (a : Wire) (i j : Val (row a)) (h : (keyOrder a).lt i.1 j.1) :
    (rowOrder a).le i j := by
  exact (@Prod.Lex.toLex_le_toLex _ _ (keyOrder a).toLT (wordOrder (wd a + 2)).toLE i j).mpr (.inl h)

theorem row_query (a : Wire) (y : Val a) (u : Val (count a)) :
    (rowOrder a).le (query a y) (y, true, u) := by
  refine (@Prod.Lex.toLex_le_toLex _ _ (keyOrder a).toLT (wordOrder (wd a + 2)).toLE
    (query a y) (y, true, u)).mpr (.inr ⟨rfl, ?_⟩)
  exact (@Prod.Lex.toLex_le_toLex _ _ _ (wordOrder (wd a + 1)).toLE
    (false, zero (wd a + 1)) (true, u)).mpr (.inl (show false < true by decide))

theorem row_compare (F : Type) [Field F] (a : Wire) :
    letI := rowOrder a
    DNet F (.pair (row a) (row a)) .bit (fun x => decide (x.1 < x.2))
      (10000 * (wd a + 1)) := by
  let _ := keyOrder a
  let _ := wordOrder (wd a + 2)
  have h := (key_encoding a).choose_spec.1
  have keys : DNet F (.pair a a) .bit (fun x => decide (x.1 < x.2)) (100 * (wd a + 1)) :=
    (compare_lt F (wd a)).pre (h.par h)
  exact (Tagged.lex_compare keys (compare_lt F (wd a + 2))).mono (by omega)

end OAI.LinearAlgebra.MatrixExponent.Lookup
end

section
/-!
# From tagged permutations to sorting dictionary and query rows

At height `w=t+1` the payload has exactly `2w` bits. A sort on whole
rows suffices since the query payloads are all zero and the dictionary
has only one row for each address.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Lookup

private theorem card_val (a : Wire) : Fintype.card (Val a) = 2 ^ wd a := by
  induction a with
  | bit => exact Fintype.card_bool
  | unit => exact Fintype.card_unit
  | pair a b ha hb => simp [Val, wd, pow_add, ha, hb]

theorem as_tree {a : Wire} (l : ℕ) (xs : List (Val a)) (h : xs.length = 2 ^ l) :
    ∃ x : Val (tree l a), flatten l x = xs := by
  induction l generalizing xs with
  | zero =>
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp h
    exact ⟨y, rfl⟩
  | succ l ih =>
    rw [pow_succ] at h
    obtain ⟨x, hx⟩ := ih (xs.take (2 ^ l)) (by rw [List.length_take, h]; omega)
    obtain ⟨y, hy⟩ := ih (xs.drop (2 ^ l)) (by rw [List.length_drop, h]; omega)
    exact ⟨(x, y), by simp [flatten, hx, hy]⟩

theorem ordered_keys (a : Wire) [LinearOrder (Val a)] :
    ∃ z : Val (tree (wd a) a), (flatten (wd a) z).Nodup ∧
      (∀ y : Val a, y ∈ flatten (wd a) z) ∧ (flatten (wd a) z).Pairwise (· < ·) := by
  let s : Finset (Val a) := Finset.univ
  obtain ⟨z, hz⟩ := as_tree (wd a) (s.sort (· ≤ ·)) (by simp [s, card_val])
  refine ⟨z, ?_⟩
  rw [hz]
  exact ⟨s.sort_nodup _, by simp [s], s.sortedLT_sort.pairwise⟩

theorem sort_dict (a : Wire) [LinearOrder (Val a)] [L : LinearOrder (Val (row a))]
    (hq : ∀ y u, L.le (query a y) (y, true, u)) (hk : ∀ i j : Val (row a), i.1 < j.1 → L.le i j) :
    ∃ z : Val (tree (wd a) a), (flatten (wd a) z).Nodup ∧
      (∀ y : Val a, y ∈ flatten (wd a) z) ∧ ∀ x c,
      flatten (wd a + 1) (sortTree (a := row a) (wd a + 1) (queries a (wd a) x, dict a (wd a) z c)) =
        (flatten (wd a) (dict a (wd a) z c)).flatMap (group a (flatten (wd a) x)) := by
  obtain ⟨z, hn, hall, hs⟩ := ordered_keys a
  refine ⟨z, hn, hall, fun x c => ?_⟩
  have g := group_sorted a (wd a) x z c L.le L.le_refl hq hk hs
  let input : Val (tree (wd a + 1) (row a)) := (queries a (wd a) x, dict a (wd a) z c)
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ => L.le_antisymm _ _)
    (sortTree_sorted _ input) g ((sortTree_perm _ input).trans (group_perm _ _ _ _ _ hn hall).symm)

private theorem cost {p C : ℝ} (hp : 1 ≤ p) {t m : ℕ}
    (hm : (m : ℝ) ≤ C * (2 : ℝ) ^ (t + 1) * ((t + 1 : ℕ) : ℝ) ^ p) :
    (↑(4 * m + 10000 * 2 ^ (t + 1) * ((t + 1) + 10000 * (t + 1) + 1) : ℕ) : ℝ) ≤
      (8 * C + 200040000) * (2 : ℝ) ^ t * (1 + (t : ℝ)) ^ p := by
  push_cast at hm ⊢
  rw [pow_succ, add_comm (t : ℝ) 1] at hm ⊢
  have h : 1 + (t : ℝ) ≤ (1 + (t : ℝ)) ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1 + (t : ℝ) by simp) hp
  have e : (1 + (t : ℝ)) + 10000 * (1 + t) + 1 ≤ 10002 * (1 + (t : ℝ)) ^ p := by linarith
  have hmul := mul_le_mul_of_nonneg_left e (by positivity : (0 : ℝ) ≤ 2 ^ t)
  linarith

theorem sorting_of_tag {F : Type} [Field F] {p : ℝ} (hp : 1 ≤ p) (h : ShortTag F p) :
    Sorting F p := by
  obtain ⟨C, hC⟩ := h
  refine ⟨8 * C + 200040000, fun a => ?_⟩
  let t := wd a
  let _ := keyOrder a
  let _ := rowOrder a
  obtain ⟨z, hn, hall, he⟩ := sort_dict a (row_query a) (row_key a)
  obtain ⟨m, htag, hm⟩ := hC (t + 1) (by omega)
  have hw : wd (row a) ≤ 4 * (t + 1) := by simp [wd, t]; omega
  have hs := Tagged.sort_one htag hw (row_compare F a)
  exact ⟨z, _, _, hn, hall, hs, cost hp hm, he⟩

end OAI.LinearAlgebra.MatrixExponent.Lookup
end
