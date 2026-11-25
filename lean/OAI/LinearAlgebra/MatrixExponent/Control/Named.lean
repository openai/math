import OAI.LinearAlgebra.MatrixExponent.Batcher
import OAI.LinearAlgebra.MatrixExponent.BitonicMerge
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Control.Address
import OAI.LinearAlgebra.MatrixExponent.Lookup.Scan
import OAI.LinearAlgebra.MatrixExponent.Network.Dense
import OAI.LinearAlgebra.MatrixExponent.Install.Weight

section
/-!
# Checking agreement on repeated addresses

Sort by address and then by bit. Complement the bit on every row and
test whether the list is still sorted. This holds exactly when all
rows with the same address agree.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Control

abbrev entry (h : ℕ) := Wire.pair (word h) .bit

def Agree {h : ℕ} (xs : List (Val (entry h))) : Prop :=
  ∀ i ∈ xs, ∀ j ∈ xs, i.1 = j.1 → i.2 = j.2

private local instance order (h : ℕ) : LinearOrder (Val (entry h)) :=
  @Prod.Lex.instLinearOrder _ _ (wordOrder h) inferInstance

private local instance (h : ℕ) : LT (Val (entry h)) := (order h).toLT
private local instance (h : ℕ) : LE (Val (entry h)) := (order h).toLE
private local instance (h : ℕ) : Min (Val (entry h)) := (order h).toMin
private local instance (h : ℕ) : Max (Val (entry h)) := (order h).toMax
private local instance (h : ℕ) : Preorder (Val (entry h)) := (order h).toPreorder

private def flip (h : ℕ) (i : Val (entry h)) : Val (entry h) := (i.1, !i.2)

private theorem le_iff {h : ℕ} (i j : Val (entry h)) :
    i ≤ j ↔ i.1 < j.1 ∨ i.1 = j.1 ∧ i.2 ≤ j.2 :=
  Prod.Lex.toLex_le_toLex

private theorem both {h : ℕ} (i j : Val (entry h)) (ho : i ≤ j) :
    flip h i ≤ flip h j ↔ (i.1 = j.1 → i.2 = j.2) := by
  rw [le_iff] at ho ⊢
  rcases ho with ho | ⟨he, hb⟩
  · simp [flip, ho, ho.ne]
  · simp only [flip, he, lt_self_iff_false, true_and, false_or, true_implies]
    cases x : i.2 <;> cases y : j.2 <;> simp [x, y] at *
    all_goals exact (by decide : ¬(true ≤ false)) hb

private theorem agree_iff {h : ℕ} (xs : List (Val (entry h))) (hs : xs.Pairwise (· ≤ ·)) :
    (xs.map (flip h)).Pairwise (· ≤ ·) ↔ Agree xs := by
  rw [List.pairwise_map]
  constructor
  · intro ht
    have hp := (hs.and ht).imp (fun e => (both _ _ e.1).mp e.2)
    intro i hi j hj he
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hi
    obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hj
    rcases lt_trichotomy a b with h | rfl | h
    · exact List.pairwise_iff_getElem.mp hp a b ha hb h he
    · rfl
    · exact (List.pairwise_iff_getElem.mp hp b a hb ha h he.symm).symm
  · intro ht
    exact hs.imp_of_mem fun hi hj h => (both _ _ h).mpr (ht _ hi _ hj)

variable (F : Type) [Field F] (h : ℕ)

private theorem compare_net : DNet F (.pair (entry h) (entry h)) .bit
    (fun x => decide (x.1 < x.2)) (250 * (h + 1)) := by
  have bit := DNet.table F (.pair .bit .bit) .bit (fun x => decide (x.1 < x.2)) (by decide)
  exact (Tagged.lex_compare (compare_lt F h) bit).mono (by simp only [wd_word]; omega)

private theorem exchange : DNet F (.pair (entry h) (entry h)) (.pair (entry h) (entry h))
    (fun x => (min x.1 x.2, max x.1 x.2)) (500 * (h + 1)) := by
  let a := entry h
  have rev := Rewire.swap (word h) .bit
  have sel := ((selectWord F (h + 1)).pre ((rev.par rev).par (.id .bit))).post (.swap _ _)
  have cmp := (DNet.id F (.pair a a)).pair (compare_net F h)
  have net := cmp.comp (sel.pair (sel.pre ((Rewire.swap a a).par (.id .bit))))
  convert net.mono (n := 500 * (h + 1)) (by simp only [a, wd, wd_word]; omega) using 1
  funext ⟨x, y⟩
  by_cases ho : x < y
  · simp [ho, min_eq_left ho.le, max_eq_right ho.le]
  · simp [ho, min_eq_right (le_of_not_gt ho), max_eq_left (le_of_not_gt ho)]

theorem agree_net (w : ℕ) :
    ∃ f, DNet F (tree w (entry h)) .bit f (800 * 2 ^ w * (w + 1) ^ 2 * (h + 1)) ∧
      ∀ x, f x = true ↔ Agree (flatten w x) := by
  have flip_net : DNet F (entry h) (entry h) (flip h) (wd (word h) + 1) :=
    (DNet.id F (word h)).par (DNet.table F .bit .bit Bool.not (by decide))
  have sort := sortTree_net (exchange F h) w
  have net := (sort.comp (Tagged.mapRows_net flip_net w)).comp (Tagged.check_order (compare_net F h) w)
  refine ⟨_, net.mono ?_, fun x => ?_⟩
  · simp only [wd, wd_word]
    ring_nf
    omega
  · simp only [decide_eq_true_eq, Tagged.flatten_mapRows, agree_iff _ (sortTree_sorted w x)]
    simp only [Agree, (sortTree_perm w x).mem_iff]

end OAI.LinearAlgebra.MatrixExponent.Control
end

section
/-!
# Simultaneous reads from an array of bits

Pair each data bit with its fixed address and each proposed output bit
with its requested address. Consistency on the combined list uniquely
determines every output, even when the same address is requested often.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Control
open Tagged

def fetch (h : ℕ) (data : Val (tree h .bit)) (addr : Val (word h)) : Bool :=
  (flatten h data)[Lookup.value h addr]'(by rw [length_flatten]; exact value_lt h addr)

def batchRead (h : ℕ) (x : Val (.pair (tree h .bit) (tree h (word h)))) : Val (tree h .bit) :=
  mapRows (a := word h) (b := .bit) (fetch h x.1) h x.2

private def pairs (h w : ℕ) :=
  zipRows (a := word h) (b := .bit) (c := entry h) Prod.mk w

private theorem entries (h w : ℕ) (f : Val (word h) → Bool)
    (a : Val (tree w (word h))) (b : Val (tree w .bit)) :
    (∀ p ∈ flatten w (pairs h w a b), f p.1 = p.2) ↔
      mapRows (b := .bit) f w a = b := by
  induction w with
  | zero => simp [flatten, pairs, mapRows, zipRows]
  | succ w ih =>
    change (∀ p ∈ flatten w (pairs h w a.1 b.1) ++ flatten w (pairs h w a.2 b.2),
      f p.1 = p.2) ↔ _
    rw [List.forall_mem_append, ih, ih]
    simp only [mapRows, Prod.ext_iff]

private theorem entry_mem (h w : ℕ) (a : Val (tree w (word h))) (b : Val (tree w .bit))
    (i : Val (word h)) (hi : i ∈ flatten w a) :
    ∃ y, (i, y) ∈ flatten w (pairs h w a b) := by
  induction w with
  | zero =>
    rw [List.mem_singleton.mp hi]
    exact ⟨b, List.mem_singleton_self _⟩
  | succ w ih =>
    rcases List.mem_append.mp hi with hl | hr
    · obtain ⟨y, hy⟩ := ih a.1 b.1 hl
      exact ⟨y, List.mem_append_left _ hy⟩
    · obtain ⟨y, hy⟩ := ih a.2 b.2 hr
      exact ⟨y, List.mem_append_right _ hy⟩

private theorem dictionary (h : ℕ) :
    ∃ keys : Val (tree h (word h)), (∀ i, i ∈ flatten h keys) ∧
      ∀ b : Val (tree h .bit), mapRows (b := .bit) (fetch h b) h keys = b := by
  let code (i : Fin (2 ^ h)) := Lookup.bits h i
  obtain ⟨keys, hk⟩ := Lookup.as_tree (a := word h) h (List.ofFn code) List.length_ofFn
  refine ⟨keys, ?_, fun b => flatten_inj h ?_⟩
  · intro i
    rw [hk, List.mem_ofFn]
    exact ⟨⟨Lookup.value h i, value_lt h i⟩, value_injective h (Lookup.value_bits (value_lt h i))⟩
  · rw [flatten_mapRows, hk]
    have hb := length_flatten h b
    apply List.ext_getElem (by simp [hb])
    intro i hi hj
    simp [code, fetch, Lookup.value_bits (show i < 2 ^ h by rw [← hb]; exact hj)]

private theorem read_iff (h : ℕ) (keys : Val (tree h (word h))) (ha : ∀ i, i ∈ flatten h keys)
    (hk : ∀ b : Val (tree h .bit), mapRows (b := .bit) (fetch h b) h keys = b)
    (b : Val (tree h .bit)) (a : Val (tree h (word h))) (y : Val (tree h .bit)) :
    Agree (flatten h (pairs h h keys b) ++ flatten h (pairs h h a y)) ↔
      batchRead h (b, a) = y := by
  have hl := (entries h h (fetch h b) keys b).mpr (hk b)
  unfold batchRead
  rw [← entries]
  constructor
  · intro he i hi
    obtain ⟨c, hc⟩ := entry_mem h h keys b i.1 (ha _)
    exact (hl _ hc).trans (he _ (List.mem_append_left _ hc) _ (List.mem_append_right _ hi) rfl)
  · intro hr i hi j hj he
    have all := List.forall_mem_append.mpr ⟨hl, hr⟩
    exact (all i hi).symm.trans (he ▸ all j hj)

theorem batch_read_net (F : Type) [Field F] (h : ℕ) :
    DNet F (.pair (tree h .bit) (tree h (word h))) (tree h .bit)
      (batchRead h) (10000 * 2 ^ h * (h + 1) ^ 3) := by
  obtain ⟨keys, ha, hk⟩ := dictionary h
  obtain ⟨f, checker, ok⟩ := agree_net F h (h + 1)
  have zip := zipRows_net (a := word h) (b := .bit) (c := entry h) (f := Prod.mk)
    (DNet.id F (entry h)) h
  have left := (((literal_net F _ keys).par (DNet.id F (tree h .bit))).pre
    ((Rewire.unit' _).comp (.swap _ _))).comp zip
  obtain ⟨v, hv, net⟩ := ((left.par zip).pre (.assoc _ _ _)).comp checker
  have pin := Net.table (F := F) .bit .unit (fun b _ => if b then 1 else 0) (by decide)
  refine ⟨v + 1 + wd (tree h .bit), ?_, Net.curry ?_⟩
  · simp only [wd_tree, wd_word, wd, pow_succ] at hv ⊢
    have hp := Nat.one_le_pow h 2 (by decide)
    ring_nf at hv ⊢
    omega
  · convert net.comp pin using 1
    funext ⟨⟨b, a⟩, y⟩ u
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have he := ok (pairs h h keys b, pairs h h a y)
    exact if_congr (he.trans (read_iff h keys ha hk b a y)).symm rfl rfl

end OAI.LinearAlgebra.MatrixExponent.Control
end

section
/-! # Reading an array in any exterior bit layout -/

namespace OAI.LinearAlgebra.MatrixExponent.Control

private theorem read_eq {a : Wire} {w : ℕ} (L : Layout a (tree w a) (Fin (2 ^ w)))
    (hL : ∀ x, List.ofFn (L.read x) = flatten w x) (x : Val (tree w a)) (i : Fin (2 ^ w)) :
    L.read x i = (flatten w x)[i.val]'(by rw [Tagged.length_flatten]; exact i.isLt) := by
  simp [← hL]

theorem read_net (F : Type) [Field F] (w : ℕ) :
    Install.BNet F (read w) (10000 * 2 ^ w * (w + 1) ^ 3) := by
  obtain ⟨D, hD⟩ := Layout.exists_tree .bit w
  obtain ⟨A, hA⟩ := Layout.exists_tree (word w) w
  let b : Fin (2 ^ w) ≃ slots (tree w .bit) :=
    (Equiv.prodUnique _ Unit).symm.trans D.positions
  let a := b.sumCongr A.positions
  apply Install.BNet.of_layout (a := .pair (tree w .bit) (tree w (word w))) (b := tree w .bit) a b
  convert batch_read_net F w using 1
  funext x
  apply D.injective
  funext i
  have deref (data : Val (tree w .bit)) (k : Val (word w)) :
      fetch w data k = D.read data (index w k) :=
    (read_eq D hD data (index w k)).symm
  have hmap : D.read (batchRead w x) i = fetch w x.1 (A.read x.2 i) := by
    simp only [read_eq D hD, read_eq A hA, batchRead, Tagged.flatten_mapRows, List.getElem_map]
  rw [hmap, deref]
  change (bits (tree w .bit)) ((bits (tree w .bit)).symm _) (b i) = _
  rw [Equiv.apply_symm_apply, Function.comp_apply, Equiv.symm_apply_apply]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Control
end
