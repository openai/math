import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dictionary
import OAI.LinearAlgebra.MatrixExponent.Tagged.SortBack
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Packets
import Mathlib.GroupTheory.Perm.ViaEmbedding
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute

section
/-! # Budget for packing calls with a common table label -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Label

open Finset

/-- Allow one enable bit per call. The rest of the address can encode
the shared label and the dictionary's enable bit. -/
def cap (w a : ℕ) := (w / 2) / (1 + a)

def blocks (w a n : ℕ) := min n (n / cap w a + 1)

theorem cap_bound (w a : ℕ) : cap w a * (1 + a) ≤ w / 2 := Nat.div_mul_le_self _ _

theorem block_space {w a : ℕ} (hw : 64 ≤ w) (ha : a ≤ w / 4) (n : ℕ) :
    n ≤ blocks w a n * cap w a := by
  have hc : 0 < cap w a := Nat.div_pos (by omega) (by omega)
  unfold blocks
  rcases min_choice n (n / cap w a + 1) with h|h <;> rw [h]
  · exact Nat.le_mul_of_pos_right _ hc
  · rw [mul_comm]; exact (Nat.lt_mul_div_succ n hc).le

private theorem block_cost {w a : ℕ} (hw : 64 ≤ w) (ha : a ≤ w / 4) (n : ℕ) :
    w * blocks w a n ≤ 8 * ((1 + a) * n) + w := by
  have h : w / 2 < (1 + a) * (cap w a + 1) := Nat.lt_mul_div_succ _ (by omega)
  have h' : w ≤ 8 * ((1 + a) * cap w a) := by rw [mul_add, mul_one] at h; omega
  calc
    _ ≤ w * (n / cap w a + 1) := Nat.mul_le_mul_left _ (min_le_right _ _)
    _ ≤ 8 * ((1 + a) * cap w a) * (n / cap w a) + w := by
      rw [mul_add, mul_one]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ h') _
    _ ≤ _ := by
      rw [mul_assoc, mul_assoc]
      gcongr
      exact Nat.mul_div_le _ _

theorem choose_rows {I : Type} [Fintype I] {w s : ℕ} (hw : 64 ≤ w)
    (hI : Fintype.card I ≤ 2 ^ (w / 4)) (a n : I → ℕ) (ha : ∀ i, a i ≤ w / 4)
    (hs : ∑ i, (1 + a i) * n i ≤ s) (hs' : s ≤ 2 ^ (2 * w - 1)) :
    ∃ j : ℕ, w ≤ j ∧ j + 1 ≤ 2 * w ∧ (∑ i, blocks w (a i) (n i)) ≤ 2 ^ j ∧
      2 ^ j * (1 + j) ≤ 40 * (s + w * 2 ^ w) := by
  let R := ∑ i, blocks w (a i) (n i)
  have ht : R ≤ s := le_trans (sum_le_sum fun i _ =>
    (min_le_left _ _).trans (Nat.le_mul_of_pos_left _ (by omega))) hs
  have hc : w * R ≤ 8 * s + w * 2 ^ w := by
    have h := sum_le_sum (s := univ) fun i _ => block_cost hw (ha i) (n i)
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id] at h
    have hcard := hI.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (show w / 4 ≤ w by omega))
    exact h.trans (Nat.add_le_add (Nat.mul_le_mul_left 8 hs) (by rw [mul_comm _ w]; gcongr))
  by_cases hR : R ≤ 2 ^ w
  · refine ⟨w, le_rfl, by omega, hR, ?_⟩
    nlinarith [Nat.mul_le_mul_left (2 ^ w) (show 1 ≤ w by omega)]
  let j := Nat.clog 2 R
  have hlo : w < j := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (lt_of_not_ge hR)
  have hhi : j ≤ 2 * w - 1 := (Nat.clog_le_iff_le_pow (by decide)).mpr (ht.trans hs')
  refine ⟨j, hlo.le, by omega, Nat.le_pow_clog (by decide) _, ?_⟩
  have hp : 2 ^ j ≤ 2 * R := by
    have he : 2 ^ (j - 1) < R := (Nat.lt_clog_iff_pow_lt (by decide)).mp (by omega)
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    omega
  calc
    _ ≤ (2 * R) * (2 * w) := Nat.mul_le_mul hp (by omega)
    _ ≤ _ := by nlinarith only [hc, Nat.zero_le s, Nat.zero_le (w * 2 ^ w)]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Label
end

/-!
# One dictionary for heterogeneous calls

A row contains one table label and several argument tuples for that
same table. Unused positions contribute the scalar one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Label
open Finset Classical Transcript

variable {F X I R : Type} [Field F] [Fintype I]

private theorem group [Fintype R] {w : ℕ} (hw : 64 ≤ w) (hI : Fintype.card I ≤ w / 4)
    (k : (I → Bool) → F) (r : R → I → X) :
    ∃ (f : (Fin (w / 2) → Bool) → F)
      (q : Fin (blocks w (Fintype.card I) (Fintype.card R)) → Fin (w / 2) → X ⊕ Bool),
      ∀ x : X → Bool, ∏ i, f (Sum.elim x id ∘ q i) = ∏ j, k (x ∘ r j) := by
  let C := Fin (cap w (Fintype.card I))
  let B := Fin (blocks w (Fintype.card I) (Fintype.card R))
  let col : C × Option I ↪ Fin (w / 2) := (Function.Embedding.nonempty_of_card_le
    (by simpa [C, add_comm] using cap_bound w (Fintype.card I))).some
  let idx : R ↪ B × C := (Function.Embedding.nonempty_of_card_le
    (by simpa [B, C] using block_space hw hI (Fintype.card R))).some
  let taps (j : R) (i : Option I) : X ⊕ Bool := i.elim (.inr true) (fun t => .inl (r j t))
  let p := Function.extend idx taps (fun _ _ => .inr false)
  let q (b : B) := Function.extend col (fun i => p (b, i.1) i.2) (fun _ => .inr false)
  let f (y : Fin (w / 2) → Bool) :=
    ∏ c : C, if y (col (c, none)) then k (fun i => y (col (c, some i))) else 1
  refine ⟨f, q, fun x => ?_⟩
  let g (i : B × C) := if Sum.elim x id (p i none)
    then k (fun j => Sum.elim x id (p i (some j))) else 1
  have he (b : B) : f (Sum.elim x id ∘ q b) = ∏ c, g (b, c) := by
    simp only [f, q, Function.comp_apply, col.injective.extend_apply, g]
  simp only [he]
  rw [← Fintype.prod_prod_type g, ← prod_subset (subset_univ (univ.image idx))]
  · rw [prod_image idx.injective.injOn]
    simp [g, p, idx.injective.extend_apply, taps, Function.comp_def]
  · intro i _ hi
    have hn : ¬∃ j, idx j = i := by simpa using hi
    simp [g, p, Function.extend_apply' _ _ _ hn]

variable [Fintype X] {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

/-- The arity bound for the output can be chosen independently of the
labels. It suffices to admit all required sorting tables. -/
theorem packed_calls {w u s : ℕ} (hw : 64 ≤ w) (hu : 3 ≤ u) (ha : 2 * 2 ^ (2 * w) * (4 * w) ≤ u)
    (hI : Fintype.card I ≤ 2 ^ (w / 4)) (hA : ∀ i, Fintype.card (A i) ≤ w / 4)
    (hs : ∑ i, (1 + Fintype.card (A i)) * Fintype.card (B i) ≤ s) (hs' : s ≤ 2 ^ (2 * w - 1))
    (k : (i : I) → (A i → Bool) → F) (r : (i : I) → B i → A i → X) :
    WideWeight F u (SortTables F w) (fun x => ∏ i, ∏ j, k i (x ∘ r i j))
      (4 * Fintype.card X + 440000 * (s + w * 2 ^ w)) := by
  obtain ⟨j, hj, hj', hrows, hcost⟩ := choose_rows hw hI _ _ hA hs hs'
  choose f t ht using fun i => group hw (hA i) (k i) (r i)
  let R := Σ i, Fin (blocks w (Fintype.card (A i)) (Fintype.card (B i)))
  let Y := Fin (w / 4) ⊕ Fin (w / 2)
  let name : I ↪ (Fin (w / 4) → Bool) := (Function.Embedding.nonempty_of_card_le (by simpa using hI)).some
  let F₀ (y : Y → Bool) := Function.extend name f (fun _ _ => 1) (y ∘ Sum.inl) (y ∘ Sum.inr)
  let read (a : R) : Y → X ⊕ Bool := Sum.elim (Sum.inr ∘ name a.1) (t a.1 a.2)
  have he (x : X → Bool) (a : R) : F₀ (Sum.elim x id ∘ read a) =
      f a.1 (Sum.elim x id ∘ t a.1 a.2) := by
    change Function.extend name f _ (name a.1) _ = _
    rw [name.injective.extend_apply]
    rfl
  have hu' : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ u := by
    refine le_trans ?_ ha
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hj')) (by omega)
  have h := dictionary hj hj' hu hu' (by simp [Y]; omega) (by simpa [R] using hrows) F₀ read
  intro a e
  obtain ⟨n, hn, h⟩ := h a e
  refine ⟨n, by rw [mul_assoc] at hn; omega, ?_⟩
  have eq (x : X → Bool) : (∏ i : R, F₀ (Sum.elim x id ∘ read i)) = ∏ i, ∏ j, k i (x ∘ r i j) := by
    simp only [he, R, Fintype.prod_sigma, ht]
  simpa only [eq] using h

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Label
end

/-! # Reading labeled gates on a common tape -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Label
open Classical Finset Transcript Install Processor

variable {F V X : Type} [Field F] [Fintype V] [Fintype X]

abbrev args (T : Table F) := Wire.pair T.1 T.2.1

def applyTable (T : Table F) (x : Val (args T)) : F := T.2.2 x.1 x.2

def tableBits (T : Table F) (x : slots (args T) → Bool) : F :=
  applyTable T ((bits (args T)).symm x)

theorem bend {u : ℕ} {M : Set (Table F)} (hu : 3 ≤ u) (T : Table F)
    (ht : arity T ≤ u) (hk : arity T ≤ 3 ∨ T ∈ M) :
    ∃ s ≤ 9 * (1 + arity T), Wide F u M (args T) .unit (fun x _ => applyTable T x) s := by
  obtain ⟨a, b, k⟩ := T
  let v := Wide.table a b k ht hk
  obtain ⟨m, hm, l⟩ := DNet.id F b
  obtain ⟨n, hn, l⟩ := l.includeWide (L := M) hu
  obtain ⟨p, hp, r⟩ := (Tagged.cap (F := F) b).includeWide (L := M) hu
  have h := (v.par l).comp r
  refine ⟨1 + (wd a + wd b) + n + p, by unfold arity; dsimp; omega, ?_⟩
  convert h using 1
  funext x _
  change k x.1 x.2 = ∑ y : Val b × Val b,
    (k x.1 y.1 * if x.2 = y.2 then 1 else 0) * if y.1 = y.2 then 1 else 0
  simp [Fintype.sum_prod_type, mul_ite]

variable (T : V → Table F) (L : Finset (Table F))

private def regroup : (Σ t : ↥L, {v // T v = t.val}) ≃ {v // T v ∈ L} where
  toFun x := ⟨x.2.val, x.2.property.symm ▸ x.1.property⟩
  invFun x := ⟨⟨T x.val, x.property⟩, ⟨x.val, rfl⟩⟩
  left_inv := by rintro ⟨⟨t, ht⟩, ⟨v, h⟩⟩; change T v = t at h; subst t; rfl
  right_inv _ := rfl

/-- Replace just the labeled factors by one dictionary. -/
theorem tape {w u s : ℕ} (hw : 64 ≤ w) (hu : 3 ≤ u) (ha : 2 * 2 ^ (2 * w) * (4 * w) ≤ u)
    (hL : L.card ≤ 2 ^ (w / 4)) (ht : ∀ t ∈ L, arity t ≤ w / 4)
    (hs : ∑ v, (1 + arity (T v)) ≤ s) (hs' : s ≤ 2 ^ (2 * w - 1))
    (r : ∀ v, slots (args (T v)) → X) :
    WideWeight F u (SortTables F w) (fun x => ∏ v : {v // T v ∈ L}, tableBits (T v) (x ∘ r v))
      (4 * Fintype.card X + 440000 * (s + w * 2 ^ w)) := by
  let A (t : ↥L) := slots (args t.val)
  let B (t : ↥L) := {v // T v = t.val}
  let read (t : ↥L) (v : B t) : A t → X := cast (congrArg (fun t => slots (args t) → X) v.property) (r v.val)
  have card (t : ↥L) : Fintype.card (A t) = arity t.val := card_slots _
  have cost : ∑ t, (1 + Fintype.card (A t)) * Fintype.card (B t) ≤ s := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun v => T v ∈ L) (fun v => 1 + arity (T v))
    have h' : (∑ v : {v // T v ∈ L}, (1 + arity (T v))) ≤ s := (Nat.le_add_right _ _).trans (h.le.trans hs)
    rw [← (regroup T L).sum_comp, Fintype.sum_sigma] at h'
    refine le_trans ?_ h'
    apply sum_le_sum
    intro t _
    have he (v : B t) : T ((regroup T L ⟨t, v⟩).val) = t.val := v.property
    simp [he, card, B, mul_comm]
  have H := packed_calls hw hu ha (by simpa using hL) (fun t => by rw [card]; exact ht _ t.property)
    cost hs' (fun t => tableBits t.val) read
  convert H using 1
  funext x
  rw [← (regroup T L).prod_comp, Fintype.prod_sigma]
  apply prod_congr rfl
  intro t _
  apply prod_congr rfl
  intro v _
  obtain ⟨t, ht⟩ := t
  obtain ⟨v, hv⟩ := v
  change T v = t at hv
  subst t
  rfl

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Label
end

/-!
# Applying small dictionaries with many output bits

Guess the output bits and check each complete answer with one scalar
dictionary call. The tape then has a unique extension, so the output
can feed a second weighted computation without a multiplicity factor.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Transcript Install Classical

variable {F I J X Y R : Type} [Field F] [Fintype I] [Fintype J] [Fintype X] [Fintype Y]
    [Fintype R] {w j u m n : ℕ}

variable (f : (I → Bool) → J → Bool) (input : R → I → X ⊕ Bool) (output : R × J ≃ Y)

def applyRows (x : X → Bool) (y : Y) : Bool :=
  let z := output.symm y
  f (Sum.elim x id ∘ input z.1) z.2

theorem transform (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w)
    (hu : 3 ≤ u) (ha : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ u)
    (hI : Fintype.card I + Fintype.card J < j) (hR : Fintype.card R ≤ 2 ^ j) :
    WideWeight F u (SortTables F w)
      (fun x : X ⊕ Y → Bool => if applyRows f input output (x ∘ Sum.inl) = x ∘ Sum.inr then 1 else 0)
      (4 * Fintype.card (X ⊕ Y) + 11000 * 2 ^ j * (1 + j)) := by
  let k (v : I ⊕ J → Bool) : F := if f (v ∘ Sum.inl) = v ∘ Sum.inr then 1 else 0
  let r (p : R) : I ⊕ J → (X ⊕ Y) ⊕ Bool :=
    Sum.elim (fun i => Sum.map Sum.inl id (input p i)) (fun t => .inl (.inr (output (p, t))))
  have H := dictionary hj hj' hu ha (by simpa using hI) hR k r
  convert H using 1
  funext x
  have hk (p) : k (Sum.elim x id ∘ r p) =
      if ∀ t, applyRows f input output (x ∘ Sum.inl) (output (p, t)) = x (.inr (output (p, t)))
      then 1 else 0 := by
    have e : (Sum.elim x id ∘ r p) ∘ Sum.inl = Sum.elim (x ∘ Sum.inl) id ∘ input p := by
      funext t
      simp only [Function.comp_apply, r, Sum.elim_inl]
      cases input p t <;> rfl
    simp only [k, e, funext_iff, applyRows, Equiv.symm_apply_apply]
    rfl
  simp_rw [hk]
  by_cases he : applyRows f input output (x ∘ Sum.inl) = x ∘ Sum.inr
  · simp [he]
  · rw [ite_eq_right he, eq_comm]
    obtain ⟨y, hy⟩ := Function.ne_iff.mp he
    obtain ⟨⟨p, t⟩, rfl⟩ := output.surjective y
    exact Finset.prod_eq_zero (Finset.mem_univ p) (ite_eq_right (fun h => hy (h t)))

/-- Existentially hide the unique output tape after weighting it. -/
theorem bind {L : Set (Table F)} {f : (X → Bool) → Y → Bool} {k : (X ⊕ Y → Bool) → F}
    (hu : 3 ≤ u)
    (hf : WideWeight F u L (fun x => if f (x ∘ Sum.inl) = x ∘ Sum.inr then 1 else 0) m)
    (hk : WideWeight F u L k n) :
    WideWeight F u L (fun x => k (Sum.elim x (f x)))
      (8 * (Fintype.card X + Fintype.card Y) + 9 * (m + n)) := by
  let test (x : X ⊕ Y → Bool) : F := if f (x ∘ Sum.inl) = x ∘ Sum.inr then 1 else 0
  let jobs (b : Bool) := if b then test else k
  let costs (b : Bool) := if b then m else n
  have ready (b : Bool) : WideWeight F u L (jobs b) (costs b) := by
    cases b
    · exact hk
    · exact hf
  have H := wide_sum jobs (fun _ => id) costs hu ready
  convert H using 1
  · funext x
    simp [weightedSum, jobs, test, Function.comp_def]
    change k (Sum.elim x (f x)) = ∑ y, (if f x = y then 1 else 0) * k (Sum.elim x y)
    simp [ite_mul]
  · simp [costs]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# Packet matching with two permitted long sorts

Compare the sorted list before and after reversing active directions.
No distinctness test is needed for the inactive records.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Transcript Messages Install
open scoped Classical

variable (F : Type) [Field F] {X : Type} [Fintype X] {w j u H z : ℕ}

def packetRows (tap : Fin (2 ^ j) → slots (Messages.row H z) → X ⊕ Bool) (x : X → Bool) :=
  List.ofFn (fun i => (bits (Messages.row H z)).symm (Sum.elim x id ∘ tap i))

def paired (l : List (Val (Messages.row H z))) : Prop := (l.map (reverse H z)).Perm l

theorem sorted_iff {a : Wire} [LinearOrder (Val a)] (x y : Val (tree j a)) :
    sortTree j x = sortTree j y ↔ (flatten j y).Perm (flatten j x) := by
  constructor
  · intro h; exact (sortTree_perm j y).symm.trans (h ▸ sortTree_perm j x)
  · intro h
    exact Tagged.unique_sort j y (sortTree j x) ((sortTree_perm ..).trans h.symm) (sortTree_sorted ..)

theorem packet_with {G : Set (Table F)}
    (admitSort : ∀ (_ : LinearOrder (Val (Messages.row H z))),
      Fast F (Messages.row H z) → sorter F (Messages.row H z) j ∈ G)
    (hu : 3 ≤ u)
    (ha : 2 * 2 ^ j * (H + z + 2) ≤ u) (hh : H + z + 2 ≤ 4 * w)
    (tap : Fin (2 ^ j) → slots (Messages.row H z) → X ⊕ Bool) :
    WideWeight F u G (fun x => if paired (packetRows tap x) then 1 else 0)
      (4 * Fintype.card X + 1000 * 2 ^ j * (1 + w)) := by
  let a := Messages.row H z
  let b := tree j a
  have hw : wd a = H + z + 2 := wd_word _
  obtain ⟨o, ho⟩ := Tagged.exists_comparator F a
  let _ := o
  have hf : Fast F a := ho.mono (by omega)
  have hsort : DWide F u G b b (sortTree j) (1 + 2 * 2 ^ j * wd a) := by
    rw [← arity_sorter F a j]
    exact ⟨_, le_rfl, Wide.table _ _ _ (by change Processor.arity (sorter F a j) ≤ u; rw [arity_sorter, hw]; exact ha)
      (.inr (admitSort o hf))⟩
  obtain ⟨L, hL⟩ := Layout.exists_tree a j
  let f := Function.uncurry tap
  intro c e
  have read := (tap_depends f).bnet F c b e L.positions
  have prep := (DNet.id F b).pair (Tagged.mapRows_net (reverse_net F H z) j)
  obtain ⟨m, hm, h⟩ := (DWide.of_dnet hu (read.comp prep)).comp (hsort.par hsort)
  obtain ⟨n, hn, cap⟩ := (Tagged.cap (F := F) b).includeWide (L := G) hu
  refine ⟨m + n, ?_, ?_⟩
  · simp only [b, wd_tree, hw, Fintype.card_prod, Fintype.card_fin, localCost] at hm hn
    rw [MatrixExponent.card_slots, wd_word] at hm
    have hk := Nat.mul_le_mul_left (2 ^ j) hh
    have := Nat.two_pow_pos j
    ring_nf at hm hn hk ⊢
    omega
  · have hc := h.comp cap
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hc
    convert hc using 1
    funext x _
    let y := (bits b).symm (Sum.elim (bits c x ∘ e) id ∘ f ∘ L.positions.symm)
    have hy : flatten j y = packetRows tap (bits c x ∘ e) := by
      rw [← hL]
      unfold packetRows
      congr 1
      funext i
      simp only [Layout.read, y, b, Equiv.apply_symm_apply, Function.comp_apply, Equiv.symm_apply_apply]
      rfl
    change (if paired _ then (1 : F) else 0) =
      if sortTree j y = sortTree j (Tagged.mapRows (reverse H z) j y) then 1 else 0
    simp only [sorted_iff, Tagged.flatten_mapRows, hy, paired]
    first | rfl | split <;> simp_all

theorem packet (hj : w ≤ j) (hj' : j ≤ 2 * w) (hu : 3 ≤ u)
    (ha : 2 * 2 ^ j * (H + z + 2) ≤ u) (hl : w ≤ H + z + 2) (hh : H + z + 2 ≤ 4 * w)
    (tap : Fin (2 ^ j) → slots (Messages.row H z) → X ⊕ Bool) :
    WideWeight F u (SortTables F w) (fun x => if paired (packetRows tap x) then 1 else 0)
      (4 * Fintype.card X + 1000 * 2 ^ j * (1 + w)) := by
  apply packet_with F _ hu ha hh tap
  intro o hf
  have hw : wd (Messages.row H z) = H + z + 2 := wd_word _
  exact ⟨j, Messages.row H z, o, hf, hj, hj', hw.ge.trans' hl, hw.le.trans hh, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # A packet plan may have repeated inactive headers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Transcript.Messages
open scoped Classical

structure PacketPlan (I : Type) (H : ℕ) where
  head : I → Val (word (H + 2))
  peer : Equiv.Perm I
  inactive : ∀ i, (head i).1 = false → peer i = i
  pairs : ∀ i, head (peer i) = opposite (head i)
  unique : ∀ i k, (head i).1 = true → head i = head k → i = k

namespace PacketPlan
variable {I : Type} {H z j : ℕ} (p : PacketPlan I H) (e : I ↪ Fin (2 ^ j))
    (v : I → Val (word z))

def packed : Fin (2 ^ j) → Val (row H z) :=
  Function.extend e (fun i => assemble (p.head i) (v i)) (fun _ => Lookup.zero _)

@[simp] theorem packed_apply (i : I) : p.packed e v (e i) = assemble (p.head i) (v i) :=
  e.injective.extend_apply _ _ _

theorem packed_other (i : Fin (2 ^ j)) (hi : i ∉ Set.range e) :
    p.packed e v i = Lookup.zero _ :=
  Function.extend_apply' _ _ _ hi

/-- The long-sort test now checks exactly one equality of payloads per
active pair. Padded positions and inactive records require no pairing. -/
theorem matching : paired (List.ofFn (p.packed e v)) ↔
    ∀ i, (p.head i).1 = true → v (p.peer i) = v i := by
  unfold paired
  constructor
  · intro hs i hi
    have hh : reverse H z (p.packed e v (e i)) ∈ List.ofFn (p.packed e v) :=
      hs.subset (List.mem_map_of_mem (List.mem_ofFn.mpr ⟨_, rfl⟩))
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp hh
    rw [packed_apply, reverse_assemble, ← p.pairs] at hk
    have hp : (p.head (p.peer i)).1 = true := by rw [p.pairs]; exact hi
    by_cases he : k ∈ Set.range e
    · obtain ⟨l, rfl⟩ := he
      rw [packed_apply] at hk
      have he := congrArg (header H z) hk
      simp only [header_assemble] at he
      have := p.unique _ _ hp he.symm
      subst l
      exact assemble_injective _ hk
    · rw [packed_other _ _ _ _ he] at hk
      have h := congrArg Prod.fst hk
      change false = (p.head (p.peer i)).1 at h
      rw [hp] at h
      contradiction
  · intro h
    rw [List.map_ofFn]
    have he : reverse H z ∘ p.packed e v = p.packed e v ∘ p.peer.viaEmbedding e := by
      funext k
      simp only [Function.comp_apply]
      by_cases hk : k ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hk
        rw [Equiv.Perm.viaEmbedding_apply, packed_apply, packed_apply, reverse_assemble, ← p.pairs]
        cases hi : (p.head i).1
        · rw [p.inactive i hi]
        · rw [h i hi]
      · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hk, packed_other _ _ _ _ hk]
        rfl
    rw [he]
    exact Equiv.Perm.ofFn_comp_perm _ _

end PacketPlan
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Hardwired packet layouts for a partial batch -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Transcript Transcript.Messages
open scoped Classical

variable {X I : Type} {H z : ℕ}

private def appendTap (H : ℕ) : (z : ℕ) →
    (slots (word z) → X) → (slots (word H) → X) → slots (word (H + z)) → X
  | 0, _, a => a
  | z + 1, b, a => Sum.elim (b ∘ Sum.inl) (appendTap H z (b ∘ Sum.inr) a)

private theorem decode_append (x : X → Bool) (a : slots (word H) → X)
    (b : slots (word z) → X) :
    (bits (word (H + z))).symm (x ∘ appendTap H z b a) =
      appendWord H z ((bits (word z)).symm (x ∘ b)) ((bits (word H)).symm (x ∘ a)) := by
  induction z with
  | zero => rfl
  | succ z ih => exact Prod.ext rfl (ih _)

def joinTap (a : slots (word (H + 2)) → X) (b : slots (word z) → X) :
    slots (row H z) → X :=
  Sum.elim (a ∘ Sum.inl) (Sum.elim (a ∘ Sum.inr ∘ Sum.inl)
    (appendTap H z b (a ∘ Sum.inr ∘ Sum.inr)))

theorem decode_join (x : X → Bool) (a : slots (word (H + 2)) → X)
    (b : slots (word z) → X) :
    (bits (row H z)).symm (x ∘ joinTap a b) =
      assemble ((bits (word (H + 2))).symm (x ∘ a)) ((bits (word z)).symm (x ∘ b)) :=
  Prod.ext rfl (Prod.ext rfl (decode_append x _ b))

/-- The tensor is fixed before the headers are known. The semantic
description only requires well-formedness on inputs where it is used. -/
theorem packet_plan_with (F : Type) [Field F] [Fintype X] [Fintype I] {w j u : ℕ}
    {G : Set (Table F)}
    (admitSort : ∀ (_ : LinearOrder (Val (row H z))), Fast F (row H z) → sorter F (row H z) j ∈ G)
    (hu : 3 ≤ u)
    (ha : 2 * 2 ^ j * (H + z + 2) ≤ u) (hh : H + z + 2 ≤ 4 * w)
    (hi : Fintype.card I ≤ 2 ^ j)
    (head : I → slots (word (H + 2)) → X ⊕ Bool) (body : I → slots (word z) → X ⊕ Bool) :
    ∃ f : (X → Bool) → F, WideWeight F u G f
        (4 * Fintype.card X + 1000 * 2 ^ j * (1 + w)) ∧
      ∀ (x : X → Bool) (p : PacketPlan I H),
        (∀ i, bits (word (H + 2)) (p.head i) = Sum.elim x id ∘ head i) →
        f x = if ∀ i, (p.head i).1 = true →
          Sum.elim x id ∘ body (p.peer i) = Sum.elim x id ∘ body i then 1 else 0 := by
  let e : I ↪ Fin (2 ^ j) := (Function.Embedding.nonempty_of_card_le (by simpa using hi)).some
  let tap := Function.extend e (fun i => joinTap (head i) (body i))
    (fun _ => Sum.inr ∘ bits (row H z) (Lookup.zero _))
  refine ⟨_, packet_with F admitSort hu ha hh tap, ?_⟩
  intro x p hp
  let v := fun i => (bits (word z)).symm (Sum.elim x id ∘ body i)
  have eq : packetRows tap x = List.ofFn (p.packed e v) := by
    unfold packetRows
    congr 1
    funext i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨k, rfl⟩ := hi
      simp only [tap, e.injective.extend_apply, PacketPlan.packed_apply]
      rw [decode_join, ← hp, Equiv.symm_apply_apply]
    · rw [p.packed_other _ _ _ hi]
      unfold tap
      rw [Function.extend_apply' _ _ _ hi]
      exact (bits (row H z)).symm_apply_apply _
  simp only [eq, p.matching, v, Equiv.symm_apply_eq, Equiv.apply_symm_apply]

theorem packet_plan (F : Type) [Field F] [Fintype X] [Fintype I] {w j u : ℕ}
    (hj : w ≤ j) (hj' : j ≤ 2 * w) (hu : 3 ≤ u)
    (ha : 2 * 2 ^ j * (H + z + 2) ≤ u) (hl : w ≤ H + z + 2) (hh : H + z + 2 ≤ 4 * w)
    (hi : Fintype.card I ≤ 2 ^ j)
    (head : I → slots (word (H + 2)) → X ⊕ Bool) (body : I → slots (word z) → X ⊕ Bool) :
    ∃ f : (X → Bool) → F, WideWeight F u (SortTables F w) f
        (4 * Fintype.card X + 1000 * 2 ^ j * (1 + w)) ∧
      ∀ (x : X → Bool) (p : PacketPlan I H),
        (∀ i, bits (word (H + 2)) (p.head i) = Sum.elim x id ∘ head i) →
        f x = if ∀ i, (p.head i).1 = true →
          Sum.elim x id ∘ body (p.peer i) = Sum.elim x id ∘ body i then 1 else 0 := by
  apply packet_plan_with F _ hu ha hh hi head body
  intro o hf
  have hw : wd (Messages.row H z) = H + z + 2 := wd_word _
  exact ⟨j, row H z, o, hf, hj, hj', hw.ge.trans' hl, hw.le.trans hh, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Pairing and padding bit positions on a shared row tape -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Classical

variable {I : Type} {H : ℕ}

theorem PacketPlan.square (a : PacketPlan I H) (i : I) : a.peer (a.peer i) = i := by
  by_cases h : (a.head i).1 = true
  · symm
    apply a.unique _ _ h
    rw [a.pairs, a.pairs]
    simp [Transcript.Messages.opposite, h]
    exact Prod.ext h rfl
  · rw [a.inactive _ (Bool.eq_false_iff.mpr h), a.inactive _ (Bool.eq_false_iff.mpr h)]

namespace Links

def pad {A B : Type} (f : A ↪ B) (x : B → Bool) : Prop :=
  ∀ i, i ∉ Set.range f → x i = false

def put {A B : Type} (f : A ↪ B) (x : A → Bool) : B → Bool :=
  Function.extend f x (fun _ => false)

theorem read_put {A B : Type} (f : A ↪ B) (x : A → Bool) : put f x ∘ f = x :=
  funext fun i => f.injective.extend_apply x (fun _ => false) i

theorem padded {A B : Type} (f : A ↪ B) (x : A → Bool) : pad f (put f x) :=
  fun _ h => Function.extend_apply' _ _ _ h

theorem put_read {A B : Type} (f : A ↪ B) {x : B → Bool} (hx : pad f x) :
    put f (x ∘ f) = x := by
  funext i
  by_cases h : i ∈ Set.range f
  · obtain ⟨k, rfl⟩ := h
    exact congrFun (read_put f _) k
  · exact ((padded f _) _ h).trans (hx _ h).symm

end Links
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# Naming whole rows by signed identifiers

Several pins can share one header. It suffices that equality of signed
identifiers coincide with equality of rows. Every live row then has a
unique opposite row, even if the unused headers are all identical.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Links
open Classical

variable {A B K : Type} {H : ℕ}

def flipped (x : Bool × K) := (!x.1, x.2)

private theorem flip_twice (x : Bool × K) : flipped (flipped x) = x := by simp [flipped]

variable (place : A → B) (key : A → Bool × K) (code : K ↪ Val (word H))

def header (i : B) : Val (word (H + 2)) :=
  if h : ∃ x, place x = i then (true, (key h.choose).1, code (key h.choose).2)
    else (false, false, Lookup.zero H)

theorem header_at (he : ∀ i j, key i = key j ↔ place i = place j) (p : A) :
    header place key code (place p) = (true, (key p).1, code (key p).2) := by
  have hp : ∃ x, place x = place p := ⟨p, rfl⟩
  rw [header, dite_eq_left hp, (he _ _).mpr hp.choose_spec]

theorem header_other (i : B) (h : i ∉ Set.range place) :
    header place key code i = (false, false, Lookup.zero H) := dite_eq_right h

theorem build_packet (he : ∀ i j, key i = key j ↔ place i = place j)
    (hp : ∀ x, ∃ y, key y = flipped (key x)) :
    ∃ p : PacketPlan B H, p.head = header place key code ∧
      ∀ x y, key y = flipped (key x) → p.peer (place x) = place y := by
  choose mate hm using hp
  let f (i : B) := if h : ∃ x, place x = i then place (mate h.choose) else i
  have route (x y : A) (h : key y = flipped (key x)) : f (place x) = place y := by
    have hh : ∃ a, place a = place x := ⟨x, rfl⟩
    unfold f
    rw [dite_eq_left hh, ← he, hm, (he _ _).mpr hh.choose_spec, h]
  have off (i : B) (hi : i ∉ Set.range place) : f i = i := dite_eq_right hi
  have inv : Function.Involutive f := by
    intro i
    by_cases hi : i ∈ Set.range place
    · obtain ⟨x, rfl⟩ := hi
      rw [route x (mate x) (hm x)]
      exact route _ x (by rw [hm, flip_twice])
    · rw [off i hi, off i hi]
  refine ⟨⟨header place key code, inv.toPerm, ?_, ?_, ?_⟩, rfl, route⟩
  · intro i hi
    apply off
    rintro ⟨x, rfl⟩
    rw [header_at _ _ _ he] at hi
    cases hi
  · intro i
    change header _ _ _ (f i) = _
    by_cases hi : i ∈ Set.range place
    · obtain ⟨x, rfl⟩ := hi
      rw [route x (mate x) (hm x), header_at _ _ _ he, header_at _ _ _ he, hm]
      rfl
    · rw [off i hi, header_other _ _ _ _ hi]
      rfl
  · intro i j hi hj
    have live (i : B) (hi : (header place key code i).1 = true) : i ∈ Set.range place := by
      by_contra hn
      rw [header_other _ _ _ _ hn] at hi
      cases hi
    obtain ⟨x, rfl⟩ := live i hi
    obtain ⟨y, rfl⟩ := live j (hj ▸ hi)
    rw [header_at _ _ _ he, header_at _ _ _ he] at hj
    obtain ⟨hd, heq⟩ := Prod.mk.inj (Prod.mk.inj hj).2
    exact (he x y).mp (Prod.ext hd (code.injective heq))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Links
end

/-!
# Routing arbitrarily wide records by short sorts

Repeat the same permutation test with successive slices of the payload.
Each test compares two sorted arrays of pairs. Source addresses are
constants, and all the tests share a single array of target addresses.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Assembly Coloring Install Transcript
open scoped Classical

variable (F : Type) [Field F] {w j u m : ℕ}

private abbrev RowFromExchange (j m : ℕ) := Wire.pair (word j) (word m)

private def taps : (B j × slots (RowFromExchange j m)) ⊕ (B j × slots (RowFromExchange j m)) → PermBus j m ⊕ Bool
  | .inl (i, .inl p) => .inr ((Control.decode j).symm i p)
  | .inl (i, .inr p) => .inl (.inl (i, p))
  | .inr p => .inl (.inr p)

private theorem taps_perm (L : Layout (RowFromExchange j m) (tree j (RowFromExchange j m)) (B j))
    (hL : ∀ x, List.ofFn (L.read x) = flatten j x) (z : PermBus j m → Bool) :
    let e := L.positions.sumCongr L.positions
    let b := tree j (RowFromExchange j m)
    let x := (bits (.pair b b)).symm (Sum.elim z id ∘ taps ∘ e.symm)
    (flatten j x.2).Perm (flatten j x.1) ↔ PermBus.valid z := by
  intro e b x
  let n := (Control.index j).symm
  let s i := (bits (word m)).symm (fun p => z (.inl (i, p)))
  let t i := (bits (word m)).symm (fun p => z (.inr (i, .inr p)))
  let a := n ∘ PermBus.address z
  have he (i : B j) (r : slots (RowFromExchange j m)) :
      bits (RowFromExchange j m) (L.read x.1 i) r = Sum.elim z id (taps (.inl (i, r))) ∧
      bits (RowFromExchange j m) (L.read x.2 i) r = Sum.elim z id (taps (.inr (i, r))) := by
    simp only [Layout.read, Equiv.apply_symm_apply]
    change bits (.pair b b) x (e (.inl (i, r))) = _ ∧ bits (.pair b b) x (e (.inr (i, r))) = _
    simp [x]
  have h₁ : L.read x.1 = fun i => (n i, s i) := by
    funext i
    apply (bits (RowFromExchange j m)).injective
    funext r
    rw [(he i r).1]
    cases r with
    | inl p => rfl
    | inr p => exact (congrFun ((bits (word m)).apply_symm_apply (fun r => z (.inl (i, r)))) p).symm
  have h₂ : L.read x.2 = fun i => (a i, t i) := by
    funext i
    apply (bits (RowFromExchange j m)).injective
    funext r
    rw [(he i r).2]
    cases r with
    | inl p => exact (congrFun ((Control.decode j).symm_apply_apply (fun r => z (.inr (i, .inl r)))) p).symm
    | inr p => exact (congrFun ((bits (word m)).apply_symm_apply (fun r => z (.inr (i, .inr r)))) p).symm
  have ha : Function.Bijective a ↔ Function.Bijective (PermBus.address z) := by
    constructor
    · intro h
      simpa only [a, Function.comp_def, Equiv.symm_apply_apply] using n.symm.bijective.comp h
    · exact n.bijective.comp
  rw [← hL, ← hL, h₁, h₂, labeled_perm, ha]
  simp only [a, s, t, Function.comp_apply, Equiv.symm_apply_apply,
    (bits (word m)).symm.injective.eq_iff, funext_iff, PermBus.valid]

private theorem slice_weight (hu : 3 ≤ u) (hl : w ≤ j) (hr : j ≤ 2 * w)
    (ha : 2 * 2 ^ j * (4 * w) ≤ u) (hm : m ≤ w) :
    WideWeight F u (SortTables F w)
      (fun z : PermBus j m → Bool => if PermBus.valid z then 1 else 0)
      (2000 * 2 ^ j * (w + 1)) := by
  let a := RowFromExchange j m
  let b := tree j a
  have hw : wd a = j + m := by simp [a, wd]
  obtain ⟨o, ho⟩ := Tagged.exists_comparator F a
  let _ := o
  have hf : Fast F a := ho.mono (by omega)
  have ok : sorter F a j ∈ SortTables F w := ⟨j, a, o, hf, hl, hr, by omega, by omega, rfl⟩
  have small : Processor.arity (sorter F a j) ≤ u := by
    rw [arity_sorter]
    exact (Nat.mul_le_mul_left _ (show wd a ≤ 4 * w by omega)).trans ha
  have hsort : DWide F u (SortTables F w) b b (sortTree j) (1 + 2 * 2 ^ j * wd a) := by
    rw [← arity_sorter F a j]
    exact ⟨_, le_rfl, Wide.table _ _ _ small (.inr ok)⟩
  obtain ⟨L, hL⟩ := Layout.exists_tree a j
  intro c e
  let p := L.positions.sumCongr L.positions
  have read := (tap_depends (taps (j := j) (m := m))).bnet F c (.pair b b) e p
  obtain ⟨k, hk, net⟩ := (DWide.of_dnet hu read).comp (hsort.par hsort)
  obtain ⟨l, hl', cap⟩ := (Tagged.cap (F := F) b).includeWide (L := SortTables F w) hu
  refine ⟨k + l, ?_, ?_⟩
  · simp only [b, wd_tree, hw, PermBus, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      MatrixExponent.card_slots, wd_word, localCost] at hk hl'
    have h₁ := Nat.mul_le_mul_left (2 ^ j) hr
    have h₂ := Nat.mul_le_mul_left (2 ^ j) hm
    have := Nat.two_pow_pos j
    ring_nf at hk hl' h₁ h₂ ⊢
    omega
  · have h := net.comp cap
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    convert h using 1
    funext x _
    let y := (bits (.pair b b)).symm (Sum.elim (bits c x ∘ e) id ∘ taps ∘ p.symm)
    change (if PermBus.valid _ then (1 : F) else 0) = if sortTree j y.1 = sortTree j y.2 then 1 else 0
    have he : (flatten j y.2).Perm (flatten j y.1) ↔ PermBus.valid (bits c x ∘ e) := taps_perm L hL _
    simp only [sorted_iff, he]

private theorem cover (A : Format) (v w : ℕ) (hw : 0 < w) (hv : A.width ≤ v) :
    ∃ m ≤ w, ∃ f : Fin (v / w + 1) × slots (word m) → A.pins, Function.Surjective f := by
  cases isEmpty_or_nonempty A.pins with
  | inl h =>
    let _ := h
    exact ⟨0, Nat.zero_le _, fun p => Empty.elim p.2, fun i => isEmptyElim i⟩
  | inr h =>
    let _ := h
    have h' : v ≤ (v / w + 1) * w := by
      have := Nat.mod_lt v hw
      have := Nat.mod_add_div v w
      rw [add_mul, one_mul, mul_comm (v / w) w]
      omega
    obtain ⟨g⟩ : Nonempty (A.pins ↪ Fin (v / w + 1) × slots (word w)) :=
      Function.Embedding.nonempty_of_card_le (by simpa [Format.width] using hv.trans h')
    exact ⟨w, le_rfl, Function.invFun g, fun i => ⟨g i, Function.leftInverse_invFun g.injective i⟩⟩

private abbrev Shuttle (A : Format) (j : ℕ) := (exchangeIn A j).pins ⊕ (exchangeOut A j).pins

private def slice {A : Format} (p : slots (word m) → A.pins) : PermBus j m → Shuttle A j
  | .inl (i, t) => .inl (.inr (i, p t))
  | .inr (i, .inl t) => .inl (.inl (i, t))
  | .inr (i, .inr t) => .inr (i, p t)

private theorem slices (A : Format) {c : ℕ} (f : Fin (c + 1) × slots (word m) → A.pins)
    (hf : Function.Surjective f) (z : Shuttle A j → Bool) :
    (∏ i, if PermBus.valid (z ∘ slice (fun t => f (i, t))) then (1 : F) else 0) =
      exchangeCheck A F z := by
  let x := (exchangeIn A j).code.symm (z ∘ Sum.inl)
  let y := (exchangeOut A j).code.symm (z ∘ Sum.inr)
  let pass := fun i => PermBus.valid (z ∘ slice (fun t => f (i, t)))
  have he (i) : pass i ↔ Function.Bijective x.1 ∧
      ∀ l t, z (.inr (l, f (i, t))) = z (.inl (.inr (x.1 l, f (i, t)))) := Iff.rfl
  have hb (l) : y l = x.2 (x.1 l) ↔
      ∀ p, z (.inr (l, p)) = z (.inl (.inr (x.1 l, p))) := by
    change A.code.symm _ = A.code.symm _ ↔ _
    rw [A.code.symm.injective.eq_iff, funext_iff]
    rfl
  have ok : (∀ i, pass i) ↔ Function.Bijective x.1 ∧ y = x.2 ∘ x.1 := by
    constructor
    · intro h
      refine ⟨((he 0).mp (h 0)).1, funext fun l => (hb l).mpr ?_⟩
      intro p
      obtain ⟨⟨i, t⟩, rfl⟩ := hf p
      exact ((he i).mp (h i)).2 l t
    · rintro ⟨ha, hy⟩ i
      exact (he i).mpr ⟨ha, fun l t => (hb l).mp (congrFun hy l) _⟩
  change (∏ i, if pass i then (1 : F) else 0) =
    if Function.Bijective x.1 ∧ y = x.2 ∘ x.1 then 1 else 0
  simp only [← ok]
  by_cases h : ∀ i, pass i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

private theorem exchange_weight (A : Format) (v : ℕ) (hw : 0 < w) (hl : w ≤ j) (hr : j ≤ 2 * w)
    (hu : 3 ≤ u) (ha : 2 * 2 ^ j * (4 * w) ≤ u) (hv : A.width ≤ v) :
    WideWeight F u (SortTables F w) (exchangeCheck (j := j) A F) (100000 * 2 ^ j * (j + v + 1)) := by
  obtain ⟨m, hm, f, hf⟩ := cover A v w hw hv
  let test (_ : Fin (v / w + 1)) (z : PermBus j m → Bool) := if PermBus.valid z then (1 : F) else 0
  let read i : PermBus j m → Shuttle A j ⊕ Empty := Sum.inl ∘ slice (fun t => f (i, t))
  have g := wide_sum test read (fun _ => 2000 * 2 ^ j * (w + 1)) hu (fun _ => slice_weight F hu hl hr ha hm)
  have he : weightedSum test read = exchangeCheck A F := by
    funext z
    simpa [weightedSum, test, read, Function.comp_def] using slices F A f hf z
  rw [he] at g
  intro a e
  obtain ⟨l, hk, h⟩ := g a e
  refine ⟨l, hk.trans ?_, h⟩
  have hp : Fintype.card (Shuttle A j) = 2 ^ j * j + 2 ^ j * A.width + 2 ^ j * A.width := by
    rw [Fintype.card_sum]
    change (exchangeIn A j).width + (exchangeOut A j).width = _
    simp [exchangeIn, exchangeOut, Perm]
  have hs : (v / w + 1) * (w + 1) ≤ 2 * v + j + 1 := by
    have := Nat.div_mul_le_self v w
    have := Nat.div_le_self v w
    rw [add_mul, mul_add, mul_one, one_mul]
    omega
  have ht := Nat.mul_le_mul_left (2 ^ j) hs
  have hz := Nat.mul_le_mul_left (2 ^ j) hv
  simp only [hp, Fintype.card_empty, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id]
  ring_nf at ht hz ⊢
  omega

theorem exchange (v : ℕ) (hw : 0 < w) (hl : w ≤ j) (hr : j ≤ 2 * w)
    (ha : 2 * 2 ^ j * (4 * w) ≤ u) :
    Access F u (SortTables F w) j v (1000000 * 2 ^ j * (j + v + 1)) := by
  have hu : 3 ≤ u := by
    have := Nat.le_mul_of_pos_left (4 * w) (show 0 < 2 * 2 ^ j by positivity)
    omega
  intro A hv
  have h := Kernel.of_weight hu (exchange_weight F A v hw hl hr hu ha hv)
  have hh : 100000 * 2 ^ j * (j + v + 1) + 4 * (exchangeOut A j).width ≤
      4 * (1000000 * 2 ^ j * (j + v + 1)) + 1000 * 2 ^ j * (j + v + 1) := by
    rw [Format.width_vec]
    have := Nat.mul_le_mul_left (2 ^ j) hv
    ring_nf at this ⊢
    omega
  simpa [exchangeCheck, Function.comp_def] using h.mono hh

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end
