import OAI.LinearAlgebra.MatrixExponent.Assembly.Matching
import OAI.LinearAlgebra.MatrixExponent.Packing.BadBases
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Mixer.Score
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Packing.Budget
import OAI.LinearAlgebra.MatrixExponent.Packing.ResetLocation

/-!
# Applying a single linear mixer in every host row

Decode the permutation once and broadcast it. Each row then uses
a Batcher gather on its own short records. The output separates
the group index from the within-group address.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
open Coloring Packing
open scoped Classical

variable (h a : ℕ) (ha : a ≤ h)

def merge (b : B a) (z : B (h - a)) : Cell h :=
  (splitCell a ha).symm ((cellIndex _).symm b, (cellIndex _).symm z)

def original (i : B h) (b : B a) (z : B (h - a)) :=
  (menu h i).symm (merge h a ha b z)

variable (A : Format) (m : ℕ)

abbrev Data := Format.vec m (.vec h A)
abbrev Groups := Format.vec m (.vec a (.vec (h - a) A))

def regroup (x : (Format.pair (.addr h) (Data h A m)).obj) : (Groups h a A m).obj :=
  fun j b z => x.2 j (cellIndex h (original h a ha x.1 b z))

private def perm (i : B h) (z : B h) :=
  cellIndex h ((menu h i).symm ((cellIndex h).symm z))

private def permCost := h + Install.localCost h * (2 ^ h * h)

variable {F : Type} [Field F]

private theorem perm_net : Circuit F (.addr h) (Coloring.Perm h) (perm h) (permCost h) := by
  let A := Format.addr h
  let D := Coloring.Perm h
  have he : Install.Depends (D.code ∘ perm h ∘ A.code.symm) h :=
    fun i => ⟨Finset.univ, by simp [A], fun x y e => by
      rw [funext (fun j => e j (Finset.mem_univ _))]⟩
  have hc : Circuit F A D (perm h) (A.width + Install.localCost h * D.width) := he.bnet F
  simpa only [A, D, Coloring.Perm, permCost, Format.width_addr, Format.width_vec] using hc

private abbrev LocalRow := Format.pair (.vec h A) (Coloring.Perm h)

def applyCost :=
  let w := (Data h A m).width
  permCost h + w + (Coloring.Perm h).width + w + 2 * (Format.vec m (LocalRow h A)).width +
    2 ^ m * (2 ^ h * (100 + (h + A.width)) ^ 8) + 3 * w

theorem apply_mixer :
    Circuit F (.pair (.addr h) (Data h A m)) (Groups h a A m)
      (regroup h a ha A m) (applyCost h A m) := by
  let C := Format.pair (Coloring.Perm h) (Data h A m)
  let D := Format.vec m (LocalRow h A)
  have broadcast : Circuit F C D (fun x j => (x.2 j, x.1)) (C.width + 2 * D.width) :=
    Circuit.project (fun p => p.2.elim (fun q => .inr (p.1, q)) .inl)
      (by rintro x ⟨i, q|q⟩ <;> rfl)
  have copy : Circuit F (Data h A m) (Groups h a A m)
      (fun x j b z => x j (cellIndex h (merge h a ha b z)))
      ((Data h A m).width + 2 * (Groups h a A m).width) :=
    Circuit.project (fun p => (p.1, cellIndex h (merge h a ha p.2.1 p.2.2.1), p.2.2.2))
      (fun _ _ => rfl)
  obtain ⟨s, hs, hb⟩ := Cheap.lookup F h (h + A.width) A (by omega) (by omega)
  have row := Circuit.map (A := LocalRow h A) (D := .vec h A) _ (fun _ : B m => hs)
  have start := (perm_net (F := F) h).par (Circuit.id F (Data h A m))
  have all := ((start.comp broadcast).comp row).comp copy
  have he : (Groups h a A m).width = (Data h A m).width := by
    simp only [Groups, Data, Format.width_vec]
    rw [← mul_assoc (2 ^ a), ← pow_add, Nat.add_sub_of_le ha]
  have limit : 2 ^ m * s ≤ 2 ^ m * (2 ^ h * (100 + (h + A.width)) ^ 8) := Nat.mul_le_mul_left _ (by omega)
  rw [show C.width = (Coloring.Perm h).width + (Data h A m).width from Format.width_pair _ _,
    he] at all
  convert all.mono (n := applyCost h A m) (by dsimp only [applyCost, D]; omega) using 1
  funext x j b z
  simp only [regroup, original, Function.comp_apply, perm, Prod.map_fst, Prod.map_snd, id_eq,
    Equiv.symm_apply_apply]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
end

/-! # Reading a butterfly in an indexed record format -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
open Coloring Packing Mixer

variable {a : Wire}

private def slot : (h : ℕ) → Cell h → slots a → slots (tree h a)
  | 0, _, i => i
  | h + 1, z, i =>
    if z 0 = 0 then .inl (slot h (Fin.tail z) i) else .inr (slot h (Fin.tail z) i)

private theorem read_bit (h : ℕ) (z : Cell h) (x : Val (tree h a)) (i : slots a) :
    bits a (Mixer.read h x z) i = bits (tree h a) x (slot h z i) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [Mixer.read, slot]
    split_ifs
    · exact ih _ x.1
    · exact ih _ x.2

private def coords (a : Wire) (h : ℕ) : Cell h × slots a ≃ slots (tree h a) :=
  Equiv.ofBijective (Function.uncurry (slot h)) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_, by simp [Fintype.card_prod, wd_tree]⟩
    intro p q eq
    let r z := (bits a).symm (fun j => decide (p = (z, j)))
    have test := congrArg (bits (tree h a) (write h r)) eq
    change bits (tree h a) _ (slot h p.1 p.2) = bits (tree h a) _ (slot h q.1 q.2) at test
    simpa only [← read_bit, read_write, r, Equiv.apply_symm_apply, Prod.mk.eta, decide_true,
      eq_comm (a := true), decide_eq_true_eq] using test)

private def layout (a : Wire) (h : ℕ) : (Format.vec h (.wire a)).pins ≃ slots (tree h a) :=
  ((cellIndex h).symm.prodCongr (.refl _)).trans (coords a h)

private theorem layout_read (h : ℕ) (x : Val (tree h a)) :
    Assembly.view _ (layout a h) x = Mixer.read h x ∘ (cellIndex h).symm := by
  apply (Format.vec h (.wire a)).code.injective
  rw [view_apply, Equiv.apply_symm_apply]
  funext ⟨i, j⟩
  exact (read_bit _ _ _ _).symm

def packed (h : ℕ) (f : Val (tree h a) → Val (tree h a)) (x : B h → Val a) :=
  Mixer.read h (f (write h (x ∘ cellIndex h))) ∘ (cellIndex h).symm

theorem packed_map {F : Type} [Field F] {u m h : ℕ} {L : Set (Table F)}
    {f : Val (tree h a) → Val (tree h a)}
    (hf : DWide F u L (tree h a) (tree h a) f m) :
    Map F u L (.vec h (.wire a)) (.vec h (.wire a)) (packed h f) m := by
  apply Map.of_layout (layout a h) (layout a h) hf
  intro x
  have he : write h (Assembly.view _ (layout a h) x ∘ cellIndex h) = x := by
    apply (Assembly.view _ (layout a h)).injective
    rw [layout_read, read_write]
    funext j
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  exact (layout_read h _).trans (by unfold packed; rw [he])

end OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
end

/-! # Autocorrelations of binary load words -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
open Coloring Packing Mixer Finset
open scoped Classical

def graph (F : Type) [Field F] (A B : Format) (f : A.obj → B.obj) : Table F :=
  lookup F A B (fun x y => if f x = y then 1 else 0)

variable {F : Type} [Field F] {u : ℕ} {L : Set (Table F)}

theorem gate {A B : Format} {f : A.obj → B.obj} (hu : A.width + B.width ≤ u)
    (h : graph F A B f ∈ L) : Map F u L A B f (1 + A.width + B.width) :=
  Kernel.lookup hu h

def precision (h d : ℕ) := 2 * (h + d) + 1

def start (d n : ℕ) (q : B d) : Val (word n) := (wordCode n).symm (q.val : ZMod (2 ^ n))

def finish (h n : ℕ) (x : Val (word n)) : B n :=
  ⟨(wordCode n x).val / 2 ^ h, (Nat.div_le_self _ _).trans_lt (ZMod.val_lt _)⟩

def correlate (h d : ℕ) (x : B h → B d) : B h → B (precision h d) :=
  let n := precision h d
  finish h n ∘ packed h (correlation (wordCode n) h) (start d n ∘ x)

theorem correlate_eq (h d : ℕ) (x : B h → B d) (z : Cell h) :
    (correlate h d x (cellIndex h z)).val =
      ∑ i, (x (cellIndex h i)).val * (x (cellIndex h (i + z))).val := by
  let f := fun i => (x (cellIndex h i)).val
  have hb := exact_correlation h d f (fun i => (x _).isLt.le) z
  unfold correlate finish packed
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  change (Mixer.view (wordCode (2 * (h + d) + 1)) h (correlation (wordCode (2 * (h + d) + 1)) h (encode h (2 * (h + d) + 1) f)) z).val / 2 ^ h = _
  rw [hb]
  exact Nat.mul_div_cancel_left _ (by positivity)

def corrKeys (F : Type) [Field F] (h d : ℕ) : Finset (Table F) :=
  let n := precision h d
  insert (graph F (.addr d) (.wire (word n)) (start d n)) <|
    insert (graph F (.wire (word n)) (.addr n) (finish h n)) (dictionary (wordCode n) F)

theorem size_keys (h d : ℕ) : (corrKeys F h d).card ≤ 4 :=
  (card_insert_le _ _).trans (Nat.add_le_add_right
    ((card_insert_le _ _).trans (Nat.add_le_add_right (dictionary_size _) 1)) 1)

def corrCost (h d : ℕ) :=
  let n := precision h d
  2 ^ h * ((1 + d + n) + (2 * h + 3) * (1 + 4 * n) + (1 + n + n))

theorem corr_map (h d : ℕ) (hu : 4 * precision h d ≤ u) (hl : (corrKeys F h d : Set _) ⊆ L) :
    Map F u L (.vec h (.addr d)) (.vec h (.addr (precision h d))) (correlate h d) (corrCost h d) := by
  let n := precision h d
  change 4 * n ≤ u at hu
  have hn : 1 ≤ n ∧ d ≤ n := by unfold n precision; omega
  have hw : (Format.wire (word n)).width = n := by simp [Format.width]
  have lead : Map F u L (.addr d) (.wire (word n)) (start d n) (1 + d + n) := by
    apply Kernel.mono (gate (by rw [Format.width_addr, hw]; omega)
      (hl (by simp [corrKeys, n])))
    rw [Format.width_addr, hw]
  have last : Map F u L (.wire (word n)) (.addr n) (finish h n) (1 + n + n) := by
    apply Kernel.mono (gate (by rw [Format.width_addr]; omega)
      (hl (by simp [corrKeys, n])))
    rw [Format.width_addr]
  have net := correlation_net (wordCode n) h (F := F) (u := u) (by omega) (by rwa [wd_word])
  have hh : (dictionary (wordCode n) F : Set _) ⊆ L :=
    fun k hk => hl (mem_insert_of_mem (mem_insert_of_mem hk))
  have mid := Kernel.widen (packed_map net) le_rfl hh
  rw [wd_word] at mid
  have before := Map.vec (t := h) _ (fun _ => lead)
  have after := Map.vec (t := h) _ (fun _ => last)
  exact ((before.comp mid).comp after).mono (by unfold corrCost; exact le_of_eq (by ring))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
end

/-! # Weighted autocorrelation tables for one processor -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
open Coloring Finset
open scoped Classical

abbrev Num (h d : ℕ) := Format.vec h (.addr d)
abbrev Input (h k d : ℕ) := Format.pair (Num h d) (Num k d)
abbrev Both (n d : ℕ) := Format.pair (.addr n) (.addr d)
abbrev wordLength (h d : ℕ) := precision h d + d

def times (n d : ℕ) (v : (Both n d).obj) : B (n + d) :=
  ⟨v.1.val * v.2.val, by rw [pow_add]; exact Nat.mul_lt_mul_of_lt_of_lt v.1.isLt v.2.isLt⟩

def pairs (h k n d : ℕ) (v : ((Num h n).pair (Num k d)).obj)
    (i : B (k + h)) : (Both n d).obj :=
  (v.1 (Match.rowIndex k h i).2, v.2 (Match.rowIndex k h i).1)

def products (h k d : ℕ) (x : (Input h k d).obj) (i : B (k + h)) :=
  times (precision h d) d (pairs h k _ _ (correlate h d x.1, x.2) i)

variable {F : Type} [Field F] {L : Set (Table F)} {u : ℕ}

def keys (F : Type) [Field F] (h d : ℕ) :=
  insert (graph F (Both (precision h d) d) (.addr (wordLength h d)) (times _ _)) (corrKeys F h d)

theorem card_keys (h d : ℕ) : (keys F h d).card ≤ 5 :=
  (card_insert_le _ _).trans (Nat.add_le_add_right (size_keys h d) 1)

theorem arity_keys {h d : ℕ} {t : Table F} (ht : t ∈ keys F h d) :
    wd t.1 + wd t.2.1 ≤ 4 * precision h d := by
  have hw : (Format.wire (word (precision h d))).width = precision h d := by
    exact (card_slots _).trans (wd_word _)
  simp only [keys, corrKeys, mem_insert] at ht
  rcases ht with rfl | rfl | rfl | hd
  · simp only [graph, lookup, wd_word, Both, Format.width_pair, Format.width_addr, wordLength]
    unfold precision
    omega
  · simp only [graph, lookup, wd_word, Format.width_addr, hw]
    unfold precision
    omega
  · simp only [graph, lookup, wd_word, hw]
    unfold precision
    omega
  · simpa only [wd_word] using Mixer.dictionary_arity _ hd

def pairCost (h k n d : ℕ) := 2 ^ h * n + 2 ^ k * d + 2 * (2 ^ (k + h) * (n + d))

private theorem pairs_net (h k n d : ℕ) :
    Circuit F ((Num h n).pair (Num k d)) (.vec (k + h) (Both n d)) (pairs h k n d)
      (pairCost h k n d) := by
  let A := (Num h n).pair (Num k d)
  let C := Format.vec (k + h) (Both n d)
  have hp : Circuit F A C (pairs h k n d) (A.width + 2 * C.width) :=
    Circuit.project (fun p => Sum.elim
      (fun j => .inl ((Match.rowIndex k h p.1).2, j))
      (fun j => .inr ((Match.rowIndex k h p.1).1, j)) p.2) (by rintro x ⟨i, j|j⟩ <;> rfl)
  simpa only [A, C, pairCost, Num, Both, Format.width_vec, Format.width_pair, Format.width_addr] using hp

def rowCost (h k d : ℕ) := corrCost h d + 4 * (2 ^ k * d) + 4 * pairCost h k (precision h d) d +
  2 ^ (k + h) * (1 + wordLength h d + wordLength h d)

theorem products_map (h k d : ℕ) (hu : 4 * precision h d ≤ u) (hl : (keys F h d : Set _) ⊆ L) :
    Map F u L (Input h k d) (Num (k + h) (wordLength h d)) (products h k d) (rowCost h k d) := by
  have h₃ : 3 ≤ u := by unfold precision at hu; omega
  have ht : Map F u L (Both (precision h d) d) (.addr (wordLength h d)) (times _ _)
      (1 + wordLength h d + wordLength h d) := by
    apply Kernel.mono (gate ?_ (hl (mem_insert_self _ _)))
    · simp [Both]
    · simp only [Both, Format.width_pair, Format.width_addr, wordLength]
      unfold precision at *
      omega
  have hp := Map.circuit (L := L) h₃ (pairs_net (F := F) h k (precision h d) d)
  have hi := Map.circuit (L := L) h₃ (Circuit.id F (Num k d))
  have hc := corr_map h d hu (fun _ hi => hl (mem_insert_of_mem hi))
  have mult := Map.vec (t := k + h) _ (fun _ => ht)
  refine (((hc.par hi).comp hp).comp mult).mono ?_
  simp only [rowCost, Num, Format.width_vec, Format.width_addr, le_refl]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
end

/-!
# Accumulating coefficients before testing mixers

Sum each column over hosts first. The quadratic-size candidate test
on the resulting single table is paid just once. Only the column
sums and the comparisons use long words.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing

open Coloring Finset
open scoped Classical

variable {m k d z : ℕ} (F : Type) [Field F]

abbrev Matrix (m k d : ℕ) := Format.vec m (Num k d)

def collect (x : B m → B k → B d) (i : B k) := total m d (fun j => x j i)

def collectCost (m k d : ℕ) := 2 ^ k * 2 ^ m * (3 * d + (100 + d) ^ 5)

theorem collect_net (m k d : ℕ) :
    Circuit F (Matrix m k d) (Num k (d + m)) collect (collectCost m k d) := by
  let A := Matrix m k d
  let D := Matrix k m d
  have hp : Circuit F A D (fun x i j => x j i) (A.width + 2 * D.width) :=
    Circuit.project (fun t => (t.2.1, t.1, t.2.2)) (fun _ _ => rfl)
  obtain ⟨c, hc, hh⟩ := cheap_total F m d
  have hs := Circuit.map (A := Num m d) (D := .addr (d + m)) (fun _ : B k => total m d)
    (fun _ => hc)
  refine (hp.comp hs).mono ?_
  have ho : c ≤ 2 ^ m * (100 + d) ^ 5 := by omega
  simp only [A, D, Matrix, Num, Format.width_vec, Format.width_addr, collectCost]
  refine (Nat.add_le_add_left (Nat.mul_le_mul_left _ ho) _).trans_eq (by ring)

variable (p : B z → B k → Prop)

def mask (x : B k → B d) (i : B z) (j : B k) : B d := if p i j then x j else 0

def maskCost (k z d : ℕ) := 2 ^ k * d + Install.localCost 1 * (2 ^ z * (2 ^ k * d))

private theorem mask_net (d : ℕ) :
    Circuit F (Num k d) (Matrix z k d) (mask p) (maskCost k z d) := by
  let A := Num k d
  let D := Matrix z k d
  have hm : Install.Depends (D.code ∘ mask p ∘ A.code.symm) 1 := by
    rintro ⟨i, j, t⟩
    refine ⟨{(j, t)}, by simp, fun x y he => ?_⟩
    change (Format.addr d).code (mask p (A.code.symm x) i j) t =
      (Format.addr d).code (mask p (A.code.symm y) i j) t
    unfold mask
    split_ifs
    · change A.code (A.code.symm x) (j, t) = A.code (A.code.symm y) (j, t)
      simpa using he (j, t) (mem_singleton_self _)
    · rfl
  have h : Circuit F A D (mask p) (A.width + Install.localCost 1 * D.width) := hm.bnet F
  simpa only [A, D, Num, Matrix, Format.width_vec, Format.width_addr, maskCost] using h

def minimize (x : B m → B k → B d) := elect ⊥ (mask p (collect x))

def test (x : B m → B k → B d) (i : B z) :=
  ∑ j, if p i j then ∑ v, (x v j).val else 0

theorem minimize_spec (x : B m → B k → B d) (i : B z) :
    test p x (minimize p x) ≤ test p x i := by
  have he q j : (mask p (collect x) q j).val = if p q j then ∑ v, (x v j).val else 0 := by
    unfold mask
    split_ifs <;> rfl
  have hp q : (∑ j, (mask p (collect x) q j).val) = test p x q := sum_congr rfl (fun j _ => he q j)
  rw [← hp, ← hp]
  exact elect_min (mask p (collect x)) i

def testCost (m k d z : ℕ) := collectCost m k d + maskCost k z (d + m) +
  2 ^ z * (2 ^ k * (100 + (d + m)) ^ 5 + (100 + (z + (d + m + k))) ^ 42)

theorem minimize_net (m d : ℕ) :
    Circuit F (Matrix m k d) (.addr z) (minimize p) (testCost m k d z) :=
  ((collect_net F m k d).comp (mask_net F p _)).comp (election F k z (d + m) ⊥)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
end

/-!
# Computing the least-cost mixer

Each row carries a nonnegative integer load at each block and an
integer weight for each depth. Zero weights disable unused depths.
The circuit returns a single common choice, breaking ties by index.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing

open Coloring Finset Packing
open scoped Classical

variable {m h k d : ℕ}

def location (hk : h < 2 ^ k) : Fin (h + 1) × Cell h ↪ B (k + h) :=
  ((Fin.castLEEmb hk).prodMap (cellIndex h).toEmbedding).trans (Match.rowIndex k h).symm.toEmbedding

def keep (hk : h < 2 ^ k) (i : B h) (u : B (k + h)) : Prop :=
  ∃ z, location hk z = u ∧ ancestor z.1.is_le (menu h i z.2) = 0

abbrev Rows (m h k d : ℕ) := Format.vec m (Input h k d)

def choose (hk : h < 2 ^ k) (x : (Rows m h k d).obj) :=
  minimize (keep hk) (fun j => products h k d (x j))

def coefficients (hk : h < 2 ^ k) (x : (Rows m h k d).obj) : Mixer.Coeff h :=
  fun i z => ∑ j, ((products h k d (x j) (location hk (i, z))).val : ℝ)

theorem product_eq (hk : h < 2 ^ k) (x : (Input h k d).obj) (i : Fin (h + 1)) (z : Cell h) :
    (products h k d x (location hk (i, z))).val = (x.2 (Fin.castLE hk i)).val *
      ∑ j, (x.1 (cellIndex h j)).val * (x.1 (cellIndex h (j + z))).val := by
  have hl : Match.rowIndex k h (location hk (i, z)) = (Fin.castLE hk i, cellIndex h z) :=
    (Match.rowIndex k h).apply_symm_apply _
  simp only [products, pairs, hl, times, correlate_eq, mul_comm]

theorem test_eq (hk : h < 2 ^ k) (x : (Rows m h k d).obj) (i : B h) :
    (test (keep hk) (fun j => products h k d (x j)) i : ℝ) =
      Mixer.eval (menu h i) (coefficients hk x) := by
  unfold test
  rw [← sum_subset (subset_univ (univ.map (location hk))), sum_map, Fintype.sum_prod_type]
  · have eq (u : Fin (h + 1)) z :
        keep hk i (location hk (u, z)) ↔ ancestor u.is_le (menu h i z) = 0 := by
      simp [keep]
    push_cast
    simp only [eq]
    rfl
  · intro v _ hv
    apply ite_eq_right
    rintro ⟨z, he, _⟩
    exact hv (mem_map.mpr ⟨z, mem_univ _, he⟩)

theorem choose_le (hk : h < 2 ^ k) (x : (Rows m h k d).obj) (i : B h) :
    Mixer.eval (menu h (choose hk x)) (coefficients hk x) ≤
      Mixer.eval (menu h i) (coefficients hk x) := by
  rw [← test_eq, ← test_eq, Nat.cast_le]
  exact minimize_spec _ _ _

def cost (m h k d : ℕ) :=
  2 ^ m * rowCost h k d + 4 * testCost m (k + h) (wordLength h d) h

/-- The input-scale work is linear in the number of hosts; the exhaustive
search on the block addresses is done only on the aggregated table. -/
theorem compute {F : Type} [Field F] {u : ℕ} {L : Set (Table F)}
    (hk : h < 2 ^ k) (hu : 4 * precision h d ≤ u) (hl : (keys F h d : Set _) ⊆ L) :
    Map F u L (Rows m h k d) (.addr h) (choose hk) (cost m h k d) := by
  have h₃ : 3 ≤ u := by unfold precision at hu; omega
  have r := Map.vec (t := m) _ (fun _ => products_map h k d hu hl)
  exact r.comp (Map.circuit h₃ (minimize_net F (keep hk) m (wordLength h d)))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
end

/-!
# Recovering the reset estimate from integer records

All loads may carry a common positive scale. Each position or
contact contributes one record, and unused records carry zero weight.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing

open Coloring Finset Packing
open scoped Classical

variable {m h k d : ℕ} {V A : Type} [Fintype V] [Fintype A]
  (base : V → ℕ) (q : A → ℕ) (l : V → Cell h → ℝ) (y : A → Cell h → ℝ) (g : ℝ)

def weight (i : Fin (h + 1)) : V ⊕ A → ℝ
  | .inl v => if base v ≤ i.val then 6 * resetWeight (i.val - base v) else 0
  | .inr c => if i.val = q c then 4 * g ^ 2 else 0

def signal := Sum.elim l y

private theorem contribution (i : Fin (h + 1)) (z : Cell h) :
    Mixer.coefficients base q l y g i z =
      ∑ t, weight base q g i t * Mixer.conv (signal l y t) (signal l y t) z := by
  rw [Fintype.sum_sum_type]
  simp only [Mixer.coefficients, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, nsmul_eq_mul, Pi.mul_apply, Pi.ofNat_apply,
    Nat.cast_ofNat, smul_eq_mul, mul_sum, Mixer.atDepth, weight, signal, Sum.elim_inl, Sum.elim_inr]
  congr 1
  · apply sum_congr rfl
    intro v _
    by_cases hi : base v ≤ i.val
    · rw [ite_eq_left hi, sum_eq_single (i.val - base v)]
      · rw [ite_eq_left (by omega)]
        ring
      · intro j _ hj
        rw [ite_eq_right (by omega), mul_zero, mul_zero]
      · have := i.isLt
        simp only [mem_range]
        omega
    · rw [ite_eq_right hi, zero_mul]
      exact sum_eq_zero (fun j _ => by rw [ite_eq_right (by omega), mul_zero, mul_zero])
  · apply sum_congr rfl
    intro c _
    split_ifs <;> ring

structure Encodes (hk : h < 2 ^ k) (x : (Rows m h k d).obj)
    (pos : V ⊕ A ↪ B m) (scale : ℝ) : Prop where
  loads : ∀ t z, signal l y t z = scale * ((x (pos t)).1 (cellIndex h z)).val
  weights : ∀ (i : Fin (h + 1)) t,
    weight base q g i t = ((x (pos t)).2 (Fin.castLE hk i)).val
  vacant : ∀ (i : Fin (h + 1)) j, j ∉ Set.range pos → ((x j).2 (Fin.castLE hk i)).val = 0 ∨
    ∀ z, ((x j).1 (cellIndex h z)).val = 0

variable {base q l y g} {hk : h < 2 ^ k} {x : (Rows m h k d).obj}
  {pos : V ⊕ A ↪ B m} {scale : ℝ}

theorem Encodes.coefficients_eq (e : Encodes base q l y g hk x pos scale) :
    Mixer.coefficients base q l y g = scale ^ 2 • coefficients hk x := by
  funext i z
  rw [contribution]
  simp only [coefficients, Pi.smul_apply, smul_eq_mul]
  rw [← sum_subset (subset_univ (univ.map pos)), sum_map, mul_sum]
  · refine sum_congr rfl (fun t _ => ?_)
    rw [product_eq, e.weights]
    simp only [Mixer.conv, e.loads, Nat.cast_mul, Nat.cast_sum, mul_sum]
    exact sum_congr rfl (fun _ _ => by ring)
  · intro j _ hj
    rw [product_eq]
    rcases e.vacant i j (by simpa using hj) with h | h <;> simp [h]

theorem Encodes.optimal (e : Encodes base q l y g hk x pos scale)
    (hq : ∀ c, q c ≤ h) (t : ℕ) (i : B h) :
    score base q l y g (menu h (choose hk x)).toEquiv t ≤
      score base q l y g (menu h i).toEquiv t := by
  apply sub_nonpos.mp
  rw [Mixer.score_diff _ _ _ _ _ _ _ hq, e.coefficients_eq,
    map_smul, smul_eq_mul, LinearMap.sub_apply]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg scale) (sub_nonpos.mpr (choose_le hk x i))

/-- Computing the winner from short control words gives the same bound
as averaging over nonzero field multipliers. -/
theorem Encodes.bad (e : Encodes base q l y g hk x pos scale)
    (E : V → Finset V) (delay : V → V → ℕ)
    (ends : (Σ c, Cell (q c)) → Bool → Σ v, Cell (base v)) (t : ℕ)
    (drop : ∀ v u, u ∈ E v → base u ≤ base v + 8 * delay v u)
    (budget : ∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (delay v u) else 0) ≤ 1 / 2)
    (hl : ∀ v z, 0 ≤ l v z ∧ l v z ≤ 1 / (2 : ℝ) ^ t)
    (hy : ∀ c z, 0 ≤ y c z ∧ y c z ≤ 1 / (2 : ℝ) ^ t)
    (hb : ∀ v, ∑ z, l v z ≤ (2 : ℝ) ^ (base v))
    (hq : ∀ c, q c ≤ h) (hg : 0 < g) :
    badLoad E delay base q ends l y g (menu h (choose hk x)).toEquiv ≤
      144 * resetWeight t / (2 : ℝ) ^ t * (∑ v, ∑ z, l v z) +
        4 * g ^ 2 / (2 : ℝ) ^ t * (∑ c, ∑ z, y c z) := by
  obtain ⟨i, hi⟩ := exists_score base q l y g hl hy hb hq
  exact (bad_le_score E delay base q ends l y g _ drop budget hl hb hg).trans
    ((e.optimal hq t i).trans hi)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
end

/-!
# From short records to the reset election

A host row carries one header per possible contact and one for its
own load. A header contains a live bit, a contact bit and a depth.
One local record per block suffices to recover all of the loads at
that position. Global host names do not enter the two lookup tables.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing

open Coloring Finset Packing
open scoped Classical

abbrev Header (k : ℕ) := Format.pair .bit (.pair .bit (.addr k))
abbrev Local (e h k s : ℕ) := Format.pair (.vec e (Header k)) (Num h s)
abbrev Records (m e h k s : ℕ) := Format.vec m (Local e h k s)

variable {m e h k s d : ℕ}

def multiplier (g d : ℕ) (r : (Header k).obj) (j : B k) : B d :=
  let i := r.2.2.val
  Fin.ofNat _ (if r.1 then
    if r.2.1 then if j.val = i then 4 * g ^ 2 else 0
    else if i ≤ j.val then 6 * 2 ^ ((j.val - i + 7) / 8) else 0
  else 0)

def header (x : (Records m e h k s).obj) (t : B (m + e)) :=
  (x (Match.rowIndex m e t).1).1 (Match.rowIndex m e t).2

def digit (get : B s → B e → B d) (x : (Records m e h k s).obj) (t : B (m + e)) (z : B h) :=
  get ((x (Match.rowIndex m e t).1).2 z) (Match.rowIndex m e t).2

def rows (g : ℕ) (get : B s → B e → B d) (x : (Records m e h k s).obj) : (Rows (m + e) h k d).obj :=
  fun t => (digit get x t, multiplier g d (header x t))

variable {V A : Type} [Fintype V] [Fintype A] (base : V → ℕ) (q : A → ℕ)
  (l : V → Cell h → ℝ) (y : A → Cell h → ℝ) (g : ℕ) (hk : h < 2 ^ k)
  (get : B s → B e → B d) (x : (Records m e h k s).obj) (pos : V ⊕ A ↪ B (m + e)) (scale : ℝ)

omit [Fintype V] [Fintype A] in
theorem encodes (hb : ∀ v, base v ≤ h) (hq : ∀ c, q c ≤ h)
    (hg : 4 * g ^ 2 < 2 ^ d) (hw : 6 * 2 ^ h < 2 ^ d)
    (heads : ∀ v, header x (pos (.inl v)) = (true, false, ⟨base v, (hb v).trans_lt hk⟩))
    (edges : ∀ c, header x (pos (.inr c)) = (true, true, ⟨q c, (hq c).trans_lt hk⟩))
    (idle : ∀ j, j ∉ Set.range pos → (header x j).1 = false ∨
      ∀ z, (digit get x j (cellIndex h z)).val = 0)
    (loads : ∀ t z, signal l y t z = scale * (digit get x (pos t) (cellIndex h z)).val) :
    Encodes base q l y g hk (rows g get x) pos scale := by
  refine ⟨loads, ?_, ?_⟩
  · intro i t
    rcases t with v | c
    · have ht : 6 * 2 ^ ((i.val - base v + 7) / 8) < 2 ^ d :=
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
          (show (i.val - base v + 7) / 8 ≤ h by have := i.isLt; omega))).trans_lt hw
      by_cases hi : base v ≤ i.val <;> simp [rows, multiplier, heads, weight, hi, resetWeight, Nat.mod_eq_of_lt ht]
    · by_cases hi : i.val = q c <;> simp [rows, multiplier, edges, weight, hi, Nat.mod_eq_of_lt hg]
  · intro i j hj
    rcases idle j hj with h | h
    · left; simp [rows, multiplier, h]
    · exact .inr h

end OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
end

/-! # The load- and weight-extraction network -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing

open Coloring Finset
open scoped Classical

variable {m e h k s d : ℕ} (g : ℕ) (get : B s → B e → B d)

private abbrev Temp (e h k d : ℕ) := Format.pair (Matrix e k d) (Matrix h e d)

private def transpose (x : (Format.vec m (Temp e h k d)).obj) : (Rows (m + e) h k d).obj :=
  fun i => let z := Match.rowIndex m e i
    (fun u => (x z.1).2 u z.2, (x z.1).1 z.2)

def rowKeys (F : Type) [Field F] (h k : ℕ) :=
  insert (graph F (.addr s) (Num e d) get)
    (insert (graph F (Header k) (Num k d) (multiplier g d)) (keys F h d))

theorem rowKeys_size (F : Type) [Field F] (h k : ℕ) : (rowKeys g get F h k).card ≤ 7 :=
  (card_insert_le _ _).trans (Nat.add_le_add_right
    ((card_insert_le _ _).trans (Nat.add_le_add_right (card_keys h d) 1)) 1)

def arity (e h k s d : ℕ) := max (4 * precision h d) (max (s + 2 ^ e * d) (2 + k + 2 ^ k * d))

def extractionCost (m e h k s d : ℕ) :=
  2 ^ m * ((2 ^ e + 2 ^ h) * (1 + arity e h k s d)) +
    4 * ((Format.vec m (Temp e h k d)).width + 2 * (Rows (m + e) h k d).width)

variable {F : Type} [Field F] {u : ℕ} {L : Set (Table F)}

theorem rowKeys_arity {T : Table F} (ht : T ∈ rowKeys g get F h k) :
    wd T.1 + wd T.2.1 ≤ arity e h k s d := by
  unfold arity
  simp only [rowKeys, mem_insert] at ht
  rcases ht with rfl | rfl | ht
  · simp only [graph, lookup, wd_word, Num, Format.width_vec, Format.width_addr]
    omega
  · simp only [graph, lookup, wd_word, Num, Format.width_vec, Format.width_addr, Header, Format.width_pair]
    rw [Format.width_bit]
    omega
  · exact (arity_keys ht).trans (le_max_left _ _)

private theorem transpose_net :
    Circuit F (.vec m (Temp e h k d)) (Rows (m + e) h k d) transpose
      ((Format.vec m (Temp e h k d)).width + 2 * (Rows (m + e) h k d).width) := by
  refine Circuit.project (fun p =>
    ((Match.rowIndex m e p.1).1, p.2.elim
      (fun t => .inr (t.1, (Match.rowIndex m e p.1).2, t.2))
      (fun t => .inl ((Match.rowIndex m e p.1).2, t)))) ?_
  rintro x ⟨i, t|t⟩ <;> rfl

theorem extract (ha : arity e h k s d ≤ u) (hl : (rowKeys g get F h k : Set _) ⊆ L) :
    Map F u L (Records m e h k s) (Rows (m + e) h k d) (rows g get) (extractionCost m e h k s d) := by
  let a := arity e h k s d
  have hu : 3 ≤ u := by unfold arity precision at ha; omega
  have ht (A D : Format) (f : A.obj → D.obj) (hf : graph F A D f ∈ rowKeys g get F h k) :
      Map F u L A D f (1 + a) := by
    have hb : A.width + D.width ≤ a := by
      simpa only [graph, lookup, wd_word] using rowKeys_arity g get hf
    exact (gate (hb.trans ha) (hl hf)).mono (by omega)
  have hd := Map.vec (t := h) _
    (fun _ => ht (.addr s) (Num e d) get (by simp [rowKeys]))
  have hw := Map.vec (t := e) _
    (fun _ => ht (Header k) (Num k d) (multiplier g d) (by simp [rowKeys]))
  have ht' := Map.vec (t := m) _ (fun _ => hw.par hd)
  exact (ht'.comp (Map.circuit hu transpose_net)).mono (by unfold extractionCost; rw [add_mul])

/-- Only the scalar decoder and width parameters enter the seven labels. -/
theorem elect_records (hk : h < 2 ^ k) (ha : arity e h k s d ≤ u)
    (hl : (rowKeys g get F h k : Set _) ⊆ L) :
    Map F u L (Records m e h k s) (.addr h) (choose hk ∘ rows g get)
      (extractionCost m e h k s d + cost (m + e) h k d) :=
  (extract g get ha hl).comp (compute hk ((le_max_left _ _).trans ha)
    (fun _ ht => hl (mem_insert_of_mem (mem_insert_of_mem ht))))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
end

/-!
# Constructing the reset schedule from finite control words

The linear permutation and all base depths are determined from
loads, contact totals and the fixed parameters. No minimization over
completed diagrams is required.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
open Coloring Packing Finset
open scoped Classical

variable {V A U : Type} [Fintype V] [Fintype A] [Fintype U] {h : ℕ}

def depths (E : V → Finset V) (delay : V → V → ℕ) (a k : ℕ) (l : V → Cell h → ℝ) :=
  baseDepths E delay a (h - k) (fun v => ∑ x, l v x)

theorem depths_spec {E : V → Finset V} {delay : V → V → ℕ} {a t : ℕ}
    (budget : ∀ w, ∑ v, (if w ∈ E v then 1 / (2 : ℝ) ^ (delay v w) else 0) ≤ 1 / 2)
    (gap : a + t ≤ h) (l : V → Cell h → ℝ) (hl : ∀ v z, 0 ≤ l v z ∧ l v z ≤ 1 / (2 : ℝ) ^ t) :
    let base := depths E delay a t l
    (∀ v, a ≤ base v ∧ base v ≤ h - t ∧ (∑ x, l v x) ≤ (2 : ℝ) ^ (base v)) ∧
    (∀ v u, u ∈ E v → base u ≤ base v + 8 * delay v u) ∧
    (∑ v, (2 : ℝ) ^ (base v)) ≤ 2 * Fintype.card V * (2 : ℝ) ^ a + 4 * (∑ v, ∑ x, l v x) := by
  apply baseDepths_spec E delay budget a (h - t) (by omega)
  intro v
  refine ⟨sum_nonneg (fun x _ => (hl v x).1), ?_⟩
  calc
    _ ≤ ∑ _x : Cell h, 1 / (2 : ℝ) ^ t := sum_le_sum (fun x _ => (hl v x).2)
    _ = _ := by simp only [sum_const, card_univ, card_cell, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
      mul_one_div, div_eq_iff (by positivity : (2 : ℝ) ^ t ≠ 0), ← pow_add, Nat.sub_add_cancel (by omega : t ≤ h)]

/-- Any sufficiently large dyadic parameter with the given error margin
works. Both data fields are explicit. The remaining fields certify them. -/
def schedule (T : Demands V A U h) (E : V → Finset V) (delay : V → V → ℕ)
    (a t : ℕ) (l : V → Cell h → ℝ) (u g ε : ℝ)
    {m k d : ℕ} (hk : h < 2 ^ k) (x : (Rows m h k d).obj)
    {pos : V ⊕ A ↪ B m} {scale : ℝ}
    (correct : Encodes (depths E delay a t l) (contactDepth (depths E delay a t l) T.ends)
      l (T.amounts u) g hk x pos scale)
    (budget : ∀ w, ∑ v, (if w ∈ E v then 1 / (2 : ℝ) ^ (delay v w) else 0) ≤ 1 / 2)
    (gap : a + t ≤ h) (hl : ∀ v z, 0 ≤ l v z ∧ l v z ≤ 1 / (2 : ℝ) ^ t)
    (inc : ∀ v z, T.incident u v z ≤ l v z) (hu : 0 < u) (hg : 0 < g)
    (small : 144 * resetWeight t / (2 : ℝ) ^ t + 4 * g ^ 2 / (2 : ℝ) ^ t ≤ ε) :
    Schedule T E delay a t l u g ε := by
  let base := depths E delay a t l
  have props := depths_spec budget gap l hl
  refine ⟨base, menu h (choose hk x), fun v => (props.1 v).1, fun v => (props.1 v).2.1,
    fun v => (props.1 v).2.2, props.2.1, props.2.2, ?_, hl, inc, gap, hu, hg⟩
  have hy c z : 0 ≤ T.amounts u c z ∧ T.amounts u c z ≤ 1 / (2 : ℝ) ^ t :=
    ⟨push_nonneg _ _ (fun _ => hu.le) _,
      ((T.amount_le u hu.le c false z).trans (inc _ z)).trans (hl _ z).2⟩
  have hq := T.contact_le base (fun v => ((props.1 v).2.1).trans (Nat.sub_le _ _))
  refine (correct.bad E delay (contactEnd base T.ends) t props.2.1 budget hl hy
    (fun v => (props.1 v).2.2) hq hg).trans ?_
  have mass : 0 ≤ ∑ v, ∑ z, l v z := sum_nonneg (fun v _ => sum_nonneg fun z _ => (hl v z).1)
  have hs : (∑ c, ∑ z, T.amounts u c z) ≤ ∑ v, ∑ z, l v z := by
    refine le_trans ?_ (sum_le_sum fun v _ => sum_le_sum fun z _ => inc v z)
    unfold Demands.amounts Demands.incident
    rw [← Fintype.sum_prod_type (push T.edge _), ← Fintype.sum_prod_type (push _ _),
      sum_push, sum_push]
    simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
    gcongr
    omega
  refine le_trans ?_ (mul_le_mul_of_nonneg_right small mass)
  rw [add_mul]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hs (by positivity)) _

end OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
end
