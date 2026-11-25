import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Preparation
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.LinearAlgebra.MatrixExponent.Sphere.Interpolation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import OAI.LinearAlgebra.MatrixExponent.Sphere.Seam
import Mathlib.Data.List.FinRange
import OAI.LinearAlgebra.MatrixExponent.Sphere.Block
import Mathlib.Tactic.Positivity

section
/-!
# Signs in the transposition of a matrix of generator blocks

Reordering blocks uses only their lengths modulo two. The formula
therefore also applies with doubled energies in place of lengths.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Plant

variable {R α β γ : Type*} [CommRing R] {k : α → α → R}

private theorem contract_tail (f : α → R) (P Q : List α → R) (xs ys : List α)
    (h : ∀ y ∈ ys, f y = 0)
    (e : ∀ zs : List α, zs.Sublist xs → zs.length + 1 = xs.length → P (zs ++ ys) = Q zs) :
    contract f P (xs ++ ys) = contract f Q xs := by
  induction xs generalizing P Q with
  | nil => exact contract_vanish f P ys h
  | cons x xs ih =>
    rw [List.cons_append, contract_cons, contract_cons, e xs (by simp) rfl]
    congr 1
    exact ih _ _ (fun zs hz he => e (x :: zs) (hz.cons_cons x) (by simp [he]))

/-- If no pair crosses a boundary, the perfect matching sum factors. -/
theorem wick_append (xs ys : List α) (h : ∀ x ∈ xs, ∀ y ∈ ys, k x y = 0) :
    wick k (xs ++ ys) = wick k xs * wick k ys := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      simp only [List.length_cons] at hn
      simp only [List.forall_mem_cons] at h
      rw [List.cons_append, wick_cons, wick_cons, mul_comm, ← contract_scale]
      exact contract_tail _ _ _ _ _ h.1 fun zs hz he =>
        (ih zs.length (by omega) zs (fun z ht => h.2 z (hz.subset ht)) rfl).trans (mul_comm _ _)

private theorem parity_length (l : List β) (f : β → List α) (a : β → ℕ)
    (h : ∀ i, (f i).length % 2 = a i % 2) :
    (l.flatMap f).length % 2 = (l.map a).sum % 2 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    exact Nat.ModEq.add (h x) ih

/-- Number of transpositions when interleaving two rows of blocks. -/
def interlace (a b : β → ℕ) : List β → ℕ
  | [] => 0
  | j :: js => (js.map a).sum * b j + interlace a b js

theorem wick_interlace (sk : ∀ x y, k y x = -k x y) (f g : β → List α) (a b : β → ℕ)
    (hf : ∀ i, (f i).length % 2 = a i % 2) (hg : ∀ i, (g i).length % 2 = b i % 2)
    (l : List β) (p q : List α) :
    wick k (p ++ l.flatMap f ++ l.flatMap g ++ q) = (-1 : R) ^ interlace a b l *
      wick k (p ++ l.flatMap (fun i => f i ++ g i) ++ q) := by
  induction l generalizing p with
  | nil => simp [interlace]
  | cons j js ih =>
    have e := wick_swap_blocks sk (p ++ f j) (js.flatMap f) (g j) (js.flatMap g ++ q)
    have t := ih (p ++ f j ++ g j)
    have hs : (-1 : R) ^ ((js.flatMap f).length * (g j).length) = (-1) ^ ((js.map a).sum * b j) := by
      rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two ((js.map a).sum * b j)]
      congr 1
      exact Nat.ModEq.mul (parity_length js f a hf) (hg j)
    rw [hs] at e
    simp only [List.flatMap_cons, List.append_assoc, interlace, pow_add, mul_assoc] at e t ⊢
    rw [e, t]

/-- Transpositions in changing from site order to species order. -/
def shuffle (a : β → γ → ℕ) (cols : List γ) : List β → ℕ
  | [] => 0
  | i :: is => shuffle a cols is + interlace (a i) (fun j => (is.map (a · j)).sum) cols

theorem wick_shuffle (sk : ∀ x y, k y x = -k x y) (f : β → γ → List α) (a : β → γ → ℕ)
    (h : ∀ i j, (f i j).length % 2 = a i j % 2)
    (rows : List β) (cols : List γ) (p q : List α) :
    wick k (p ++ rows.flatMap (fun i => cols.flatMap (f i)) ++ q) =
      (-1 : R) ^ shuffle a cols rows *
        wick k (p ++ cols.flatMap (fun j => rows.flatMap (f · j)) ++ q) := by
  induction rows generalizing p with
  | nil =>
    have e : cols.flatMap (fun _ => ([] : List α)) = [] := by
      induction cols with
      | nil => rfl
      | cons _ _ ih => simp [ih]
    simp [shuffle, e]
  | cons i is ih =>
    have e := ih (p ++ cols.flatMap (f i))
    have t := wick_interlace sk (f i) (fun j => is.flatMap (f · j))
      (a i) (fun j => (is.map (a · j)).sum) (h i)
      (fun j => parity_length is _ _ (fun s => h s j)) cols p q
    simp only [List.flatMap_cons, List.append_assoc, shuffle, pow_add, mul_assoc] at e t ⊢
    rw [e, t]

@[simp] theorem interlace_zero (b : β → ℕ) (l : List β) : interlace (fun _ => 0) b l = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [interlace, ih]

@[simp] theorem shuffle_zero (rows : List β) (cols : List γ) : shuffle (fun _ _ => 0) cols rows = 0 := by
  induction rows with
  | nil => rfl
  | cons x xs ih => simp [shuffle, ih]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Plant
end

section
/-! # Signs within and between blocks of species -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Plant

variable {A B D : Type*}

private theorem interlace_append (a b : A → ℕ) (x y : List A) :
    interlace a b (x ++ y) = interlace a b x + interlace a b y +
      (y.map a).sum * (x.map b).sum := by
  induction x with
  | nil => simp [interlace]
  | cons i x ih => simp [interlace, ih]; ring

private theorem interlace_map (a b : A → ℕ) (f : B → A) (x : List B) :
    interlace a b (x.map f) = interlace (a ∘ f) (b ∘ f) x := by
  induction x with
  | nil => rfl
  | cons i x ih => simp [interlace, ih]

private theorem interlace_blocks (d k : ℕ) (a b : Fin (d * k) → ℕ) :
    interlace a b (List.finRange (d * k)) =
      interlace (fun i => ∑ j, a (finProdFinEquiv (i, j))) (fun i => ∑ j, b (finProdFinEquiv (i, j)))
        (List.finRange d) +
      ∑ i, interlace (fun j => a (finProdFinEquiv (i, j))) (fun j => b (finProdFinEquiv (i, j)))
        (List.finRange k) := by
  let f (i : Fin d) (j : Fin k) := finProdFinEquiv (i, j)
  let v (i : Fin d) := (List.finRange k).map (f i)
  have hv : List.finRange (d * k) = (List.finRange d).flatMap v := by
    have h := List.ofFn_mul (id : Fin (d * k) → Fin (d * k))
    simp only [List.ofFn_eq_map, List.map_id, id_eq] at h
    rw [h]
    congr 2
    funext i
    apply List.map_congr_left
    intro j _
    apply Fin.ext
    simp [f, mul_comm, add_comm]
  have hs (u : Fin (d * k) → ℕ) (i : Fin d) : ((v i).map u).sum = ∑ j, u (f i j) := by
    simp only [v, List.map_map, Function.comp_def]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  have ht (l : List (Fin d)) : ((l.flatMap v).map a).sum = (l.map (fun i => ∑ j, a (f i j))).sum := by
    induction l with
    | nil => rfl
    | cons i l ih => simp [ih, hs]
  have he (l : List (Fin d)) :
      interlace a b (l.flatMap v) =
        interlace (fun i => ∑ j, a (f i j)) (fun i => ∑ j, b (f i j)) l +
          (l.map (fun i => interlace (a ∘ f i) (b ∘ f i) (List.finRange k))).sum := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.flatMap_cons, interlace_append, ih, ht, hs]
      simp only [interlace, List.map_cons, List.sum_cons, v, interlace_map]
      omega
  rw [hv, he]
  simp only [← List.ofFn_eq_map, List.sum_ofFn, Function.comp_def, f]

/-- Once the intra-block signs are known, the remaining sign only
uses the total occupancy of each block at each mark. -/
theorem shuffle_blocks (d b : ℕ) (ε : A → Fin (d * b) → ℕ) (rows : List A) :
    shuffle ε (List.finRange (d * b)) rows =
      shuffle (fun i c => ∑ j : Fin b, ε i (finProdFinEquiv (c, j))) (List.finRange d) rows +
      ∑ c : Fin d, shuffle (fun i j => ε i (finProdFinEquiv (c, j))) (List.finRange b) rows := by
  have commute (f : A → Fin b → ℕ) (l : List A) :
      (∑ j, (l.map (f · j)).sum) = (l.map (fun i => ∑ j, f i j)).sum := by
    induction l with
    | nil => simp
    | cons i l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
  induction rows with
  | nil => simp [shuffle]
  | cons i rows ih =>
    simp only [shuffle, ih, interlace_blocks d b, Finset.sum_add_distrib]
    have h (c : Fin d) := commute (fun i j => ε i (finProdFinEquiv (c, j))) rows
    simp only [h]
    omega

end OAI.LinearAlgebra.MatrixExponent.Sphere.Plant
end

section
/-!
# One auxiliary probe per coded mode

The covectors are prescribed only on the mode prefixes used in the
fixed-energy codes. The remaining modes have higher normalized weight.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Plant

open Finset

theorem probe_basis {F : Type*} [Field F] {m n : ℕ} (z : Fin m ↪ F) (y : Fin n ↪ F)
    (hz : ∀ i j, y j ≠ z i) (b : Fin m → ℕ) (hn : (∑ i, 4 * b i) ≤ n) (v : Mode m → F) :
    ∃ c : Fin n → F, ∀ i : Mode m, i.2 < 4 * b i.1 →
      (∑ j, c j * (y j - z i.1)⁻¹ ^ (i.2 + 1)) = v i := by
  classical
  let T := Σ i, Fin (4 * b i)
  let h : T ↪ F × ℕ := ⟨fun x => (z x.1, x.2.val), by
    rintro ⟨i, k⟩ ⟨j, l⟩ e
    have : i = j := z.injective (congrArg Prod.fst e)
    subst j
    rw [show k = l from Fin.ext (congrArg Prod.snd e)]⟩
  let q (x : F) := ∑ i, if z i = x then 4 * b i else 0
  have hq (i) : q (z i) = 4 * b i := by simp [q, z.injective.eq_iff]
  have hd : ∑ x ∈ univ.image z, q x ≤ Fintype.card (Fin n) := by
    simpa only [sum_image z.injective.injOn, hq, Fintype.card_fin] using hn
  let p (j : Fin n) (x : T) := (y j - z x.1)⁻¹ ^ (x.2.val + 1)
  have he : Submodule.span F (Set.range p) = ⊤ :=
    cauchy_span_degrees h y (univ.image z) q
      (fun i => mem_image_of_mem _ (mem_univ i.1))
      (fun i => by change i.2.val < q (z i.1); rw [hq]; exact i.2.isLt)
      (fun j i => hz i.1 j) hd
  have hm : (fun x : T => v (x.1, x.2.val)) ∈ Submodule.span F (Set.range p) := by simp [he]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hm
  refine ⟨c, fun i hi => ?_⟩
  simpa [p, Finset.sum_apply] using congrFun hc ⟨i.1, ⟨i.2, hi⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Plant
end

section
/-! # Ordered wedges and their single-species components -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Plant

variable {r : ℕ}

def place (i : Fin r) (x : Mode 1) : Mode r := (i, x.2)

private theorem lt_one {x y : Mode 1} : toLex x < toLex y ↔ x.2 < y.2 := by
  rw [Prod.Lex.toLex_lt_toLex, Subsingleton.elim x.1 y.1]
  simp

def pack (u : Fin r → Wedge 1) : Wedge r := by
  refine ⟨(List.finRange r).flatMap (fun i => (u i).val.map (place i)), ?_⟩
  rw [List.pairwise_flatMap]
  constructor
  · intro i _
    apply List.pairwise_map.mpr
    refine (u i).property.imp ?_
    intro x y h
    exact Prod.Lex.toLex_lt_toLex.mpr (.inr ⟨rfl, lt_one.mp h⟩)
  · refine (List.sortedLT_finRange r).pairwise.imp ?_
    intro i j h x hx y hy
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
    exact Prod.Lex.toLex_lt_toLex.mpr (.inl h)

def slice (u : Wedge r) (i : Fin r) : Wedge 1 := by
  refine ⟨(u.val.filter (fun x => x.1 = i)).map (fun x => (0, x.2)), ?_⟩
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ (u.property.filter _)
  intro x y hx hy h
  apply lt_one.mpr
  simp only [List.mem_filter, decide_eq_true_eq] at hx hy
  simpa [Prod.Lex.toLex_lt_toLex, hx.2, hy.2] using h

theorem wedge_perm {u v : Wedge r} (h : u.val.Perm v.val) : u = v :=
  Subtype.ext (h.eq_of_pairwise (fun _ _ _ _ h ht => (h.asymm ht).elim) u.property v.property)

theorem mem_pack (u : Fin r → Wedge 1) (i : Fin r) (m : ℕ) :
    (i, m) ∈ (pack u).val ↔ (0, m) ∈ (u i).val := by
  simp only [pack, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro ⟨j, ⟨k, n⟩, h, eq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    exact Subsingleton.elim k 0 ▸ h
  · exact fun h => ⟨i, (0, m), h, rfl⟩

theorem mem_slice (u : Wedge r) (i : Fin r) (m : ℕ) :
    (0, m) ∈ (slice u i).val ↔ (i, m) ∈ u.val := by
  simp [slice]

@[simp] theorem pack_slice (u : Wedge r) : pack (slice u) = u := by
  apply wedge_perm
  apply (List.perm_ext_iff_of_nodup (pack _).nodup u.nodup).mpr
  rintro ⟨i, m⟩
  rw [mem_pack, mem_slice]

@[simp] theorem slice_pack (u : Fin r → Wedge 1) (i : Fin r) : slice (pack u) i = u i := by
  apply wedge_perm
  apply (List.perm_ext_iff_of_nodup (slice _ _).nodup (u i).nodup).mpr
  rintro ⟨j, m⟩
  rw [Subsingleton.elim j 0, mem_slice, mem_pack]

theorem sum_pack {M : Type*} [AddCommMonoid M] (f : Mode r → M) (u : Fin r → Wedge 1) :
    ((pack u).val.map f).sum = ∑ i, ((u i).val.map (fun x => f (place i x))).sum := by
  have h (l : List (Fin r)) :
      ((l.flatMap (fun i => (u i).val.map (place i))).map f).sum =
        (l.map (fun i => ((u i).val.map (fun x => f (place i x))).sum)).sum := by
    induction l with
    | nil => rfl
    | cons j l ih => simp [List.map_map, Function.comp_def, ih]
  simp only [pack, h, ← List.ofFn_eq_map, List.sum_ofFn]

theorem energy_pack (u : Fin r → Wedge 1) : energy (pack u).val = ∑ i, energy (u i).val := by
  unfold energy
  rw [sum_pack]
  rfl

theorem length_pack (u : Fin r → Wedge 1) : (pack u).val.length = ∑ i, (u i).val.length := by
  simp [pack, List.length_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Plant
end

section
/-! # Factorization of the sphere form into independent species -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Plant

variable {F A : Type*} [Field F] {r : ℕ}

def put (j : Fin r) (x : Site F 1) : Site F r := (x.1, place j x.2)

private theorem kernel_put (j : Fin r) (x y : Site F 1) :
    fieldKernel (put j x) (put j y) = fieldKernel x y := by
  simp [fieldKernel, coeff, put, place, Subsingleton.elim x.2.1 y.2.1]

private theorem columns (xs : Fin r → List (Site F 1)) :
    wick fieldKernel ((List.finRange r).flatMap (fun j => (xs j).map (put j))) =
      ∏ j, wick fieldKernel (xs j) := by
  have aux (l : List (Fin r)) (h : l.Nodup) :
      wick fieldKernel (l.flatMap (fun j => (xs j).map (put j))) =
        (l.map (fun j => wick fieldKernel (xs j))).prod := by
    induction l with
    | nil => simp
    | cons j l ih =>
      rw [List.flatMap_cons, wick_append, ih (List.nodup_cons.mp h).2, wick_map]
      · simp only [kernel_put, List.map_cons, List.prod_cons]
      · intro x hx y hy
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨i, hi, hy⟩ := List.mem_flatMap.mp hy
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hy
        have hn : j ≠ i := fun e => (List.nodup_cons.mp h).1 (e ▸ hi)
        simp [put, place, fieldKernel, coeff, hn]
  simpa only [← List.ofFn_eq_map, List.prod_ofFn] using aux _ (List.nodup_finRange r)

def bundle (z : A → F) (X : A → Wedge r) (l : List A) : List (Site F r) :=
  l.flatMap (fun i => (X i).val.map (z i, ·))

private theorem bundle_shuffle (z : A → F) (X : A → Fin r → Wedge 1) (e : A → Fin r → ℕ)
    (h : ∀ i j, (X i j).val.length % 2 = e i j % 2) (l : List A) (p q : List (Site F r)) :
    wick fieldKernel (p ++ bundle z (fun i => pack (X i)) l ++ q) =
      (-1 : F) ^ shuffle e (List.finRange r) l *
        wick fieldKernel (p ++ (List.finRange r).flatMap
          (fun j => (bundle z (X · j) l).map (put j)) ++ q) := by
  let f i j := (X i j).val.map (fun x => (z i, place j x))
  have hm (i j) : (f i j).length % 2 = e i j % 2 := by simpa [f] using h i j
  simpa [bundle, pack, f, put, List.map_flatMap, List.map_map, Function.comp_def] using
    wick_shuffle fieldKernel_skew f e hm l (List.finRange r) p q

/-- The sign only uses the parities of the individual wedges. -/
theorem wick_species (z : A → F) (X : A → Fin r → Wedge 1) (e : A → Fin r → ℕ)
    (h : ∀ i j, (X i j).val.length % 2 = e i j % 2) (l : List A) :
    wick fieldKernel (l.flatMap (fun i => (pack (X i)).val.map (z i, ·))) =
      (-1 : F) ^ shuffle e (List.finRange r) l *
        ∏ j, wick fieldKernel (l.flatMap (fun i => (X i j).val.map (z i, ·))) := by
  have he := bundle_shuffle z X e h l [] []
  simp only [List.nil_append, List.append_nil, columns] at he
  exact he

/-- When the first group has even length in every species, its
shuffle sign and the second group's shuffle sign are independent. -/
theorem wick_two_groups {B : Type*} (z : A → F) (y : B → F)
    (X : A → Fin r → Wedge 1) (Y : B → Fin r → Wedge 1) (l : List A) (m : List B)
    (a : A → Fin r → ℕ) (b : B → Fin r → ℕ)
    (ha : ∀ i j, (X i j).val.length % 2 = a i j % 2)
    (hb : ∀ i j, (Y i j).val.length % 2 = b i j % 2)
    (he : ∀ j, (bundle z (X · j) l).length % 2 = 0) :
    wick fieldKernel (bundle z (fun i => pack (X i)) l ++ bundle y (fun i => pack (Y i)) m) =
      (-1 : F) ^ shuffle a (List.finRange r) l * (-1) ^ shuffle b (List.finRange r) m *
        ∏ j, wick fieldKernel (bundle z (X · j) l ++ bundle y (Y · j) m) := by
  let f j := (bundle z (X · j) l).map (put j)
  let g j := (bundle y (Y · j) m).map (put j)
  have h₁ := bundle_shuffle z X a ha l [] (bundle y (fun i => pack (Y i)) m)
  have h₂ := bundle_shuffle y Y b hb m ((List.finRange r).flatMap f) []
  have h₃ := wick_interlace fieldKernel_skew f g (fun _ => 0) (fun j => (g j).length)
    (fun j => by simp [f, he]) (fun _ => rfl) (List.finRange r) [] []
  simp only [List.nil_append, List.append_nil, interlace_zero, pow_zero, one_mul] at h₁ h₂ h₃
  rw [h₁, h₂, h₃, mul_assoc]
  simp only [f, g, ← List.map_append, columns]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Plant
end

/-!
# Planting one species with linearly many auxiliary marks

Site `i` carries `b i` coded bits, using the first `4 * b i` modes.
After rescaling weights at each site, all tested modes cost at most
eight and every untested mode costs strictly more. Thus interpolation
of just the tested modes suffices under a total weighted budget.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Plant

open Finset
open scoped Classical
variable {F : Type*} [Field F] {m n d : ℕ}

instance : Fintype (Probe n d) := by
  refine Fintype.ofInjective (fun x : Probe n d => (x.val.val.map Prod.fst).toFinset) ?_
  intro x y h
  apply Subtype.ext
  apply wedge_perm
  apply (List.perm_ext_iff_of_nodup x.val.nodup y.val.nodup).mpr
  have he (x : Probe n d) (i : Fin n) (j : ℕ) :
      (i, j) ∈ x.val.val ↔ i ∈ (x.val.val.map Prod.fst).toFinset ∧ j = 0 := by
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · exact fun h => ⟨⟨_, h, rfl⟩, x.property.1 _ h⟩
    · rintro ⟨⟨⟨k, j⟩, h, rfl⟩, rfl⟩
      exact (show j = 0 from x.property.1 _ h) ▸ h
  rintro ⟨i, j⟩
  dsimp only at h
  rw [he, he, h]

abbrev Bits (b : Fin m → ℕ) := ∀ i, Fin (b i) → Bool

def coded (b : Fin m → ℕ) (x : Bits b) : Wedge m :=
  pack (fun i => (bitCode (b i) (x i)).val)

def unitCost (n : ℕ) : ℝ := if n = 0 then 9 else (n : ℝ)⁻¹

def price (b : Fin m → ℕ) (x : Mode m) : ℝ := (2 * x.2 + 1) * unitCost (b x.1)

def cost (b : Fin m → ℕ) (x : Wedge m) : ℝ := (x.val.map (price b)).sum

def budget (b : Fin m → ℕ) : ℝ := ∑ i, (8 * b i ^ 2 : ℕ) * unitCost (b i)

private theorem price_pos (b : Fin m → ℕ) (x : Mode m) : 0 < price b x := by
  unfold price unitCost
  split_ifs <;> positivity

private theorem small (b : Fin m → ℕ) (x : Mode m) : price b x ≤ 8 ↔ x.2 < 4 * b x.1 := by
  unfold price unitCost
  split_ifs with h
  · have := Nat.cast_nonneg (α := ℝ) x.2
    simp only [h, mul_zero, Nat.not_lt_zero, iff_false]
    linarith
  · rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have : 2 * x.2 + 1 ≤ 8 * b x.1 ↔ x.2 < 4 * b x.1 := by omega
    exact_mod_cast this

theorem cost_pack (b : Fin m → ℕ) (x : Fin m → Wedge 1) :
    cost b (pack x) = ∑ i, energy (x i).val * unitCost (b i) := by
  unfold cost
  rw [sum_pack]
  refine sum_congr rfl fun i _ => ?_
  induction (x i).val with
  | nil => simp [energy]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simp [energy, place, price, add_mul]

theorem cost_coded (b : Fin m → ℕ) (x : Bits b) : cost b (coded b x) = budget b := by
  rw [coded, cost_pack]
  exact sum_congr rfl fun i _ => by rw [(bitCode _ (x i)).property]

def slots (z : Fin m → F) (i : Mode m) : F × ℕ := (z i.1, i.2)

variable (z : Fin m ↪ F) (y : Fin n ↪ F) (hz : ∀ i j, y j ≠ z i)
variable (b : Fin m → ℕ) (hn : (∑ i, 4 * b i) ≤ n)

include hz hn in
theorem selector (x : Bits b) :
    ∃ c : Probe n (∑ i, 2 * b i) → F, ∀ w : Wedge m, cost b w ≤ budget b →
      ∑ p, c p * probeEval (slots z) y p w.val = if coded b x = w then 1 else 0 := by
  let delta (i j : Mode m) : F := if i = j then -1 else 0
  choose t ht using fun i => probe_basis z y hz b hn (delta i)
  let row (i j : Mode m) := if price b i ≤ 8 then
    ∑ k, t i k * (y k - z j.1)⁻¹ ^ (j.2 + 1) else delta i j
  have tri (i j) (h : price b j ≤ price b i) : -row i j = if i = j then 1 else 0 := by
    have he : row i j = delta i j := by
      unfold row
      split_ifs with hi
      · exact ht i j ((small b j).mp (h.trans hi))
      · rfl
    rw [he]
    simp only [delta, neg_ite, neg_neg, neg_zero]
  let u := coded b x
  have len : u.val.length = ∑ i, 2 * b i := by simp [u, coded, length_pack, bitCode_length]
  have even : u.val.length % 2 = 0 := by rw [len, ← mul_sum]; omega
  have hc (i : Mode m) (hi : i ∈ u.val) : ∃ c : Fin n → F,
      ∀ j, ∑ k, c k * (y k - (slots z j).1)⁻¹ ^ ((slots z j).2 + 1) = row i j := by
    have hp : price b i ≤ 8 := by
      apply (small b i).mpr
      rcases i with ⟨l, j⟩
      exact bitCode_support (x l) (0, j) ((mem_pack _ l j).mp hi)
    exact ⟨t i, fun j => (ite_eq_left hp).symm⟩
  obtain ⟨c, he⟩ := weighted_probe (slots z) y (price b) (price_pos b) _ u.nodup len.le even row tri hc
  refine ⟨c, fun w hw => ?_⟩
  have h : cost b w ≤ cost b u := by rw [cost_coded]; exact hw
  have key := he w.val (fun h => congrArg Subtype.val (wedge_perm h)) h
  rw [sum_subset (subset_univ _) (fun p _ hp => by rw [Finsupp.notMem_support_iff.mp hp, zero_mul])] at key
  simpa only [show u.val = w.val ↔ u = w from Subtype.ext_iff.symm] using key

/-- Extend a bit table by zero to all unrecognized words. -/
def decoded (L : Bits b → F) (w : Wedge m) : F :=
  ∑ x, if coded b x = w then L x else 0

theorem coded_injective : Function.Injective (coded b) := by
  intro x y h
  funext i
  apply (bitCode _).injective
  apply Subtype.ext
  simpa only [coded, slice_pack] using congrArg (fun z => slice z i) h

@[simp] theorem decoded_coded (L : Bits b → F) (x : Bits b) :
    decoded b L (coded b x) = L x := by
  simp [decoded, (coded_injective b).eq_iff]

theorem exists_code {L : Bits b → F} {w : Wedge m} (h : decoded b L w ≠ 0) :
    ∃ x, coded b x = w := by
  by_contra! hn
  simp [decoded, hn] at h

include hz hn in
theorem plant_one (L : Bits b → F) :
    ∃ c : Probe n (∑ i, 2 * b i) → F, ∀ w : Wedge m, cost b w ≤ budget b →
      ∑ p, c p * probeEval (slots z) y p w.val = decoded b L w := by
  choose t ht using selector z y hz b hn
  refine ⟨fun p => ∑ x, L x * t x p, fun w hw => ?_⟩
  simp only [sum_mul, mul_assoc]
  rw [sum_comm]
  simp only [← mul_sum, ht _ w hw, mul_ite, mul_one, mul_zero, decoded]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Plant
end

/-! # Occupancy words for the auxiliary marks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Plant

open Finset
open scoped Classical
variable {m n d r : ℕ} {F : Type*} [Field F]

def lowest : Bool → Wedge 1
  | false => ⟨[], by simp⟩
  | true => ⟨[(0, 0)], by simp⟩

@[simp] theorem energy_lowest (x : Bool) : energy (lowest x).val = x.toNat := by cases x <;> rfl
@[simp] theorem length_lowest (x : Bool) : (lowest x).val.length = x.toNat := by cases x <;> rfl

def occupancy (x : Fin r → Bool) : Wedge r := pack (fun j => lowest (x j))

theorem energy_occupancy (x : Fin r → Bool) : energy (occupancy x).val = ∑ j, (x j).toNat := by
  rw [occupancy, energy_pack]
  simp only [energy_lowest]

theorem length_occupancy (x : Fin r → Bool) : (occupancy x).val.length = ∑ j, (x j).toNat := by
  rw [occupancy, length_pack]
  simp only [length_lowest]

theorem occupancy_injective : Function.Injective (occupancy (r := r)) := by
  intro x y h
  funext j
  have he := congrArg (fun p => (slice p j).val.length) h
  simp only [occupancy, slice_pack, length_lowest] at he
  cases hx : x j <;> cases hy : y j <;> simp_all

def probeBit (p : Probe n d) (i : Fin n) := decide ((i, 0) ∈ p.val.val)

theorem occupancy_probe (p : Probe n d) : occupancy (probeBit p) = p.val := by
  apply wedge_perm
  apply (List.perm_ext_iff_of_nodup (occupancy _).nodup p.val.nodup).mpr
  rintro ⟨i, j⟩
  rw [occupancy, mem_pack]
  by_cases h : (i, 0) ∈ p.val.val
  · simp [probeBit, h, lowest]
    exact ⟨fun he => he ▸ h, fun he => p.property.1 _ he⟩
  · simp [probeBit, h, lowest]
    exact fun he => h ((show j = 0 from p.property.1 _ he) ▸ he)

omit [Field F] in
theorem bundle_pack (z : Fin m → F) (x : Fin m → Wedge 1) :
    bundle z x (List.finRange m) = (pack x).val.map (mark (slots z)) := by
  simp only [bundle, pack, List.map_flatMap, List.map_map, Function.comp_def, mark, slots, place]
  congr 1
  funext i
  refine List.map_congr_left fun j _ => ?_
  exact congrArg (z i, ·) (Prod.ext (Subsingleton.elim _ _) rfl)

/-- The contribution of one species of the auxiliary state. -/
def response (z : Fin m → F) (y : Fin n → F) (J : (Fin n → Bool) → F) (w : Wedge m) : F :=
  ∑ x, J x * wick fieldKernel
    ((occupancy x).val.map (mark (slots y)) ++ w.val.map (mark (slots z)))

theorem plant_bits (z : Fin m ↪ F) (y : Fin n ↪ F) (hz : ∀ i j, y j ≠ z i)
    (b : Fin m → ℕ) (hn : (∑ i, 4 * b i) ≤ n) (L : Bits b → F) :
    ∃ J : (Fin n → Bool) → F,
      (∀ x, J x ≠ 0 → (∑ j, (x j).toNat) ≤ (∑ i, 2 * b i) ∧ (∑ j, (x j).toNat) % 2 = 0) ∧
      ∀ w, cost b w ≤ budget b → response z y J w = decoded b L w := by
  obtain ⟨c, hc⟩ := plant_one z y hz b hn L
  let J x := ∑ p, if x = probeBit p then c p else 0
  refine ⟨J, ?_, fun w hw => ?_⟩
  · intro x hx
    obtain ⟨p, _, h⟩ := exists_ne_zero_of_sum_ne_zero hx
    have : x = probeBit p := by by_contra hn; simp [hn] at h
    rw [← length_occupancy, this, occupancy_probe]
    exact p.property.2
  unfold response J
  simp only [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq', mem_univ, ite_true, occupancy_probe]
  exact hc w hw

end OAI.LinearAlgebra.MatrixExponent.Sphere.Plant
end

/-!
# Planting across independent species

Only the total energy at each original mark is fixed. This fixes the
total weight across species. If one species exceeds its budget, a
second is under budget and its selector vanishes. Thus exact levels
at every mark in every species follow without a separate check on
each seam.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Plant

open Finset
open scoped Classical
variable {F : Type*} [Field F] {r m n : ℕ}

def column (X : Fin m → Wedge r) (j : Fin r) := pack (fun i => slice (X i) j)

private theorem total_cost (b : Fin m → ℕ) (X : Fin m → Wedge r)
    (hX : ∀ i, energy (X i).val = r * (8 * b i ^ 2)) :
    ∑ j, cost b (column X j) = ∑ _ : Fin r, budget b := by
  simp only [column, cost_pack]
  rw [sum_comm]
  simp only [← sum_mul, ← Nat.cast_sum, ← energy_pack, pack_slice, hX, Nat.cast_mul, budget,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sum, mul_assoc]

private theorem budget_guard (b : Fin m → ℕ) (L : Bits b → F) (f : Wedge m → F)
    (hf : ∀ x, cost b x ≤ budget b → f x = decoded b L x)
    (X : Fin m → Wedge r) (hX : ∀ i, energy (X i).val = r * (8 * b i ^ 2)) :
    ∏ j, f (column X j) = ∏ j, decoded b L (column X j) := by
  by_cases he : ∀ j, cost b (column X j) ≤ budget b
  · exact prod_congr rfl fun j _ => hf _ (he j)
  push Not at he
  obtain ⟨j, hj⟩ := he
  obtain ⟨i, hi⟩ : ∃ i, cost b (column X i) < budget b := by
    by_contra! nh
    have h := sum_lt_sum (s := univ) (fun i _ => nh i) ⟨j, mem_univ j, hj⟩
    exact (total_cost b X hX).not_gt h
  have z : decoded b L (column X i) = 0 := by
    by_contra hn
    obtain ⟨v, hv⟩ := exists_code b hn
    rw [← hv, cost_coded] at hi
    exact hi.false
  rw [prod_eq_zero (mem_univ i) ((hf _ hi.le).trans z), prod_eq_zero (mem_univ i) z]

/-- Sign exponent of the auxiliary occupancy table. -/
def auxSign (x : Fin n → Fin r → Bool) :=
  shuffle (fun i j => (x i j).toNat) (List.finRange r) (List.finRange n)

private def originalSign (X : Fin m → Wedge r) :=
  shuffle (fun i j => (slice (X i) j).val.length % 2) (List.finRange r) (List.finRange m)

private theorem on_codes (b : Fin m → ℕ) (L : Bits b → F) (X : Fin m → Wedge r)
    (h : ∏ j, decoded b L (column X j) ≠ 0) : originalSign X = 0 := by
  have e (i j) : (slice (X i) j).val.length % 2 = 0 := by
    obtain ⟨v, hv⟩ := exists_code b (prod_ne_zero_iff.mp h j (mem_univ _))
    have ht := congrArg (fun x => slice x i) hv
    simp only [coded, column, slice_pack] at ht
    rw [← ht, bitCode_length]
    omega
  simp only [originalSign, e, shuffle_zero]

/-- A joint state on auxiliary sites. Each coefficient factors over
species, apart from the known shuffle sign. -/
def joint (J : (Fin n → Bool) → F) (x : Fin n → Fin r → Bool) : F :=
  (-1) ^ auxSign x * ∏ j, J (x · j)

private theorem joint_sphere (J : (Fin n → Bool) → F)
    (hJ : ∀ x, J x ≠ 0 → (∑ i, (x i).toNat) % 2 = 0)
    (z : Fin m → F) (y : Fin n → F) (X : Fin m → Wedge r) :
    (∑ x : Fin n → Fin r → Bool, joint J x * wick fieldKernel
      (bundle y (fun i => occupancy (x i)) (List.finRange n) ++ bundle z X (List.finRange m))) =
      (-1 : F) ^ originalSign X * ∏ j, response z y J (column X j) := by
  let k (j : Fin r) (v : Fin n → Bool) := wick fieldKernel
    ((occupancy v).val.map (mark (slots y)) ++ (column X j).val.map (mark (slots z)))
  have term (x : Fin n → Fin r → Bool) :
      joint J x * wick fieldKernel
        (bundle y (fun i => occupancy (x i)) (List.finRange n) ++ bundle z X (List.finRange m)) =
        (-1 : F) ^ originalSign X * ∏ j, J (x · j) * k j (x · j) := by
    rw [joint, prod_mul_distrib]
    by_cases h : ∏ j, J (x · j) = 0
    · simp [h]
    let U i j := lowest (x i j)
    let V i j := slice (X i) j
    have even (j) : (bundle y (U · j) (List.finRange n)).length % 2 = 0 := by
      rw [bundle_pack, List.length_map, length_pack]
      simp only [U, length_lowest]
      exact hJ (x · j) (prod_ne_zero_iff.mp h j (mem_univ _))
    have he := wick_two_groups y z U V (List.finRange n) (List.finRange m)
      (fun i j => (x i j).toNat) (fun i j => (slice (X i) j).val.length % 2)
      (fun i j => by simp [U]) (fun i j => by simp [V]) even
    simp only [V, pack_slice, bundle_pack] at he
    change wick fieldKernel
      (bundle y (fun i => occupancy (x i)) (List.finRange n) ++ bundle z X (List.finRange m)) =
      (-1 : F) ^ auxSign x * (-1) ^ originalSign X * ∏ j, k j (x · j) at he
    rw [he, mul_mul_mul_comm, ← mul_assoc ((-1 : F) ^ auxSign x) ((-1 : F) ^ auxSign x),
      ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  simp only [term, ← mul_sum]
  congr 1
  change _ = ∏ j, ∑ v, J v * k j v
  rw [Fintype.prod_sum]
  let E : (Fin n → Fin r → Bool) ≃ (Fin r → Fin n → Bool) := ⟨fun x j i => x i j,
    fun x i j => x j i, fun _ => rfl, fun _ => rfl⟩
  exact E.sum_comp (fun x => ∏ j, J (x j) * k j (x j))

/-- Linear-size auxiliary positions and a product state enforce the
prescribed bit table on each species, given only total leg energies.
The same one-species state works for every replication count. -/
theorem plant_joint (z : Fin m ↪ F) (y : Fin n ↪ F) (hz : ∀ i j, y j ≠ z i)
    (b : Fin m → ℕ) (hn : (∑ i, 4 * b i) ≤ n) (L : Bits b → F) :
    ∃ J : (Fin n → Bool) → F,
      (∀ x, J x ≠ 0 → (∑ j, (x j).toNat) ≤ (∑ i, 2 * b i) ∧ (∑ j, (x j).toNat) % 2 = 0) ∧
      ∀ (r : ℕ) (X : Fin m → Wedge r), (∀ i, energy (X i).val = r * (8 * b i ^ 2)) →
      (∑ x : Fin n → Fin r → Bool, joint J x * wick fieldKernel
        (bundle y (fun i => occupancy (x i)) (List.finRange n) ++ bundle z X (List.finRange m))) =
        ∏ j, decoded b L (column X j) := by
  obtain ⟨J, hJ, he⟩ := plant_bits z y hz b hn L
  refine ⟨J, hJ, fun r X hX => ?_⟩
  rw [joint_sphere J (fun x hx => (hJ x hx).2), budget_guard b L _ he X hX]
  by_cases h : ∏ j, decoded b L (column X j) = 0
  · rw [h, mul_zero]
  · rw [on_codes b L X h, pow_zero, one_mul]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Plant
end

/-! # Wiring coordinates on the original marks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Plant

open Finset
open scoped Classical
variable {F : Type*} [Field F] {m n r : ℕ}

abbrev bitsAt (n r : ℕ) := Fin r → Fin n → Bool

/-- Encode one packet for every species at a fixed total energy. -/
def markCode (n r : ℕ) : bitsAt n r ↪ Level r (r * (8 * n ^ 2)) where
  toFun x := ⟨pack (fun j => (bitCode n (x j)).val), by
    rw [energy_pack]
    have h (j : Fin r) := (bitCode n (x j)).property
    simp [h]⟩
  inj' x y h := coded_injective (fun _ => n) (congrArg Subtype.val h)

private theorem eq_pack (u : Fin r → Wedge 1) (w : Wedge r) :
    pack u = w ↔ ∀ i, u i = slice w i := by
  constructor
  · rintro rfl i
    exact (slice_pack u i).symm
  · intro h
    rw [funext h, pack_slice]

private theorem code_iff (b : Fin m → ℕ) (X : ∀ i, Level r (r * (8 * b i ^ 2)))
    (σ : ∀ i, bitsAt (b i) r) :
    (∀ i, markCode (b i) r (σ i) = X i) ↔
      ∀ j, coded b (fun i => σ i j) = column (fun i => (X i).val) j := by
  have e (i) : markCode (b i) r (σ i) = X i ↔
      ∀ j, (bitCode (b i) (σ i j)).val = slice (X i).val j := by
    rw [Subtype.ext_iff]
    exact eq_pack _ _
  simp only [e, coded, eq_pack, column, slice_pack]
  exact forall_comm

/-- Sum over all coded, independently addressable packets. Any assignment
that disagrees with any original mark contributes zero. -/
theorem joint_decoded (z : Fin m ↪ F) (y : Fin n ↪ F) (hz : ∀ i j, y j ≠ z i)
    (b : Fin m → ℕ) (hn : (∑ i, 4 * b i) ≤ n) (L : Bits b → F) :
    ∃ J : (Fin n → Bool) → F,
      (∀ x, J x ≠ 0 → (∑ j, (x j).toNat) ≤ (∑ i, 2 * b i) ∧ (∑ j, (x j).toNat) % 2 = 0) ∧
      ∀ (r : ℕ) (X : ∀ i, Level r (r * (8 * b i ^ 2))),
      (∑ x : Fin n → Fin r → Bool, joint J x * wick fieldKernel
        (bundle y (fun i => occupancy (x i)) (List.finRange n) ++
          bundle z (fun i => (X i).val) (List.finRange m))) =
        ∑ σ : (i : Fin m) → bitsAt (b i) r,
          if ∀ i, markCode (b i) r (σ i) = X i then ∏ j, L (fun i => σ i j) else 0 := by
  obtain ⟨J, hJ, h⟩ := plant_joint z y hz b hn L
  refine ⟨J, hJ, fun r X => ?_⟩
  rw [h _ _ (fun i => (X i).property)]
  unfold decoded
  rw [Fintype.prod_sum]
  let E : (∀ i, bitsAt (b i) r) ≃ (Fin r → Bits b) :=
    ⟨fun x j i => x i j, fun x i j => x j i, fun _ => rfl, fun _ => rfl⟩
  rw [← E.sum_comp]
  refine sum_congr rfl fun σ _ => ?_
  simp only [code_iff b X σ]
  change (∏ j, if coded b (fun i => σ i j) = column (fun i => (X i).val) j
    then L (fun i => σ i j) else 0) = _
  split_ifs with hσ
  · exact prod_congr rfl fun j _ => ite_eq_left (hσ j)
  · push Not at hσ
    obtain ⟨j, hj⟩ := hσ
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Plant
end
