import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Prod
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array

section
/-!
# Lifting short sorts by four parallel passes

In a grid with `c` columns of height `2*r*c`, where `c ≤ r`, four
passes of independent column sorts suffice. Between passes the wiring is
fixed. Grouping the first and last half-columns together in the final
pass avoids sentinels.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Columns

variable {α : Type*} [LinearOrder α] {c n : ℕ}

/-- Column number first, position within the column second. -/
abbrev Grid (c n : ℕ) := Fin c × Fin n

def pass (x : Grid c n → α) (z : Grid c n) : α :=
  x (z.1, Tuple.sort (fun i => x (z.1, i)) z.2)

private theorem sorted (x : Grid c n → α) (a : Fin c) :
    Monotone (fun i => pass x (a, i)) :=
  Tuple.monotone_sort (fun i => x (a, i))

theorem pass_perm (x : Grid c n → α) :
    ∃ e : Equiv.Perm (Grid c n), pass x = x ∘ e :=
  ⟨Equiv.prodCongrRight (fun a => Tuple.sort (fun i => x (a, i))), rfl⟩

private theorem reaches (f : Fin n → ℕ) (hf : Function.Injective f) (i : Fin n) :
    ∃ j ≤ i, i.val ≤ f j := by
  by_contra! h
  let g (j : Fin (i.val + 1)) : Fin i.val :=
    ⟨f ⟨j, by omega⟩, h _ (by change j.val ≤ i.val; omega)⟩
  have hg : Function.Injective g := by
    intro j k e
    apply Fin.ext
    exact congrArg (fun u : Fin n => u.val) (hf (Fin.val_eq_of_eq e))
  have := Fintype.card_le_of_injective _ hg
  simp only [Fintype.card_fin] at this
  omega

/-- A large entry after sorting has a witness to its left before sorting.
Dually, a small entry has a witness to its right. -/
private theorem witnesses (x : Grid c n → α) (a : Fin c) (i : Fin n) :
    (∃ j ≤ i, pass x (a, i) ≤ x (a, j)) ∧ (∃ j ≥ i, x (a, j) ≤ pass x (a, i)) := by
  let σ := Tuple.sort (fun k => x (a, k))
  constructor
  · obtain ⟨j, hj, hj'⟩ := reaches _ (Fin.val_injective.comp σ.symm.injective) i
    refine ⟨j, hj, (sorted x a (show i ≤ σ.symm j from hj')).trans_eq ?_⟩
    exact congrArg (fun k => x (a, k)) (σ.apply_symm_apply j)
  · obtain ⟨j, hj, hj'⟩ := reaches _ (Fin.val_injective.comp σ.injective) i
    exact ⟨σ j, hj', sorted x a hj⟩

private def back (d : ℕ) (i : Fin n) : Fin n := ⟨i.val - d, by omega⟩

/-- Sorting two sequences which interlace with displacement `d` preserves
that displacement. At most `d` inputs are unmatched. -/
private theorem interlace (x : Grid c n → α) (a b : Fin c) (d : ℕ)
    (h : ∀ k : Fin n, d ≤ k.val → x (a, back d k) ≤ x (b, k))
    (i j : Fin n) (hij : i.val + d ≤ j.val) : pass x (a, i) ≤ pass x (b, j) := by
  let σ := Tuple.sort (fun k => x (a, k))
  let τ := Tuple.sort (fun k => x (b, k))
  let f (k : Fin n) := if k.val < d then k.val else (σ.symm (back d k)).val + d
  have hf : Function.Injective f := by
    intro k l e
    unfold f at e
    split at e <;> split at e
    · exact Fin.ext e
    · omega
    · omega
    · have hb := σ.symm.injective (Fin.ext (Nat.add_right_cancel e))
      simp only [back, Fin.mk.injEq] at hb
      omega
  obtain ⟨k, hkj, hk⟩ := reaches _ (hf.comp τ.injective) j
  change j.val ≤ f (τ k) at hk
  have hdk : d ≤ (τ k).val := by unfold f at hk; split at hk <;> omega
  dsimp only [f] at hk
  rw [ite_eq_right (by omega : ¬ (τ k).val < d)] at hk
  calc
    pass x (a, i) ≤ pass x (a, σ.symm (back d (τ k))) := sorted x a (by omega)
    _ = x (a, back d (τ k)) := congrArg (fun l => x (a, l)) (σ.apply_symm_apply _)
    _ ≤ pass x (b, k) := h _ hdk
    _ ≤ pass x (b, j) := sorted x b hkj

private def pack (c d : ℕ) : Fin c × Fin d × Fin c ≃ Grid c (d * c) :=
  Equiv.prodCongr (.refl _) finProdFinEquiv

private def swapEnds (c d : ℕ) : Equiv.Perm (Fin c × Fin d × Fin c) where
  toFun z := (z.2.2, z.2.1, z.1)
  invFun z := (z.2.2, z.2.1, z.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Deal entries cyclically from each old column into the new ones.
Indices map from the new layout back into the old. -/
def deal (c d : ℕ) : Equiv.Perm (Grid c (d * c)) :=
  (pack c d).symm.trans ((swapEnds c d).trans (pack c d))

/-- Read the sorted columns in row-major order into aligned blocks. -/
def align (c d : ℕ) : Equiv.Perm (Grid c (d * c)) :=
  (pack c d).symm.trans <| (swapEnds c d).trans <|
    Equiv.prodCongr (.refl _) ((Equiv.prodComm _ _).trans
      (finProdFinEquiv.trans (finCongr (Nat.mul_comm c d))))

private theorem deal_at {d : ℕ} (a b : Fin c) (k : Fin d) :
    deal c d (a, finProdFinEquiv (k, b)) = (b, finProdFinEquiv (k, a)) := by
  change pack c d (swapEnds c d ((pack c d).symm (pack c d (a, k, b)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem align_at {d : ℕ} (a b : Fin c) (k : Fin d) :
    align c d (a, finProdFinEquiv (k, b)) =
      (b, Fin.cast (Nat.mul_comm c d) (finProdFinEquiv (a, k))) := by
  unfold align
  simp [pack, swapEnds]

private theorem spread {d : ℕ} (x : Grid c (d * c) → α) (a b : Fin c)
    (i j : Fin (d * c)) (hij : i.val + c ≤ j.val) :
    pass (pass x ∘ deal c d) (a, i) ≤ pass (pass x ∘ deal c d) (b, j) := by
  refine interlace _ _ _ _ ?_ _ _ hij
  intro k hk
  obtain ⟨⟨u, v⟩, rfl⟩ := finProdFinEquiv.surjective k
  have hu : 0 < u.val := by
    change c ≤ v.val + c * u.val at hk
    by_contra! h
    rw [show u.val = 0 by omega, Nat.mul_zero, Nat.add_zero] at hk
    omega
  have hm : c * u.val = c * (u.val - 1) + c := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hu]
  have he : back c (finProdFinEquiv (u, v)) = finProdFinEquiv (back 1 u, v) := by
    apply Fin.ext
    change v.val + c * u.val - c = v.val + c * (u.val - 1)
    omega
  simp only [Function.comp_apply, he, deal_at]
  apply sorted
  change a.val + c * (u.val - 1) ≤ b.val + c * u.val
  omega

variable {r : ℕ}

private def firstTwo (x : Grid c (2 * r * c) → α) :=
  pass (pass x ∘ deal c (2 * r)) ∘ align c (2 * r)

/-- Between distinct aligned blocks, an inversion must cross from the
second half of one block to the first half of its immediate successor. -/
private theorem crossing (hc : c ≤ r) (x : Grid c (2 * r * c) → α)
    {a b : Fin c} {i j : Fin (2 * r * c)} (hab : a < b)
    (h : firstTwo x (b, j) < firstTwo x (a, i)) :
    a.val + 1 = b.val ∧ r * c ≤ i.val ∧ j.val < r * c := by
  obtain ⟨⟨u, v⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨y, z⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [firstTwo, Function.comp_apply, align_at] at h
  have near : y.val + 2 * r * b.val < u.val + 2 * r * a.val + c := by
    by_contra! hh
    exact h.not_ge (spread x _ _ _ _ hh)
  have reach (k : ℕ) (hk : a.val + k ≤ b.val) :
      2 * r * a.val + 2 * r * k ≤ 2 * r * b.val := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ hk
  have hnext : a.val + 1 = b.val := by
    by_contra! hh
    have := reach 2 (by omega)
    omega
  have := reach 1 hnext.le
  have hu : r ≤ u.val := by omega
  have hy : y.val + 1 ≤ r := by omega
  change _ ∧ r * c ≤ v.val + c * u.val ∧ z.val + c * y.val < r * c
  have hlo := Nat.mul_le_mul_left c hu
  have hhi := Nat.mul_le_mul_left c hy
  rw [Nat.mul_add] at hhi
  rw [Nat.mul_comm r c]
  omega

private def staggerAt (z : Grid c (2 * r * c)) : Grid c (2 * r * c) :=
  if h : z.2.val < r * c then
    if z.1.val = 0 then z else
      (z.1, ⟨z.2.val + r * c, by have := Nat.mul_assoc 2 r c; omega⟩)
  else if k : z.1.val + 1 < c then
    (⟨z.1.val + 1, k⟩, back (r * c) z.2)
  else (⟨0, by have := z.1.isLt; omega⟩, z.2)

/-- Within each staggered block the two layouts give the same order. -/
private theorem stagger_le (u v : Grid c (2 * r * c))
    (h : (staggerAt u).1 = (staggerAt v).1) :
    (staggerAt u).2 ≤ (staggerAt v).2 ↔ toLex u ≤ toLex v := by
  have he : 2 * r * c = 2 * (r * c) := Nat.mul_assoc ..
  rw [Prod.Lex.toLex_le_toLex]
  simp only [staggerAt, back] at h ⊢
  split_ifs at * <;> simp only [Fin.ext_iff, Fin.le_def, Fin.lt_def] at h ⊢ <;> omega

/-- Map aligned positions to their slots in the final pass. Block zero
contains the two end halves in their original order. -/
noncomputable def stagger (c r : ℕ) : Equiv.Perm (Grid c (2 * r * c)) :=
  Equiv.ofBijective staggerAt <| (Fintype.bijective_iff_injective_and_card _).mpr ⟨by
    intro u v h
    have e := congrArg Prod.fst h
    exact toLex.injective (le_antisymm ((stagger_le _ _ e).1 (by rw [h]))
      ((stagger_le _ _ e.symm).1 (by rw [h]))), rfl⟩

/-- All remaining inversions after pass three lie in one staggered block
per inversion. Sorting that block then resolves the inversion. -/
private theorem afterThree (hc : c ≤ r) (x : Grid c (2 * r * c) → α)
    (u v : Grid c (2 * r * c)) (hle : toLex u ≤ toLex v)
    (hne : (staggerAt u).1 ≠ (staggerAt v).1) :
    pass (firstTwo x) u ≤ pass (firstTwo x) v := by
  obtain ⟨a, i⟩ := u
  obtain ⟨b, j⟩ := v
  rcases Prod.Lex.toLex_le_toLex.mp hle with hab | ⟨he, hij⟩
  · by_contra! inv
    obtain ⟨k, hk, hk'⟩ := (witnesses (firstTwo x) a i).1
    obtain ⟨l, hl, hl'⟩ := (witnesses (firstTwo x) b j).2
    obtain ⟨he, hhi, hlo⟩ := crossing hc x hab ((hl'.trans_lt inv).trans_le hk')
    change a.val + 1 = b.val at he
    apply hne
    simp only [staggerAt, dite_eq_left (by omega : j.val < r * c),
      dite_eq_right (by omega : ¬ i.val < r * c), dite_eq_left (by omega : a.val + 1 < c),
      ite_eq_right (by omega : ¬ b.val = 0)]
    exact Fin.ext he
  · change a = b at he
    subst b
    exact sorted _ _ hij

private theorem cleanup (y : Grid c n → α) (g : Equiv.Perm (Grid c n))
    (hg : ∀ u v, (g u).1 = (g v).1 → ((g u).2 ≤ (g v).2 ↔ toLex u ≤ toLex v))
    (hy : ∀ u v, toLex u ≤ toLex v → (g u).1 ≠ (g v).1 → y u ≤ y v)
    (u v : Grid c n) (h : toLex u ≤ toLex v) :
    pass (y ∘ g.symm) (g u) ≤ pass (y ∘ g.symm) (g v) := by
  by_cases he : (g u).1 = (g v).1
  · have := sorted (y ∘ g.symm) (g u).1 ((hg u v he).2 h)
    change pass _ (g u) ≤ pass _ ((g u).1, (g v).2) at this
    rwa [he] at this
  · obtain ⟨i, hi, hi'⟩ := (witnesses (y ∘ g.symm) (g u).1 (g u).2).1
    obtain ⟨j, hj, hj'⟩ := (witnesses (y ∘ g.symm) (g v).1 (g v).2).2
    let a := g.symm ((g u).1, i)
    let b := g.symm ((g v).1, j)
    have ha : g a = ((g u).1, i) := g.apply_symm_apply _
    have hb : g b = ((g v).1, j) := g.apply_symm_apply _
    have ha' := (hg a u (by rw [ha])).1 (by rwa [ha])
    have hb' := (hg v b (by rw [hb])).1 (by rwa [hb])
    exact hi'.trans ((hy a b (ha'.trans (h.trans hb')) (by rwa [ha, hb])).trans hj')

/-- Each pass invokes one short sorter per column. -/
noncomputable def fourPass (x : Grid c (2 * r * c) → α) : Grid c (2 * r * c) → α :=
  pass (pass (pass (pass x ∘ deal c (2 * r)) ∘ align c (2 * r)) ∘ (stagger c r).symm) ∘
    stagger c r

theorem fourPass_sorted (hc : c ≤ r) (x : Grid c (2 * r * c) → α)
    (u v : Grid c (2 * r * c)) (h : toLex u ≤ toLex v) : fourPass x u ≤ fourPass x v :=
  cleanup _ (stagger c r) stagger_le (afterThree hc x) u v h

theorem fourPass_perm (x : Grid c (2 * r * c) → α) :
    ∃ e : Equiv.Perm (Grid c (2 * r * c)), fourPass x = x ∘ e := by
  obtain ⟨e₁, h₁⟩ := pass_perm x
  obtain ⟨e₂, h₂⟩ := pass_perm (pass x ∘ deal c (2 * r))
  obtain ⟨e₃, h₃⟩ := pass_perm (firstTwo x)
  obtain ⟨e₄, h₄⟩ := pass_perm (pass (firstTwo x) ∘ (stagger c r).symm)
  refine ⟨(stagger c r).trans (e₄.trans ((stagger c r).symm.trans
    (e₃.trans ((align c (2 * r)).trans (e₂.trans ((deal c (2 * r)).trans e₁)))))), ?_⟩
  change pass (pass (firstTwo x) ∘ (stagger c r).symm) ∘ stagger c r = _
  rw [h₄, h₃, firstTwo, h₂, h₁]
  rfl

private theorem unpack_monotone {i j : Fin (c * n)} (h : i ≤ j) :
    toLex (finProdFinEquiv.symm i) ≤ toLex (finProdFinEquiv.symm j) := by
  obtain ⟨⟨a, u⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨b, v⟩, rfl⟩ := finProdFinEquiv.surjective j
  change u.val + n * a.val ≤ v.val + n * b.val at h
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Prod.Lex.toLex_le_toLex]
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact .inl hab
  · exact .inr ⟨rfl, by change u ≤ v; omega⟩
  · have := Nat.mul_le_mul_left n (show b.val + 1 ≤ a.val by omega)
    rw [Nat.mul_add] at this
    omega

private theorem tuple_eq (x : Fin (c * n) → α) (y : Grid c n → α)
    (hs : ∀ u v, toLex u ≤ toLex v → y u ≤ y v)
    (he : ∃ e : Equiv.Perm (Grid c n), y = (x ∘ finProdFinEquiv) ∘ e) :
    y = (x ∘ Tuple.sort x) ∘ finProdFinEquiv := by
  let p := @finProdFinEquiv c n
  have hm : Monotone (y ∘ p.symm) :=
    fun i j h => hs _ _ (unpack_monotone h)
  obtain ⟨e, he⟩ := he
  rw [he] at hm ⊢
  change Monotone (x ∘ (p.symm.trans (e.trans p))) at hm
  have h := Tuple.unique_monotone hm (Tuple.monotone_sort x)
  funext z
  simpa only [Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
    using congrFun h (p z)

/-- A full tuple sort factors through four calls to the parallel short
sorter. The three permutations are fixed before the input is given. -/
theorem factor (hc : c ≤ r) (hn : n = 2 * r * c) :
    ∃ D A S : Equiv.Perm (Grid c n), ∀ x : Fin (c * n) → α,
      pass (pass (pass (pass (x ∘ finProdFinEquiv) ∘ D) ∘ A) ∘ S.symm) ∘ S =
        (x ∘ Tuple.sort x) ∘ finProdFinEquiv := by
  subst n
  refine ⟨deal c (2 * r), align c (2 * r), stagger c r, fun x => ?_⟩
  let p := @finProdFinEquiv c (2 * r * c)
  change fourPass (x ∘ p) = (x ∘ Tuple.sort x) ∘ p
  exact tuple_eq x _ (fourPass_sorted hc _) (fourPass_perm _)

end OAI.LinearAlgebra.MatrixExponent.Columns
end

section
/-! # Wiring four layers of parallel short sorting networks -/

namespace OAI.LinearAlgebra.MatrixExponent.Columns

/-- Column lifting uses only composition and reordering. The same proof
works for trivalent gates and high-arity sorting gates. -/
structure Model where
  Runs : (a b : Wire) → (Val a → Val b) → ℕ → Prop
  pre {a b c f g m} : Runs b c g m → Rewire a b f → Runs a c (fun x => g (f x)) m
  post {a b c f g m} : Runs a b f m → Rewire b c g → Runs a c (fun x => g (f x)) m
  comp {a b c f g m n} : Runs a b f m → Runs b c g n → Runs a c (fun x => g (f x)) (m + n)
  mono {a b f m n} : Runs a b f m → m ≤ n → Runs a b f n

def trivalent (F : Type) [Field F] : Model :=
  ⟨DNet F, DNet.pre, DNet.post, DNet.comp, DNet.mono⟩

namespace Model

variable (M : Model) {a b u : Wire} [LinearOrder (Val a)] {c n m t : ℕ}

private theorem assemble (B : Layout a b (Grid c n)) (U : Layout a u (Fin (c * n)))
    {f : Val b → Val b} {g : Val u → Val u} (h : M.Runs (copies b t) (copies b t) (mapCopies f t) m)
    (hf : ∀ x, B.read (f x) = pass (B.read x))
    (hg : ∀ x, U.read (g x) = U.read x ∘ Tuple.sort (U.read x))
    {r : ℕ} (hc : c ≤ r) (hn : n = 2 * r * c) :
    M.Runs (copies u t) (copies u t) (mapCopies g t) (4 * m) := by
  obtain ⟨D, A, S, he⟩ := factor (α := Val a) hc hn
  obtain ⟨pre, hpre, epre⟩ := U.rewire B finProdFinEquiv
  obtain ⟨d, hd, ed⟩ := B.rewire B D
  obtain ⟨j, hj, ej⟩ := B.rewire B A
  obtain ⟨s, hs, es⟩ := B.rewire B S.symm
  obtain ⟨post, hpost, epost⟩ := B.rewire U (finProdFinEquiv.symm.trans S)
  have eqn : (fun x => post (f (s (f (j (f (d (f (pre x))))))))) = g := by
    funext x
    apply U.injective
    rw [epost, hf, es, hf, ej, hf, ed, hf, epre, hg]
    funext i
    simpa only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
      using congrFun (he (U.read x)) (finProdFinEquiv.symm i)
  have lifted (k : ℕ) (x : Val (copies u k)) :
      mapCopies post k (mapCopies f k (mapCopies s k (mapCopies f k
        (mapCopies j k (mapCopies f k (mapCopies d k (mapCopies f k (mapCopies pre k x)))))))) =
        mapCopies g k x := by
    induction k with
    | zero => rfl
    | succ k ih => exact Prod.ext (congrFun eqn x.1) (ih x.2)
  rw [← funext (lifted t), show 4 * m = ((m + m) + m) + m by omega]
  have h₁ := M.pre h (hpre.mapCopies t)
  have h₂ := M.comp h₁ (M.pre h (hd.mapCopies t))
  have h₃ := M.comp h₂ (M.pre h (hj.mapCopies t))
  have hr := M.post (M.comp h₃ (M.pre h (hs.mapCopies t))) (hpost.mapCopies t)
  exact hr

private theorem read_parallel {w : ℕ} (L : Layout (tree w a) (copies (tree w a) c) (Fin c))
    (T : Layout a (tree w a) (Fin n))
    (hL : ∀ (f : Val (tree w a) → Val (tree w a)) x, L.read (mapCopies f c x) = f ∘ L.read x)
    (hT : ∀ x, List.ofFn (T.read x) = flatten w x) (x : Val (copies (tree w a) c)) :
    (L.nest T).read (mapCopies (sortTree w) c x) = pass ((L.nest T).read x) := by
  funext ⟨i, j⟩
  simp only [pass, Layout.read_nest, hL, Function.comp_apply, T.read_sort hT]

private theorem map_append (f : Val b → Val b) (d n : ℕ)
    (x : Val (copies b d)) (y : Val (copies b n)) :
    mapCopies f (n + d) (appendCopies b d n (x, y)) =
      appendCopies b d n (mapCopies f d x, mapCopies f n y) := by
  induction d with
  | zero => rfl
  | succ d ih => exact Prod.ext rfl (ih x.2)

private theorem map_join (f : Val b → Val b) (d t : ℕ) (x : Val (copies (copies b d) t)) :
    mapCopies f (d * t) (joinCopies b d t x) =
      joinCopies b d t (mapCopies (mapCopies f d) t x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change mapCopies f (d * t + d) (appendCopies b d (d * t) _) = _
    rw [map_append, ih]
    rfl

private theorem regroup {f : Val b → Val b} {d : ℕ}
    (h : M.Runs (copies b (d * t)) (copies b (d * t)) (mapCopies f (d * t)) m) :
    M.Runs (copies (copies b d) t) (copies (copies b d) t)
      (mapCopies (mapCopies f d) t) m := by
  have j := Rewire.joinCopies b d t
  obtain ⟨s, hs, he⟩ := j.inverse
  have eqn : (fun x => s (mapCopies f (d * t) (joinCopies b d t x))) =
      mapCopies (mapCopies f d) t := by
    funext x
    exact ((he _ _).mp (map_join f d t x).symm).symm
  rw [← eqn]
  exact M.post (M.pre h j) hs

/-- Combine groups of `2^v` short sorts, preserving independence between
the `t` resulting long sorts. No factorization of the input network is needed. -/
theorem sort_lift_batch {v w : ℕ} (hw : 2 * v + 1 ≤ w)
    (h : M.Runs (copies (tree w a) (2 ^ v * t)) (copies (tree w a) (2 ^ v * t))
      (mapCopies (sortTree w) (2 ^ v * t)) m) :
    M.Runs (copies (tree (w + v) a) t) (copies (tree (w + v) a) t)
      (mapCopies (sortTree (w + v)) t) (4 * m) := by
  let r := 2 ^ (w - v - 1)
  have hc : 2 ^ v ≤ r := Nat.pow_le_pow_right (by decide) (by omega)
  have hn : 2 ^ w = 2 * r * 2 ^ v := by
    unfold r
    rw [← pow_succ', ← pow_add, show w - v - 1 + 1 + v = w by omega]
  have hU := Layout.exists_tree a (w + v)
  rw [pow_add, Nat.mul_comm (2 ^ w)] at hU
  obtain ⟨U, hU⟩ := hU
  obtain ⟨T, hT⟩ := Layout.exists_tree a w
  obtain ⟨L, hL⟩ := Layout.exists_copies (tree w a) (2 ^ v)
  exact M.assemble (L.nest T) U (M.regroup h) (read_parallel L T hL hT) (U.read_sort hU) hc hn

private theorem single {f : Val b → Val b}
    (h : M.Runs (copies b 1) (copies b 1) (mapCopies f 1) m) : M.Runs b b f m :=
  by
    have he := M.post (M.pre h (.unit' _)) (.unit _)
    exact he

theorem sort_lift {v w : ℕ} (hw : 2 * v + 1 ≤ w)
    (h : M.Runs (copies (tree w a) (2 ^ v)) (copies (tree w a) (2 ^ v))
      (mapCopies (sortTree w) (2 ^ v)) m) :
    M.Runs (tree (w + v) a) (tree (w + v) a) (sortTree (w + v)) (4 * m) := by
  apply M.single
  apply M.sort_lift_batch hw
  rwa [mul_one]

/-- Each full lift multiplies the address length minus two by at least 3/2.
The cost of `k` lifts is at most `4^k` times the initial batch size. -/
theorem sort_lift_iterate {v w : ℕ} (hw : 2 ≤ w) (k : ℕ)
    (hv : 2 ^ k * (w + v - 2) ≤ 3 ^ k * (w - 2))
    (h : M.Runs (copies (tree w a) (2 ^ v)) (copies (tree w a) (2 ^ v))
      (mapCopies (sortTree w) (2 ^ v)) m) :
    M.Runs (tree (w + v) a) (tree (w + v) a) (sortTree (w + v)) (4 ^ k * m) := by
  induction k generalizing v w m with
  | zero =>
    have : v = 0 := by simp only [pow_zero, one_mul] at hv; omega
    subst v
    simpa using M.single h
  | succ k ih =>
    by_cases small : 2 * v + 1 ≤ w
    · apply M.mono (M.sort_lift small h)
      exact Nat.mul_le_mul_right m (by rw [pow_succ]; have := Nat.one_le_pow k 4 (by decide); omega)
    let d := (w - 1) / 2
    have hi : 2 * d + 1 ≤ w := by omega
    have he : d + (v - d) = v := by omega
    have ha : w + d + (v - d) = w + v := by omega
    have hb : 3 * (w - 2) ≤ 2 * (w + d - 2) := by omega
    have hbound : 2 ^ k * (w + d + (v - d) - 2) ≤ 3 ^ k * (w + d - 2) := by
      rw [ha, ← Nat.mul_le_mul_left_iff (by decide : 0 < 2)]
      calc
        _ = 2 ^ (k + 1) * (w + v - 2) := by rw [pow_succ', mul_assoc]
        _ ≤ 3 ^ (k + 1) * (w - 2) := hv
        _ ≤ 3 ^ k * (2 * (w + d - 2)) := by rw [pow_succ, mul_assoc]; exact Nat.mul_le_mul_left _ hb
        _ = _ := by rw [mul_left_comm]
    have h₁ := sort_lift_batch (t := 2 ^ (v - d)) (M := M) (a := a) (m := m) hi (by
      rwa [← pow_add, he])
    have h₂ := ih (by omega : 2 ≤ w + d) hbound h₁
    rwa [ha, ← mul_assoc, ← pow_succ] at h₂

end Model

variable {F : Type} [Field F] {a : Wire} [LinearOrder (Val a)] {m t : ℕ}

theorem sort_lift_batch {v w : ℕ} (hw : 2 * v + 1 ≤ w)
    (h : DNet F (copies (tree w a) (2 ^ v * t)) (copies (tree w a) (2 ^ v * t))
      (mapCopies (sortTree w) (2 ^ v * t)) m) :
    DNet F (copies (tree (w + v) a) t) (copies (tree (w + v) a) t)
      (mapCopies (sortTree (w + v)) t) (4 * m) :=
  (trivalent F).sort_lift_batch hw h

theorem sort_lift {v w : ℕ} (hw : 2 * v + 1 ≤ w)
    (h : DNet F (copies (tree w a) (2 ^ v)) (copies (tree w a) (2 ^ v))
      (mapCopies (sortTree w) (2 ^ v)) m) :
    DNet F (tree (w + v) a) (tree (w + v) a) (sortTree (w + v)) (4 * m) :=
  (trivalent F).sort_lift hw h

theorem sort_lift_iterate {v w : ℕ} (hw : 2 ≤ w) (k : ℕ)
    (hv : 2 ^ k * (w + v - 2) ≤ 3 ^ k * (w - 2))
    (h : DNet F (copies (tree w a) (2 ^ v)) (copies (tree w a) (2 ^ v))
      (mapCopies (sortTree w) (2 ^ v)) m) :
    DNet F (tree (w + v) a) (tree (w + v) a) (sortTree (w + v)) (4 ^ k * m) :=
  (trivalent F).sort_lift_iterate hw k hv h

theorem sort_lift_three {v w : ℕ} (hw : 40 ≤ w) (hv : v ≤ 3 * w / 2)
    (h : DNet F (copies (tree w a) (2 ^ v)) (copies (tree w a) (2 ^ v))
      (mapCopies (sortTree w) (2 ^ v)) m) :
    DNet F (tree (w + v) a) (tree (w + v) a) (sortTree (w + v)) (64 * m) :=
  sort_lift_iterate (by omega) 3 (by omega) h

end OAI.LinearAlgebra.MatrixExponent.Columns
end
