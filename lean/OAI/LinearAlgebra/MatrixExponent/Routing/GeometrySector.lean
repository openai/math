import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Module
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryTerms
import Mathlib.Algebra.Order.Monoid.Prod
import OAI.LinearAlgebra.MatrixExponent.Sphere.Block
import OAI.LinearAlgebra.MatrixExponent.Spectral.Placements
import OAI.LinearAlgebra.MatrixExponent.Spectral.Span

section
/-!
# The metric consequence of shifted crossing

The two original wires connect opposite terminals. On either cut we
may move terminals to a pair of centers and connect those centers.
At least one cut must pay the full cost of the original wires.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

def CutBound {S : Type*} (d : S → S → ℝ) : Prop :=
  ∀ (x x' y y' z z' w w' : S) (t u α β : ℝ),
    0 < t → 0 < u → 0 < α → 0 < β → 2 * (t ^ 2 + u ^ 2) < α ^ 2 + β ^ 2 →
    t * (d x x' - d x z - d x' z') + u * (d y y' - d y z - d y' z') ≤ α * d z z' ∨
    t * (d x x' - d x w - d x' w') + u * (d y y' - d y w' - d y' w) ≤ β * d w w'

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# The parallelogram law from shifted crossing

There is no regularity assumption on the seminorm. The directional
savings on two cuts are estimated using a finite difference at an
approximate minimizer of `p (r • (z+w) + z) - r * p (z+w)`.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (p : Seminorm ℝ V)

private theorem scale {r : ℝ} (hr : 0 ≤ r) (x : V) : p (r • x) = r * p x := by
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hr]

/-- The sum of the two directional savings approaches the norm of
the sum of the directions. -/
private theorem gain (z w : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : V, p (z + w) - ε ≤ 2 * p x - p (x - z) - p (x - w) := by
  let f (r : ℝ) := p (r • (z + w) + z) - r * p (z + w)
  let S := f '' Set.Ici 0
  have hne : S.Nonempty := ⟨_, 0, by simp, rfl⟩
  have hbd : BddBelow S := by
    refine ⟨-p z, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    have h := map_add_le_add p (r • (z + w) + z) (-z)
    rw [add_neg_cancel_right, map_neg_eq_map, scale p hr] at h
    unfold f
    linarith
  obtain ⟨_, ⟨r, hr, rfl⟩, he⟩ := exists_lt_of_csInf_lt hne
    (show sInf S < sInf S + ε / 2 by linarith)
  let s := 2 * r + 1
  have hs : 0 ≤ s := by change 0 ≤ r at hr; dsimp [s]; linarith
  have h := csInf_le hbd (show f s ∈ S from ⟨s, hs, rfl⟩)
  let x := s • (z + w) + z
  refine ⟨x, ?_⟩
  have eq : x - w = (2 : ℝ) • (r • (z + w) + z) := by unfold x s; module
  rw [eq, scale p (by norm_num), show x - z = s • (z + w) by unfold x; abel, scale p hs]
  unfold f at h he
  unfold x s at *
  linarith

private theorem tradeoff {t u X Y a b : ℝ}
    (ha : a ≤ (t + u) * X) (hb : b ≤ (t + u) * Y)
    (hc : ∀ α β : ℝ, 0 < α → 0 < β → 2 * (t ^ 2 + u ^ 2) < α ^ 2 + β ^ 2 →
      a ≤ α * X ∨ b ≤ β * Y) :
    a + b ≤ (t ^ 2 + u ^ 2) / 2 + X ^ 2 + Y ^ 2 := by
  let s := (t ^ 2 + u ^ 2) / 2
  have hA : a - X ^ 2 ≤ s := by
    unfold s
    linarith only [ha, sq_nonneg (t - X), sq_nonneg (u - X)]
  have hB : b - Y ^ 2 ≤ s := by
    unfold s
    linarith only [hb, sq_nonneg (t - Y), sq_nonneg (u - Y)]
  change a + b ≤ s + X ^ 2 + Y ^ 2
  by_contra! bad
  let δ := (a + b - s - X ^ 2 - Y ^ 2) / 3
  have hd : 0 < δ := by unfold δ; linarith
  let A := a - X ^ 2 - δ
  let B := b - Y ^ 2 - δ
  have h₁ : 0 < A := by unfold A δ; linarith
  have h₂ : 0 < B := by unfold B δ; linarith
  have h₃ : s < A + B := by unfold A B δ; linarith
  have h₄ := Real.sq_sqrt h₁.le
  have h₅ := Real.sq_sqrt h₂.le
  obtain h | h := hc (2 * Real.sqrt A) (2 * Real.sqrt B) (by positivity) (by positivity)
    (by unfold s at h₃; linarith only [h₃, h₄, h₅])
  · have he : A + X ^ 2 < a := by unfold A; linarith
    linarith only [h, he, h₄, sq_nonneg (Real.sqrt A - X)]
  · have he : B + Y ^ 2 < b := by unfold B; linarith
    linarith only [h, he, h₅, sq_nonneg (Real.sqrt B - Y)]

private theorem gain_bound (hc : CutBound (fun x y => p (x - y))) (x y z w : V)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    t * (2 * p x - p (x - z) - p (x - w)) + u * (2 * p y - p (y - z) - p (y + w)) ≤
      (t ^ 2 + u ^ 2) / 2 + p z ^ 2 + p w ^ 2 := by
  let f := fun a b : V => p a - p (a - b)
  have hf (a b : V) : f a b ≤ p b := by
    have h := map_add_le_add p (a - b) b
    rw [sub_add_cancel] at h
    unfold f
    linarith
  have hsum (z w : V) (hw : p w = p z) : t * f x z + u * f y w ≤ (t + u) * p z := by
    rw [add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hf _ _) ht.le)
      (mul_le_mul_of_nonneg_left ((hf _ _).trans_eq hw) hu.le)
  have h := tradeoff (hsum z z rfl) (hsum w (-w) (map_neg_eq_map _ _)) (by
    intro α β hα hβ h
    have h' := hc x (-x) y (-y) z (-z) w (-w) t u α β ht hu hα hβ h
    have hd (a : V) : p (a - -a) = 2 * p a := by
      rw [sub_neg_eq_add, ← two_smul ℝ, scale p (by norm_num)]
    have hm (a b : V) : p (-a - -b) = p (a - b) := by
      rw [show -a - -b = -(a - b) by abel, map_neg_eq_map]
    have hm' : p (-y - w) = p (y - -w) := by simpa using hm y (-w)
    simp only [hd, hm, hm'] at h'
    rcases h' with h' | h'
    · left; unfold f; linarith only [h']
    · right; unfold f; linarith only [h'])
  simp only [f, sub_neg_eq_add] at h
  linarith only [h]

private theorem parallelogram_le (hc : CutBound (fun x y => p (x - y))) (z w : V) :
    p (z + w) ^ 2 + p (z - w) ^ 2 ≤ 2 * (p z ^ 2 + p w ^ 2) := by
  let t := p (z + w)
  let u := p (z - w)
  have h (x y : V) : p (x + y) ^ 2 ≤ 2 * (p x ^ 2 + p y ^ 2) := by
    have he := pow_le_pow_left₀ (apply_nonneg p _) (map_add_le_add p x y) 2
    linarith only [he, sq_nonneg (p x - p y)]
  rcases (apply_nonneg p (z + w)).eq_or_lt with ht | ht
  · simpa [← ht, sub_eq_add_neg] using h z (-w)
  rcases (apply_nonneg p (z - w)).eq_or_lt with hu | hu
  · simpa [← hu] using h z w
  apply le_of_forall_pos_le_add
  intro ε hε
  have hd : 0 < ε / (2 * (t + u)) := div_pos hε (by unfold t u; positivity)
  obtain ⟨x, hx⟩ := gain p z w hd
  obtain ⟨y, hy⟩ := gain p z (-w) hd
  rw [← sub_eq_add_neg, sub_neg_eq_add] at hy
  have he := div_mul_cancel₀ ε (show 2 * (t + u) ≠ 0 by unfold t u; positivity)
  dsimp only [t, u] at hx hy he
  linarith only [he, mul_le_mul_of_nonneg_left hx ht.le, mul_le_mul_of_nonneg_left hy hu.le,
    gain_bound p hc x y z w ht hu]

theorem parallelogram_of_cuts (hc : CutBound (fun x y => p (x - y))) (z w : V) :
    p (z + w) ^ 2 + p (z - w) ^ 2 = 2 * (p z ^ 2 + p w ^ 2) := by
  refine le_antisymm (parallelogram_le p hc z w) ?_
  have h := parallelogram_le p hc (z + w) (z - w)
  rw [show z + w + (z - w) = (2 : ℝ) • z by module, show z + w - (z - w) = (2 : ℝ) • w by module,
    scale p (by norm_num), scale p (by norm_num)] at h
  linarith

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Geodesic sectors

Two rays from a common origin whose equal-time distances grow linearly
span an affine quadrant. Only Busemann convexity is used here.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {Y : Type*} [PseudoMetricSpace Y]

def Divides (t : Fraction) (x y z : Y) : Prop :=
  dist x z = t.val * dist x y ∧ dist z y = (1 - t.val) * dist x y

def Busemann (Y : Type*) [PseudoMetricSpace Y] : Prop :=
  ∀ (t : Fraction) (x y m a b n : Y), Divides t x y m → Divides t a b n →
    dist m n ≤ (1 - t.val) * dist x a + t.val * dist y b

def Segments (Y : Type*) [PseudoMetricSpace Y] : Prop :=
  ∀ (t : Fraction) (x y : Y), ∃ m, Divides t x y m

theorem Divides.of_le {t : Fraction} {x y z : Y} (hx : dist x z ≤ t.val * dist x y)
    (hy : dist z y ≤ (1 - t.val) * dist x y) : Divides t x y z := by
  have h := dist_triangle x z y
  constructor <;> linarith

theorem Divides.same (t : Fraction) (x : Y) : Divides t x x x := by simp [Divides]

theorem Busemann.unique (h : Busemann Y) {t : Fraction} {x y z w : Y}
    (hz : Divides t x y z) (hw : Divides t x y w) : dist z w = 0 := by
  refine le_antisymm ?_ dist_nonneg
  simpa using h t _ _ _ _ _ _ hz hw

theorem Divides.replace {t : Fraction} {x y z w : Y} (h : Divides t x y z)
    (he : dist z w = 0) : Divides t x y w := by
  apply Divides.of_le
  · linarith [h.1, dist_triangle x z w]
  · rw [dist_comm] at he
    linarith [h.2, dist_triangle w z y]

def mix {V : Type*} [AddCommGroup V] [Module ℝ V] (t : Fraction) (x y : V) : V :=
  (1 - t.val) • x + t.val • y

abbrev Coord := ℝ × ℝ

def AffineSector (F : Coord → Y) : Prop :=
  ∀ (t : Fraction) (x y : Coord), 0 ≤ x → 0 ≤ y → Divides t (F x) (F y) (F (mix t x y))

def Ray (f : ℝ → Y) (A : ℝ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → dist (f s) (f t) = |s - t| * A

theorem Ray.divides {f : ℝ → Y} {A s t : ℝ} (hf : Ray f A)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (u : Fraction) : Divides u (f s) (f t) (f (mix u s t)) := by
  have hm : 0 ≤ mix u s t := add_nonneg (mul_nonneg (sub_nonneg.mpr u.2.2) hs)
    (mul_nonneg u.2.1 ht)
  rw [Divides, hf _ _ hs hm, hf _ _ hm ht, hf _ _ hs ht]
  have eq : s - mix u s t = u.val * (s - t) := by unfold mix; simp only [smul_eq_mul]; ring
  have eq' : mix u s t - t = (1 - u.val) * (s - t) := by unfold mix; simp only [smul_eq_mul]; ring
  rw [eq, eq', abs_mul, abs_mul, abs_of_nonneg u.2.1, abs_of_nonneg (sub_nonneg.mpr u.2.2)]
  exact ⟨mul_assoc _ _ _, mul_assoc _ _ _⟩

private def weight (v : Coord) : ℝ := v.1 + v.2

private theorem mix_pos (t : Fraction) {x y : Coord} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ mix t x y :=
  add_nonneg (smul_nonneg (sub_nonneg.mpr t.2.2) hx) (smul_nonneg t.2.1 hy)

/-- Boundary values are preserved up to zero distance, since the
ambient metric need not separate points. -/
theorem exists_sector (h : Busemann Y) (hs : Segments Y)
    {a b : ℝ → Y} {A B c : ℝ} (ha : Ray a A) (hb : Ray b B)
    (he : ∀ r, 0 ≤ r → dist (a r) (b r) = r * c) :
    ∃ F : Coord → Y, AffineSector F ∧
      ∀ r, 0 ≤ r → dist (F (r, 0)) (a r) = 0 ∧ dist (F (0, r)) (b r) = 0 := by
  have hw (v : Coord) (hv : 0 ≤ v) : 0 ≤ weight v := add_nonneg hv.1 hv.2
  have hn (v : Coord) (hv : 0 ≤ v) : ∃ t : Fraction, t.val * weight v = v.2 := by
    rcases (hw v hv).eq_or_lt with hz | hp
    · have hv₁ : 0 ≤ v.1 := hv.1
      have hv₂ : 0 ≤ v.2 := hv.2
      exact ⟨⟨0, by norm_num, by norm_num⟩, by unfold weight at hz; dsimp; linarith⟩
    refine ⟨⟨v.2 / weight v, div_nonneg hv.2 hp.le, (div_le_one hp).mpr ?_⟩,
      div_mul_cancel₀ _ hp.ne'⟩
    exact le_add_of_nonneg_left hv.1
  let s := fun v : Coord => if hv : 0 ≤ v then (hn v hv).choose else ⟨0, by norm_num, by norm_num⟩
  let F := fun v => (hs (s v) (a (weight v)) (b (weight v))).choose
  have hF (v : Coord) : Divides (s v) (a (weight v)) (b (weight v)) (F v) :=
    (hs _ _ _).choose_spec
  have he' (v : Coord) (hv : 0 ≤ v) :
      dist (a (weight v)) (F v) = v.2 * c ∧ dist (F v) (b (weight v)) = v.1 * c := by
    have heq : (s v).val * weight v = v.2 := by
      simp only [s, dite_eq_left hv]
      exact (hn v hv).choose_spec
    have hh := hF v
    unfold Divides at hh
    rw [he _ (hw _ hv)] at hh
    constructor
    · rw [hh.1, ← mul_assoc, heq]
    · rw [hh.2, ← mul_assoc, sub_mul, one_mul, heq, weight, add_sub_cancel_right]
  refine ⟨F, ?_, ?_⟩
  · intro t x y hx hy
    let v := mix t x y
    have hv := mix_pos t hx hy
    have eq : weight v = mix t (weight x) (weight y) := by
      change (1 - t.val) * x.1 + t.val * y.1 + ((1 - t.val) * x.2 + t.val * y.2) =
        (1 - t.val) * (x.1 + x.2) + t.val * (y.1 + y.2)
      ring
    obtain ⟨m, hm⟩ := hs t (F x) (F y)
    have h₁ := h t _ _ _ _ _ _ (ha.divides (hw _ hx) (hw _ hy) t) hm
    have h₂ := h t _ _ _ _ _ _ hm (hb.divides (hw _ hx) (hw _ hy) t)
    rw [← eq, (he' x hx).1, (he' y hy).1] at h₁
    rw [← eq, (he' x hx).2, (he' y hy).2] at h₂
    apply hm.replace
    apply h.unique _ (hF v)
    apply Divides.of_le
    · rw [← (hF v).1, (he' _ hv).1]
      change _ ≤ ((1 - t.val) * x.2 + t.val * y.2) * c
      linarith
    · rw [← (hF v).2, (he' _ hv).2]
      change _ ≤ ((1 - t.val) * x.1 + t.val * y.1) * c
      linarith
  · intro r hr
    constructor
    · simpa [weight, dist_comm] using (he' (r, 0) ⟨hr, le_rfl⟩).1
    · simpa [weight] using (he' (0, r) ⟨le_rfl, hr⟩).2

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Four-terminal wire prices from shifted crossings

Each summand of the crossing moves to the two centers of its cut.
There its separated factorization costs a single wire. All placements
allow coincidences, including at the two centers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral

private abbrev Role := Bool ⊕ Bool
private abbrev leg (a b : ℕ) : Role → Type := Sum.elim (fun _ => Fin a) (fun _ => Fin b)
private instance (a b : ℕ) : ∀ s, Fintype (leg a b s) :=
  Sum.rec (fun _ => inferInstanceAs (Fintype (Fin a))) (fun _ => inferInstanceAs (Fintype (Fin b)))

variable {K : Type} [Field K] {a b r : ℕ}

private abbrev Row (a b : ℕ) := ∀ s, leg a b s

private def ind (i i' : Fin a) (j j' : Fin b) : K :=
  if i = i' ∧ j = j' then 1 else 0

private def matchRow (a b : ℕ) (x : Row a b) : K :=
  ind (a := a) (b := b) (x (.inl true)) (x (.inl false)) (x (.inr true)) (x (.inr false))

private abbrev pairWire (K : Type) [Field K] (a b : ℕ) : Raw K Role where
  leg := leg a b
  term := Fin a × Fin b
  factor i s := match s with
    | .inl _ => fun (x : Fin a) => if x = i.1 then 1 else 0
    | .inr _ => fun (x : Fin b) => if x = i.2 then 1 else 0

private theorem pairWire_coeff (x : Row a b) : (pairWire K a b).coeff x = matchRow a b x := by
  unfold Raw.coeff
  erw [Fintype.sum_prod_type]
  simp only [Fintype.prod_sum_type, Fintype.prod_bool]
  have key (i i' : Fin a) (j j' : Fin b) :
      (∑ p : Fin a, ∑ q : Fin b,
        ((if i = p then (1 : K) else 0) * (if i' = p then 1 else 0)) *
          ((if j = q then 1 else 0) * (if j' = q then 1 else 0))) = ind i i' j j' := by
    rw [← Finset.sum_mul_sum]
    by_cases h : i = i' <;> simp [mul_ite, ind, h]
  exact key _ _ _ _

private theorem crossing_pair :
    Tensor.wire K (.inl true : Role) (.inl false) a *
      Tensor.wire K (.inr true) (.inr false) b ≤
        Tensor.ofRaw (Raw.ofTable (leg a b) (matchRow a b)) := by
  have e : pairWire K a b ≈ Raw.ofTable (leg a b) (matchRow a b) :=
    Raw.equiv_coeff (fun _ => Equiv.refl _) fun x =>
      (pairWire_coeff x).trans (Raw.coeff_ofTable _ _ x).symm
  rw [← Tensor.ofRaw_eq e]
  refine Raw.Restricts.rows (Equiv.refl _) ?_
  intro s x
  change Fin a × Fin b at x
  cases s with
  | inl s =>
    by_cases h : x.2.val = 0
    · refine .inl ⟨x.1, fun i => ?_⟩
      change Fin a × Fin b at i
      change (if x.1 = Raw.port {Sum.inl true, Sum.inl false} (.inl s : Role) i.1 then (1 : K) else 0) *
        (if x.2 = Raw.port {Sum.inr true, Sum.inr false} (.inl s : Role) i.2 then 1 else 0) =
        if x.1 = i.1 then 1 else 0
      cases s <;> simp [Raw.port, Fin.ext_iff, h]
    · refine .inr (fun i => ?_)
      change Fin a × Fin b at i
      change _ * (if x.2 = Raw.port {Sum.inr true, Sum.inr false} (.inl s : Role) i.2 then (1 : K) else 0) = 0
      simp [Raw.port, Fin.ext_iff, h]
  | inr s =>
    by_cases h : x.1.val = 0
    · refine .inl ⟨x.2, fun i => ?_⟩
      change Fin a × Fin b at i
      change (if x.1 = Raw.port {Sum.inl true, Sum.inl false} (.inr s : Role) i.1 then (1 : K) else 0) *
        (if x.2 = Raw.port {Sum.inr true, Sum.inr false} (.inr s : Role) i.2 then 1 else 0) =
        if x.2 = i.2 then 1 else 0
      cases s <;> simp [Raw.port, Fin.ext_iff, h]
    · refine .inr (fun i => ?_)
      change Fin a × Fin b at i
      change (if x.1 = Raw.port {Sum.inl true, Sum.inl false} (.inr s : Role) i.1 then (1 : K) else 0) * _ = 0
      simp [Raw.port, Fin.ext_iff, h]

private def cut (σ : Bool) (A B : Fin a → Fin b → Fin r → K) (x : Row a b) : K :=
  ∑ j, A (x (.inl true)) (x (.inr σ)) j * B (x (.inl false)) (x (.inr (!σ))) j

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

private theorem cut_price (f : Tensor K S →+* ℝ) (hf : Monotone f) (s : Role → S)
    (σ : Bool) (A B : Fin a → Fin b → Fin r → K) (z z' : S) :
    f (Tensor.place s (Tensor.ofRaw (Raw.ofTable (leg a b) (cut σ A B)))) ≤
      f (Tensor.wire K z z' r) *
        (f (Tensor.wire K (s (.inl true)) z a) * f (Tensor.wire K (s (.inl false)) z' a) *
          (f (Tensor.wire K (s (.inr σ)) z b) * f (Tensor.wire K (s (.inr (!σ))) z' b))) := by
  let X := Raw.ofTable (leg a b) (cut σ A B)
  let G (s : Role) := s = .inl true ∨ s = .inr σ
  let c (s : Role) := if G s then z else z'
  have h : Tensor.place c (Tensor.ofRaw X) ≤ Tensor.wire K z z' r := by
    let L j (x : Row a b) := A (x (.inl true)) (x (.inr σ)) j
    let R j (x : Row a b) := B (x (.inl false)) (x (.inr (!σ))) j
    have hL j x y (h : ∀ i, G i → x i = y i) : L j x = L j y := by
      unfold L
      rw [h _ (Or.inl rfl), h _ (Or.inr rfl)]
    have hR j x y (h : ∀ i, ¬ G i → x i = y i) : R j x = R j y := by
      unfold R
      rw [h (.inl false) (by simp [G]), h (.inr (!σ)) (by cases σ <;> simp [G])]
    simpa only [Fintype.card_fin] using
      Tensor.separated_le (leg a b) (cut σ A B) G L R (fun _ => rfl) hL hR z z'
  let W := ∏ i, Tensor.wire K (c i) (s i) (Fintype.card (X.leg i))
  have hm := hf (Tensor.transport X c s)
  change f (Tensor.place s (Tensor.ofRaw X)) ≤ f (Tensor.place c (Tensor.ofRaw X) * W) at hm
  rw [map_mul] at hm
  have hW : 0 ≤ f W := by simpa using hf (Tensor.zero_le W)
  refine (hm.trans (mul_le_mul_of_nonneg_right (hf h) hW)).trans_eq ?_
  congr 1
  unfold W
  rw [map_prod, Fintype.prod_sum_type, Fintype.prod_bool, Fintype.prod_bool]
  have hl (i : Bool) : Fintype.card (X.leg (.inl i)) = a := Fintype.card_fin _
  have hr (i : Bool) : Fintype.card (X.leg (.inr i)) = b := Fintype.card_fin _
  simp only [hl, hr]
  cases σ <;> simp [c, G, Tensor.wire_comm, mul_comm]

private def pairValue (f : Tensor K S →+* ℝ) (x x' y y' z z' : S) (a b r : ℕ) :=
  f (Tensor.wire K z z' r) *
    (f (Tensor.wire K x z a) * f (Tensor.wire K x' z' a) *
      (f (Tensor.wire K y z b) * f (Tensor.wire K y' z' b)))

private theorem crossing_price (f : Tensor K S →+* ℝ) (hf : Monotone f)
    (x x' y y' z z' w w' : S) {p q : ℕ} (h : Sphere.Crossing K a b p q) :
    f (Tensor.wire K x x' a) * f (Tensor.wire K y y' b) ≤
      pairValue f x x' y y' z z' a b p + pairValue f x x' y' y w w' a b q := by
  obtain ⟨A, B, C, D, hab⟩ := h
  let s : Role → S := Sum.elim (fun i => if i then x else x') (fun j => if j then y else y')
  let V := fun i : Bool => if i then cut true A B else cut false C D
  have he (u : Row a b) : matchRow a b u = ∑ i : Bool, (1 : K) * V i u := by
    rw [Fintype.sum_bool, one_mul, one_mul]
    exact hab _ _ _ _
  have hv := Tensor.span_le (leg a b) (matchRow a b) V (fun _ => 1) he
  rw [Fintype.sum_bool] at hv
  have H := hf ((Tensor.place_mono s (crossing_pair.trans hv)).trans (Tensor.place_add_le s _ _))
  rw [Tensor.place_mul, Tensor.place_wire, Tensor.place_wire, f.map_mul, f.map_add] at H
  exact H.trans (add_le_add (cut_price f hf s true A B z z') (cut_price f hf s false C D w w'))

private theorem crossing_trim {p q a' b' : ℕ} (h : Sphere.Crossing K a b p q)
    (ha : a' ≤ a) (hb : b' ≤ b) : Sphere.Crossing K a' b' p q := by
  obtain ⟨A, B, C, D, H⟩ := h
  let L {r : ℕ} (M : Fin a → Fin b → Fin r → K) (i : Fin a') (j : Fin b') :=
    M (Fin.castLE ha i) (Fin.castLE hb j)
  refine ⟨L A, L B, L C, L D, fun i i' j j' => ?_⟩
  simpa [L] using H (Fin.castLE ha i) (Fin.castLE ha i') (Fin.castLE hb j) (Fin.castLE hb j')

private theorem log_bound {v : ℝ} (hv : 0 ≤ v) :
    let a := ⌈Real.exp v⌉₊
    v ≤ Real.log (a : ℝ) ∧ Real.log (a : ℝ) ≤ v + 1 := by
  have hp := Real.exp_pos v
  have ha := Nat.le_ceil (Real.exp v)
  constructor
  · simpa using Real.log_le_log hp ha
  · apply (Real.log_le_iff_le_exp (hp.trans_le ha)).mpr
    rw [Real.exp_add]
    have h := Nat.ceil_lt_add_one hp.le
    have h₁ := Real.add_one_le_exp v
    have h₂ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp 1) hp.le
    linarith

omit [Nonempty S] in
private theorem finite_cut (f : Tensor K S →+* ℝ) (hf : Monotone f)
    (x x' y y' z z' : S) {t u α n : ℝ} (ht : 0 ≤ t * n) (hu : 0 ≤ u * n)
    (ha : a = ⌈Real.exp (t * n)⌉₊) (hb : b = ⌈Real.exp (u * n)⌉₊)
    (hr : 0 < r) (hr' : (r : ℝ) ≤ Real.exp (α * n))
    (h : f (Tensor.wire K x x' a) * f (Tensor.wire K y y' b) ≤
      2 * pairValue f x x' y y' z z' a b r) :
    let d := Tensor.dist f
    n * (t * (d x x' - d x z - d x' z') + u * (d y y' - d y z - d y' z') - α * d z z') ≤ 5 := by
  have ha' : 0 < a := by rw [ha]; positivity
  have hb' : 0 < b := by rw [hb]; positivity
  have pos (v w : S) (m : ℕ) (hm : 0 < m) : 0 < f (Tensor.wire K v w m) := by
    rw [Tensor.price_wire f hf v w hm]
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm) _
  have H := Real.log_le_log (mul_pos (pos _ _ _ ha') (pos _ _ _ hb')) h
  unfold pairValue at H
  have h₀ := pos z z' _ hr
  have h₁ := pos x z _ ha'
  have h₂ := pos x' z' _ ha'
  have h₃ := pos y z _ hb'
  have h₄ := pos y' z' _ hb'
  have h₅ := pos x x' _ ha'
  have h₆ := pos y y' _ hb'
  simp (disch := positivity) only [Real.log_mul] at H
  have L (v w : S) (m : ℕ) (hm : 0 < m) :
      Real.log (f (Tensor.wire K v w m)) = Tensor.dist f v w * Real.log m := by
    rw [Tensor.price_wire f hf v w hm, Real.log_rpow (Nat.cast_pos.mpr hm)]
  have cost (v w : S) {m : ℕ} {l : ℝ} (hl : 0 ≤ l) (hm : m = ⌈Real.exp l⌉₊) :
      Tensor.dist f v w * l ≤ Real.log (f (Tensor.wire K v w m)) ∧
      Real.log (f (Tensor.wire K v w m)) ≤ Tensor.dist f v w * l + 1 := by
    rw [L _ _ _ (by rw [hm]; positivity), hm]
    obtain ⟨hl, hu⟩ := log_bound hl
    have hpos := Tensor.dist_nonneg f hf v w
    refine ⟨mul_le_mul_of_nonneg_left hl hpos, ?_⟩
    linarith only [mul_le_mul_of_nonneg_left hu hpos, Tensor.dist_le_one f hf v w]
  have h₇ : Real.log (f (Tensor.wire K z z' r)) ≤ Tensor.dist f z z' * (α * n) := by
    rw [L _ _ _ hr]
    exact mul_le_mul_of_nonneg_left ((Real.log_le_iff_le_exp (Nat.cast_pos.mpr hr)).mpr hr')
      (Tensor.dist_nonneg f hf _ _)
  dsimp only
  linarith only [H, h₇, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2),
    (cost x x' ht ha).1, (cost y y' hu hb).1, (cost x z ht ha).2,
    (cost x' z' ht ha).2, (cost y z hu hb).2, (cost y' z' hu hb).2]

/-- Remove the constant loss by using arbitrarily large shifted crossings. -/
theorem shifted_metric (H : Sphere.ShiftedCrossing K) (f : Tensor K S →+* ℝ)
    (hf : Monotone f) : CutBound (Tensor.dist f) := by
  intro x x' y y' z z' w w' t u α β ht hu hα hβ hquad
  by_contra! h
  let d := Tensor.dist f
  let v := t * (d x x' - d x z - d x' z') + u * (d y y' - d y z - d y' z') - α * d z z'
  let v' := t * (d x x' - d x w - d x' w') + u * (d y y' - d y w' - d y' w) - β * d w w'
  have hv : 0 < v := sub_pos.mpr h.1
  have hv' : 0 < v' := sub_pos.mpr h.2
  obtain ⟨n, a, b, p, q, hn, hp, hq, ha, hb, hp', hq', hx⟩ :=
    H t u α β ht hu hα hβ hquad (max (6 / v) (6 / v'))
  have h₁ := (div_le_iff₀ hv).mp ((le_max_left _ _).trans hn)
  have h₂ := (div_le_iff₀ hv').mp ((le_max_right _ _).trans hn)
  have hn' : 0 ≤ n := (div_pos (by norm_num : (0 : ℝ) < 6) hv).le.trans ((le_max_left _ _).trans hn)
  have ht' := mul_nonneg ht.le hn'
  have hu' := mul_nonneg hu.le hn'
  have h₃ := crossing_price f hf x x' y y' z z' w w'
    (crossing_trim hx (Nat.ceil_le.mpr ha) (Nat.ceil_le.mpr hb))
  have split (a b c : ℝ) (h : a ≤ b + c) : a ≤ 2 * b ∨ a ≤ 2 * c := by
    by_contra! he
    linarith
  rcases split _ _ _ h₃ with hl | hr
  · have hu := finite_cut f hf x x' y y' z z' ht' hu' rfl rfl hp hp' hl
    change n * v ≤ 5 at hu
    linarith
  · rw [Tensor.wire_comm K y y'] at hr
    have hu := finite_cut f hf x x' y' y w w' ht' hu' rfl rfl hq hq' hr
    dsimp only at hu
    rw [Tensor.dist_comm f y' y] at hu
    unfold v' d at h₂
    linarith only [hu, h₂]

end OAI.LinearAlgebra.MatrixExponent.Routing
end
