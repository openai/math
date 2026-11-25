import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.Zoom
import OAI.LinearAlgebra.MatrixExponent.FieldExtension
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.TreePrice
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Face.Contact
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.Rigidity
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Arms
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Geometry.Ray

section
/-!
# Parameters for private products

First fix the power count to amortize the two index strings per private
output. Then take the rank slack small compared with the sparse saving.
Rounding up to a binary length and the fixed multiplicative constant
each consume at most one further rank slack.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion
open Real Filter

private theorem natpower (x : ℝ) (hx : 0 < x) (k : ℕ) :
    x ^ k = exp (log x * k) := by rw [← rpow_natCast, rpow_def_of_pos hx]

theorem private_at_rate {F : Type} [Field F] (h : SparseApprox F)
    {x ε : ℝ} (he : 0 < ε)
    (hrank : ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, ∃ s j r : ℕ, n ≤ s ∧
      (s : ℝ) ^ (x + ε) ≤ j ∧ (r : ℝ) ≤ (s : ℝ) ^ (2 + δ) ∧ Rectangle.RankLE F s s j r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℕ, ∃ s j r p : ℕ, m ≤ s ∧ 0 < r ∧ 0 < p ∧
      (s : ℝ) ^ (x + δ) * p ≤ j ∧ (r : ℝ) ≤ (s : ℝ) ^ (2 - δ) ∧ j ≤ s ^ 3 ∧
        Decodes F s j r p := by
  obtain ⟨n, hn⟩ := exists_nat_gt (12 / ε)
  obtain ⟨c, C, hc, hc', hC, happrox⟩ := h n
  let k := (n : ℝ) + 1
  have hk : 1 ≤ k := by unfold k; simp
  have hek : 12 ≤ k * ε := by unfold k; rw [div_lt_iff₀ he] at hn; linarith
  let δ := min (ε / 2) (c / (4 * k))
  have hd : 0 < δ := lt_min (half_pos he) (by positivity)
  have hd' : δ ≤ ε / 2 := min_le_left _ _
  have hdc : δ * (4 * k) ≤ c := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hd₁ : δ ≤ 1 / 4 := by nlinarith
  have hcost : δ + (k - c) * (2 + 2 * δ) ≤ k * (2 - δ) := by nlinarith
  have hshort : k * (x + δ) + 2 * (2 + 2 * δ) ≤ k * (x + ε) := by nlinarith
  have hlog₂ : 0 < log 2 := by positivity
  obtain ⟨S, hS⟩ := eventually_atTop.mp ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    |>.eventually_ge_atTop ((max (log C) (log 2)) / δ))
  refine ⟨δ, hd, fun m => ?_⟩
  obtain ⟨s, j, r, hs, hj, hr, hdec⟩ := hrank δ hd (max 2 (max S m))
  have hs' : 1 ≤ (s : ℝ) := by exact_mod_cast (show 1 ≤ s by omega)
  have hs₀ : 0 < (s : ℝ) := zero_lt_one.trans_le hs'
  let L := log s
  have hL : 0 ≤ L := log_nonneg hs'
  have hbig : max (log C) (log 2) ≤ L * δ := (div_le_iff₀ hd).mp (hS s (by omega))
  let b := ⌈L * (2 + δ) / log 2⌉₊
  have hb₁ : L * (2 + δ) ≤ b * log 2 := (div_le_iff₀ hlog₂).mp (Nat.le_ceil _)
  have hb₂ : (b : ℝ) * log 2 ≤ L * (2 + 2 * δ) := by
    have ht := Nat.ceil_lt_add_one (show 0 ≤ L * (2 + δ) / log 2 by positivity)
    have ht' := mul_lt_mul_of_pos_right ht hlog₂
    rw [add_mul, div_mul_cancel₀ _ hlog₂.ne', one_mul] at ht'
    exact ht'.le.trans (by linarith [le_max_right (log C) (log 2)])
  have hcap : (s : ℝ) ^ (2 + δ) ≤ (2 : ℝ) ^ b := by
    rw [rpow_def_of_pos hs₀, natpower _ (by norm_num), exp_le_exp, mul_comm (log 2)]
    exact hb₁
  have hsq : (s : ℝ) * s ≤ (s : ℝ) ^ (2 + δ) := by
    rw [← pow_two, ← rpow_two]
    exact rpow_le_rpow_of_exponent_le hs' (by linarith)
  obtain ⟨t, ht, hbound, hdecode⟩ := happrox s j r b (by exact_mod_cast hr.trans hcap)
    (by exact_mod_cast hsq.trans hcap) hdec
  refine ⟨s ^ (n + 1), j ^ (n + 1), t, 2 ^ (2 * b), (show m ≤ s by omega).trans (Nat.le_self_pow (by omega) _),
    ht, by positivity, ?_, ?_, ?_, hdecode⟩
  · push_cast
    apply le_trans _ (pow_le_pow_left₀ (by positivity) hj (n + 1))
    rw [← rpow_natCast_mul hs₀.le, ← rpow_mul_natCast hs₀.le, rpow_def_of_pos hs₀,
      rpow_def_of_pos hs₀, natpower _ (by norm_num), ← exp_add, exp_le_exp]
    push_cast
    unfold L at hb₂ hL
    unfold k at hshort
    linarith only [hb₂, mul_le_mul_of_nonneg_left hshort hL]
  · have hC' : C ≤ exp (L * δ) := le_exp_of_log_le ((le_max_left _ _).trans hbig)
    refine hbound.trans ((mul_le_mul_of_nonneg_right hC' (by positivity)).trans ?_)
    rw [Nat.cast_pow, ← rpow_natCast_mul hs₀.le, rpow_def_of_pos hs₀,
      rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← exp_add, exp_le_exp]
    push_cast
    have h₁ := mul_le_mul_of_nonneg_left hcost hL
    have h₂ := mul_le_mul_of_nonneg_left hb₂ (by linarith : 0 ≤ k - c)
    unfold k L at h₁ h₂
    unfold L
    linarith only [h₁, h₂]
  · have hpos : 0 < s := by omega
    have harea := hdec.cycle.area hpos
    have hj' : j ≤ r := le_trans (by simpa using Nat.mul_le_mul_right j hpos) harea
    have hpow : (r : ℝ) ≤ (s : ℝ) ^ (3 : ℕ) := by
      rw [← rpow_natCast]
      exact hr.trans (rpow_le_rpow_of_exponent_le hs' (by norm_num; linarith))
    rw [← pow_mul, mul_comm (n + 1), pow_mul]
    exact Nat.pow_le_pow_left (hj'.trans (by exact_mod_cast hpow)) _

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# Short output sums from a strict dual threshold

A sparse row is evaluated by a short list of products specific to that
output. Each rank-one summand in the error matrix contributes just one
common bilinear form. The two within-pair wires pay for the short lists,
so the four-site obstruction does not need one private product per output.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion

open Finset
open scoped Classical

variable {F X Y I : Type} [Field F] [Fintype I] {s j p : ℕ}

private theorem pad_sum (L : I → X → F) (R : I → Y → F) (h : Fintype.card I ≤ p) :
    ∃ (U : Fin p → X → F) (V : Fin p → Y → F), ∀ x y,
      ∑ i, L i x * R i y = ∑ t, U t x * V t y := by
  let e : Fin p ≃ I ⊕ Fin (p - Fintype.card I) := Fintype.equivOfCardEq (by simp; omega)
  let u := Sum.elim L (fun _ : Fin (p - Fintype.card I) => 0)
  let v := Sum.elim R (fun _ : Fin (p - Fintype.card I) => 0)
  refine ⟨u ∘ e, v ∘ e, fun x y => ?_⟩
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun i => u i x * v i y), Fintype.sum_sum_type]
  simp [u, v]

private theorem decode {R : ℝ} (M D : Matrix I I F) (hl : Low (M - D) R)
    (hs : ∀ x, #{y | D x y ≠ 0} ≤ p)
    (row : Out s → I) (u v : I → Leg s j → F)
    (he : ∀ e x y, entry F e x y = ∑ t, M (row e) t * (u t x * v t y)) :
    ∃ t : ℕ, 0 < t ∧ (t : ℝ) ≤ R + 1 ∧ Decodes F s j t p := by
  let T (e : Out s) : Finset I := {t | D (row e) t ≠ 0}
  have hshort (e : Out s) :
      ∃ a b : Fin p → Leg s j → F, ∀ x y, ∑ t, D (row e) t * (u t x * v t y) =
        ∑ l, a l x * b l y := by
    obtain ⟨a, b, h⟩ := pad_sum (fun (t : T e) x => D (row e) t * u t x) (fun (t : T e) => v t)
      (show Fintype.card ↥(T e) ≤ p by rw [Fintype.card_coe]; exact hs _)
    refine ⟨a, b, fun x y => ?_⟩
    rw [← h x y]
    simp_rw [mul_assoc]
    rw [sum_coe_sort (T e) (fun t => D (row e) t * (u t x * v t y))]
    symm
    apply sum_subset (subset_univ _)
    intro k _ hk
    have hz : D (row e) k = 0 := by simpa [T] using hk
    simp [hz]
  choose a b hab using hshort
  obtain ⟨J, _, hJ, L, U, hLU⟩ := hl
  let E (t : J) (x : Leg s j × Leg s j) := ∑ l, U t l * (u l x.1 * v l x.2)
  obtain ⟨c, d, hcd⟩ := pad_sum (fun t e => L (row e) t) E (Nat.le_succ _)
  refine ⟨Fintype.card J + 1, by omega, by simpa using add_le_add_left hJ 1, a, b,
    fun e t => c t e, fun t x y => d t (x, y), fun e x y => ?_⟩
  have eqn (t : I) : M (row e) t = D (row e) t + ∑ k, L (row e) k * U k t := by
    have h := congrArg (fun P : Matrix I I F => P (row e) t) hLU
    exact sub_eq_iff_eq_add'.mp h
  rw [he, short, ← hab, ← hcd e (x, y)]
  simp only [eqn, add_mul, sum_add_distrib, sum_mul, E, mul_sum, mul_assoc]
  rw [sum_comm]

theorem sparseApprox (F : Type) [Field F] : SparseApprox F := by
  intro n
  obtain ⟨c, C, hc, hc', hC, h⟩ := sparse_power (F := F) n
  refine ⟨c, C + 1, hc, hc', by linarith, fun s j r m hr hs hk => ?_⟩
  obtain ⟨M, row, u, v, he⟩ := padded_power n hr hs hk
  obtain ⟨D, hl, hD⟩ := h m M
  obtain ⟨t, ht, hbound, hdec⟩ := decode _ D hl hD row u v he
  refine ⟨t, ht, hbound.trans ?_, hdec⟩
  rw [add_mul, one_mul]
  exact add_le_add_right (Real.one_le_rpow (by norm_num) (mul_nonneg (by linarith) (by positivity))) _

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

section
/-!
# Private products below the harmonic threshold

The rectangular upper bound at inner width one half suffices.
Approaching that width from below leaves room for the power and
sparsification overheads without a strict dual improvement.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion

private theorem threshold_rank (F : Type) [Field F] {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∃ s j r : ℕ, n ≤ s ∧ (s : ℝ) ^ (1 / 2 : ℝ) ≤ j ∧
      (r : ℝ) ≤ (s : ℝ) ^ (2 + δ) ∧ Rectangle.RankLE F s s j r := by
  have h := Rectangle.upper_of_diagonal (Rectangle.support F) (Rectangle.diagonal F)
    zero_lt_one zero_lt_one (by norm_num : (0 : ℝ) < 1 / 2)
  norm_num [Rectangle.U, Rectangle.benchmark] at h
  obtain ⟨m, r, hm, hr, hs⟩ :=
    (Rectangle.exponent_lt_iff_rank zero_le_one zero_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp
      (h.trans_lt (lt_add_of_pos_right 2 hδ))
  rw [Rectangle.side_one] at hr
  refine ⟨m ^ n, (Rectangle.side m (1 / 2)) ^ n, r ^ n, (Nat.lt_pow_self (by omega : 1 < m)).le,
    Nat.ceil_le.mp (Rectangle.side_pow (le_rfl : Rectangle.side m (1 / 2) ≤ _) n), ?_, hr.pow n⟩
  rw [Nat.cast_pow, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity),
    mul_comm (n : ℝ), Real.rpow_mul_natCast (by positivity)]
  exact pow_le_pow_left₀ (by positivity) hs.le _

theorem weak_private (F : Type) [Field F] (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∃ s j r p : ℕ, n ≤ s ∧ 0 < r ∧ 0 < p ∧
      (s : ℝ) ^ (1 / 2 - ε) * p ≤ j ∧ (r : ℝ) ≤ (s : ℝ) ^ (2 - δ) ∧ j ≤ s ^ 3 ∧ Decodes F s j r p := by
  obtain ⟨δ, hd, h⟩ := private_at_rate (x := 1 / 2 - ε) (sparseApprox F) hε
    (fun δ hδ n => by rw [sub_add_cancel]; exact threshold_rank F hδ n)
  refine ⟨δ, hd, fun n => ?_⟩
  obtain ⟨s, j, r, p, hs, hr, hp, he, hb, hj, hdec⟩ := h (max 1 n)
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast (le_max_left 1 n).trans hs
  refine ⟨s, j, r, p, (le_max_right _ _).trans hs, hr, hp, ?_, hb, hj, hdec⟩
  exact (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hs' (le_add_of_nonneg_right hd.le))
    (Nat.cast_nonneg _)).trans he

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# Contact on three fixed rays

Apply the one-sided short-sum bound at the two moving sites. Its two
labels have identical wire distances. The universal harmonic lower
bound on one of them therefore gives an upper bound on the other.
Crucially the latter only uses the three stationary disk centers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion
open Spectral

variable {F E X : Type} [Field F] [Field E] [PseudoMetricSpace X]

def indices (i : Fin 4) : Fin 3 → Fin 4 := ![i, 0, 1]

theorem label_eq (A : Atlas F X) (x : Fin 4 → X) (i : Fin 4) :
    A.price x (label F i 2) = A.price (x ∘ indices i) 2 := by
  rw [A.place]
  have h : Tensor.place (indices i) (2 : Tensor F (Fin 3)) = label F i 2 := by
    rw [← (show Tensor.shared F (Finset.univ : Finset (Fin 3)) 2 = 2 from Tensor.shared_all F 2),
      Tensor.place_shared, show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    simp [indices, label]
  simp only [Function.comp_apply, h]

private theorem lower (A : Atlas F X) (x : Fin 3 → X) {a h : ℝ} (hh : 0 < h) (ha : h ≤ a)
    (h₁ : dist (x 0) (x 1) = a) (h₂ : dist (x 0) (x 2) = a) (h₃ : dist (x 1) (x 2) = h) :
    a + h / 4 ≤ A.price x 2 := by
  let d := A.price x 2
  obtain ⟨D, hD⟩ := A.valid x
  let u := a - h / 2
  let v := h / 2
  have hu : 0 < u := by unfold u; linarith
  have hv : 0 < v := by unfold v; linarith
  obtain ⟨hd, hp⟩ := Rectangle.prices_of_ordinary (x := u) (y := v) (z := v) hD
    (by rw [A.wire, h₁]; unfold u v; ring) (by rw [A.wire, h₂]; unfold u v; ring)
    (by rw [A.wire, h₃]; unfold v; ring) (by positivity)
  have hb := Rectangle.diagonal F _ _ _ hp
  change 0 < d at hd
  change Rectangle.dStar (u / d) (v / d) (v / d) ≤ 1 at hb
  have he : Rectangle.dStar (u / d) (v / d) (v / d) = (u + 2 * v - u * v / (2 * u + v)) / d := by
    unfold Rectangle.dStar
    field_simp
    ring
  rw [he, div_le_one hd] at hb
  have hc : u * v / (2 * u + v) ≤ v / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [sq_nonneg v]
  have hh : a + h / 4 = u + 2 * v - v / 2 := by unfold u v; ring
  rw [hh]
  exact (sub_le_sub_left hc _).trans hb

namespace K0.Leaves

variable (M : Leaves F E X) (B : Branches E)

def tripodMarks (a b : ℚ) : Fin 3 → X :=
  fun i => M.pt (B.pos (indices 2 i)) (if i = 0 then a else b)

theorem three_rays (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l h : ℚ, l ∈ Set.Ioc 0 (1 / 2) → h ∈ Set.Ioc 0 (2 * l) →
      7 * (h : ℝ) < 2 * l * δ → B.X M.tree l ≤ 3 / 2 + ε →
      M.A.price (M.tripodMarks B (2 * l - h / 2) (h / 2)) 2 ≤ 2 * (l : ℝ) + (1 / 4 + 3 * ε) * h := by
  obtain ⟨δ, hδ, hpriv⟩ := weak_private F ε hε
  refine ⟨δ, hδ, fun l h hl hh hgap hx => ?_⟩
  obtain ⟨z, h₀, h₁, h₂, hu⟩ := B.collision_point M.tree hl hh
  let a := 2 * l - h / 2
  let b := h / 2
  have ha : 0 ≤ a := by unfold a; linarith [hl.1, hh.2]
  have hb : 0 ≤ b := by unfold b; linarith [hh.1]
  have ha' : a ≤ 1 := by unfold a; linarith [hl.2, hh.1]
  have hb' : b ≤ 1 := by unfold b; linarith [hl.2, hh.2]
  let x : Fin 4 → X := ![M.pt (B.pos 0) b, M.pt (B.pos 1) b, M.pt (B.pos 2) a, M.pt z a]
  have he : (fun i => M.pt (B.pts z i) (Branches.depth 2 l (2 * l - h) i)) = x := by
    funext i
    fin_cases i <;> simp [Branches.pts, Branches.depth, x, a, b] <;> congr 1 <;> ring
  change M.A.price _ 2 ≤ _ at hu
  rw [he] at hu
  have cross (t w : K0 E) (hw : val E (t - w) = 0) : dist (M.pt t b) (M.pt w a) = 2 * (l : ℝ) := by
    rw [M.metric t w hb' ha', gap_branch hb ha hw]
    simp [a, b]
  have h₀₂ : dist (x 0) (x 2) = 2 * (l : ℝ) := cross _ _ (B.separate 0 2 (by decide))
  have h₁₂ : dist (x 1) (x 2) = 2 * (l : ℝ) := cross _ _ (B.separate 1 2 (by decide))
  have h₀₃ : dist (x 0) (x 3) = 2 * (l : ℝ) := cross _ _ h₀
  have h₁₃ : dist (x 1) (x 3) = 2 * (l : ℝ) := cross _ _ h₁
  have h₀₁ : dist (x 0) (x 1) = (h : ℝ) := by
    change dist (M.pt _ b) (M.pt _ b) = _
    rw [M.metric _ _ hb' hb', gap_branch hb hb (B.separate 0 1 (by decide))]
    congr 1
    unfold b; ring
  have h₂₃ : dist (x 2) (x 3) = (h : ℝ) := by
    change dist (M.pt _ a) (M.pt _ a) = _
    have hc : 2 * l - h ≤ a := by unfold a; linarith [hh.1]
    rw [M.metric _ _ ha' ha', gap_branch hc hc h₂]
    congr 1
    unfold a; ring
  have hp : (0 : ℝ) < h := Rat.cast_pos.mpr hh.1
  have hle : (h : ℝ) ≤ 2 * l := by exact_mod_cast hh.2
  have lo (i : Fin 4) (h₀ : dist (x 0) (x i) = 2 * (l : ℝ))
      (h₁ : dist (x 1) (x i) = 2 * (l : ℝ)) :
      2 * (l : ℝ) + h / 4 ≤ M.A.price x (label F i 2) := by
    rw [label_eq]
    exact lower _ _ hp hle ((dist_comm _ _).trans h₀) ((dist_comm _ _).trans h₁) h₀₁
  have ha₂ := lo 2 h₀₂ h₁₂
  have ha₃ := lo 3 h₀₃ h₁₃
  obtain ⟨D, hD⟩ := M.A.valid x
  have hr := one_rate hpriv hD ((M.A.wire x _ _).trans h₀₂) ((M.A.wire x _ _).trans h₀₁)
    ((M.A.wire x _ _).trans h₂₃) (hp.le.trans hle) hp.le hgap (by linarith only [ha₂, ha₃, hp])
  rw [label_eq M.A x 2, show x ∘ indices 2 = M.tripodMarks B a b by
    funext i; fin_cases i <;> rfl] at hr
  change M.A.price (M.tripodMarks B a b) 2 ≤ _
  linarith only [hu, hr, ha₃, mul_le_mul_of_nonneg_left hx hp.le]

end K0.Leaves
end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# A common limit for all three rays

Approximate real radii by rational ones before taking the limit.
Integer radii are represented exactly, so the collision bounds survive
at each of the integer lengths used to approach the reciprocal face.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0.Leaves

open Filter
open scoped Topology

variable {F E X : Type} [Field F] [Field E] [PseudoMetricSpace X]
variable (M : Leaves F E X) (B : Branches E)

def zoom (n : ℕ) : ℚ := n + 1

theorem zoom_pos (n : ℕ) : 0 < zoom n := by unfold zoom; positivity

theorem zoom_pos' (n : ℕ) : (0 : ℝ) < zoom n := Rat.cast_pos.mpr (zoom_pos n)

private def approx (r : ℝ) (n : ℕ) : ℚ := ⌊(zoom n : ℝ) * r⌋₊ / zoom n

private theorem approx_nat (i n : ℕ) : approx (i : ℝ) n = i := by
  unfold approx
  rw [show (zoom n : ℝ) * i = ((n + 1) * i : ℕ) by simp [zoom], Nat.floor_natCast]
  push_cast
  exact mul_div_cancel_left₀ _ (zoom_pos n).ne'

private theorem approx_limit {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n => (approx r n : ℝ)) atTop (𝓝 r) := by
  have hl : Tendsto (fun n => r - 1 / (zoom n : ℝ)) atTop (𝓝 r) := by
    simpa [zoom] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub r
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
    (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
  · have h := Nat.lt_floor_add_one ((zoom n : ℝ) * r)
    simp only [approx, Rat.cast_div, Rat.cast_natCast]
    rw [le_div_iff₀ (zoom_pos' n), sub_mul, div_mul_cancel₀ _ (zoom_pos' n).ne']
    linarith
  · simp only [approx, Rat.cast_div, Rat.cast_natCast]
    rw [div_le_iff₀ (zoom_pos' n), mul_comm r]
    exact Nat.floor_le (mul_nonneg (zoom_pos' n).le hr)

private theorem approx_fits (x : Rectangle.Twig) :
    ∀ᶠ n in atTop, approx x.radius n / zoom n ∈ Set.Icc 0 1 := by
  have h : Tendsto (fun n => (zoom n : ℝ)) atTop atTop := by
    simpa [zoom] using (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  filter_upwards [h.eventually_ge_atTop (x.radius + 1),
    (approx_limit x.radius_nonneg).eventually_le_const (lt_add_one _)] with n hn hh
  have hf := zoom_pos n
  exact ⟨by unfold approx; positivity, (div_le_one hf).mpr (Rat.cast_le.mp (hh.trans hn))⟩

def toRay (n : ℕ) (x : Rectangle.Twig) :=
  M.pt (B.pos (indices 2 x.arm)) (approx x.radius n / zoom n)

private theorem ray_limit (a b : Rectangle.Twig) :
    Tendsto (fun n => (zoom n : ℝ) * dist (M.toRay B n a) (M.toRay B n b)) atTop (𝓝 (dist a b)) := by
  have ha := approx_limit a.radius_nonneg
  have hb := approx_limit b.radius_nonneg
  rw [Rectangle.Twig.dist_eq]
  by_cases h : a.arm = b.arm
  · rw [ite_eq_left h]
    refine (ha.sub hb).abs.congr' ?_
    filter_upwards [approx_fits a, approx_fits b] with n hn hm
    unfold toRay
    rw [h, M.metric _ _ hn.2 hm.2]
    have eq (z : K0 E) (t s : ℚ) (ht : t ≤ 1) (hs : s ≤ 1) : diskGap z z t s = |t - s| := by
      rcases le_total t s with h|h
      · rw [gap_same _ h ht, abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
      · rw [gap_symm, gap_same _ h hs, abs_of_nonneg (sub_nonneg.mpr h)]
    rw [eq _ _ _ hn.2 hm.2, ← sub_div, abs_div, abs_of_pos (zoom_pos n)]
    push_cast
    rw [mul_div_cancel₀ _ (zoom_pos' n).ne']
  · rw [ite_eq_right h]
    refine (ha.add hb).congr' ?_
    filter_upwards [approx_fits a, approx_fits b] with n hn hm
    have hi : Function.Injective (indices 2) := by decide
    unfold toRay
    rw [M.metric _ _ hn.2 hm.2, gap_branch hn.1 hm.1 (B.separate _ _ (hi.ne h)),
      mul_zero, sub_zero, ← add_div]
    push_cast
    rw [mul_div_cancel₀ _ (zoom_pos' n).ne']

theorem ray_integer (i n : ℕ) :
    M.toRay B n ∘ Rectangle.Twig.mark ![(i : ℝ), 1, 1] =
      M.tripodMarks B (i / zoom n) (1 / zoom n) := by
  have he : approx 1 n = 1 := by simpa using approx_nat 1 n
  funext j
  fin_cases j <;> simp [toRay, tripodMarks, Rectangle.Twig.mark, Rectangle.Twig.radius,
    approx_nat, he]

/-- The same atlas works for every integer length. -/
theorem ray_atlas : ∃ A : Atlas F Rectangle.Twig, Rectangle.Twig.Homogeneous A ∧
    ∀ (i : ℕ) (v : ℝ),
      (∀ᶠ n in atTop, (zoom n : ℝ) * M.A.price (M.tripodMarks B (i / zoom n) (1 / zoom n)) 2 ≤ v) →
      Rectangle.Twig.label A ![(i : ℝ), 1, 1] ≤ v := by
  let l := Ultrafilter.of (atTop : Filter ℕ)
  have hl : (l : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨A, hA⟩ := Atlas.scaled_limit l (fun _ => X) (fun _ => M.A) (M.toRay B)
    (fun n => zoom n) (fun n => (zoom_pos' n).le) (fun a b => (M.ray_limit B a b).mono_left hl)
  obtain ⟨Q, hQ, hQA⟩ := Rectangle.Twig.tangent A
  refine ⟨Q, hQ, fun i v h => (hQA _ _).trans (le_of_tendsto (hA _ _) ?_)⟩
  filter_upwards [h.filter_mono hl] with n hn
  rw [← M.ray_integer B] at hn
  exact hn

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0.Leaves
end

/-!
# A moving family forces contact at infinity

For each large integer `i`, shrink collision placements with fixed
ratio of radii `i : 1 : 1`. The short-output estimate bounds the
three-terminal diagonal at all these ratios on one homogeneous
tripod. This gives a zero of the defect on the reciprocal face.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0.Leaves

open Filter
open scoped Topology
variable {F E X : Type} [Field F] [Field E] [PseudoMetricSpace X]
variable (M : Leaves F E X) (B : Branches E)

private theorem estimate (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      (zoom n : ℝ) * M.A.price (M.tripodMarks B (i / zoom n) (1 / zoom n)) 2 ≤ i + 3 / 2 + 6 * ε := by
  obtain ⟨δ, hδ, ht⟩ := M.three_rays B ε hε
  obtain ⟨L, hL, hg⟩ := B.small_X M.tree hε
  filter_upwards [eventually_ge_atTop 1, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop
    (14 / δ)] with i hi hi'
  have hi'' : (14 : ℝ) < (i + 1) * δ := by
    rw [div_lt_iff₀ hδ] at hi'
    linarith only [hi', hδ]
  let scale := ((i : ℚ) + 1) / (2 * L)
  obtain ⟨k, hk⟩ := exists_nat_ge scale
  filter_upwards [eventually_ge_atTop k] with n hn
  let l := ((i : ℚ) + 1) / (2 * zoom n)
  let h := 2 / zoom n
  have hz := zoom_pos n
  have hz' := zoom_pos' n
  have he : l ≤ L := by
    have hkn : (k : ℚ) ≤ zoom n := by unfold zoom; exact_mod_cast (show k ≤ n + 1 by omega)
    have hs : (i : ℚ) + 1 ≤ zoom n * (2 * L) :=
      (div_le_iff₀ (mul_pos (by norm_num) hL.1)).mp (hk.trans hkn)
    unfold l
    rw [div_le_iff₀ (by positivity)]
    linarith only [hs]
  have hl : l ∈ Set.Ioc 0 (1 / 2) := ⟨by unfold l; positivity, he.trans hL.2⟩
  have hh : h ∈ Set.Ioc 0 (2 * l) := by
    have hq : (1 : ℚ) ≤ i := by exact_mod_cast hi
    refine ⟨by unfold h; positivity, ?_⟩
    unfold l h
    field_simp
    linarith
  have hm : B.X M.tree l ≤ 3 / 2 + ε :=
    (B.monotone_X M.tree ⟨hl.1, by linarith [hl.2]⟩ ⟨hL.1, by linarith [hL.2]⟩ he).trans hg
  have hgap : 7 * (h : ℝ) < 2 * l * δ := by
    unfold h l
    push_cast
    field_simp
    linarith only [hi'']
  have hc := ht l h hl hh hgap hm
  rw [show 2 * l - h / 2 = (i : ℚ) / zoom n by unfold h l; ring,
    show h / 2 = 1 / zoom n by unfold h; ring] at hc
  refine (mul_le_mul_of_nonneg_left hc hz'.le).trans_eq ?_
  unfold h l
  push_cast
  field_simp
  ring

private theorem zero_of_integer {D : Rectangle.Minimum.Vec → ℝ} (h : Rectangle.StarTripod F D)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, D ![(n : ℝ), 1, 1] ≤ n + 3 / 2 + ε) :
    Rectangle.Face.limit D 1 1 = 0 := by
  have ht := Rectangle.Face.tends h zero_lt_one zero_lt_one
  have hp : 0 ≤ Rectangle.Face.limit D 1 1 := by
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact h.toTripod.regular.nonneg _ (Rectangle.Face.positive hr zero_lt_one zero_lt_one)
  apply le_antisymm _ hp
  have hr : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    · filter_upwards [eventually_gt_atTop 0] with n hn
      change 0 < (n : ℝ)⁻¹
      positivity
  refine le_of_forall_pos_le_add fun ε hε => le_of_tendsto (ht.comp hr) ?_
  filter_upwards [hu ε hε] with n hn
  change Rectangle.defect D ![(n : ℝ)⁻¹, 1, 1] ≤ _
  have he : (![(n : ℝ)⁻¹, 1, 1] : Rectangle.Minimum.Vec)⁻¹ = ![(n : ℝ), 1, 1] := by
    ext i
    fin_cases i <;> simp
  rw [Rectangle.defect, he]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, inv_one, inv_inv, zero_add]
  have h₀ : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have h₁ : ((n : ℝ)⁻¹ + 1 + 1)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  linarith only [hn, h₁]

theorem tripod [Infinite E] (M : Leaves F E X) :
    ∃ A : Atlas F Rectangle.Twig, Rectangle.Twig.Homogeneous A ∧
      Rectangle.Face.limit (Rectangle.Twig.label A) 1 1 = 0 := by
  let B := Classical.arbitrary (Branches E)
  obtain ⟨A, hA, h⟩ := M.ray_atlas B
  refine ⟨A, hA, zero_of_integer hA.star (fun ε hε => ?_)⟩
  filter_upwards [M.estimate B (ε / 6) (by positivity)] with n hn
  exact (h n _ hn).trans_eq (by ring)

theorem contact [Infinite F] [Infinite E] (M : Leaves F E X) :
    omega F = 9 / 4 ∧ Rectangle.Rigidity F := by
  obtain ⟨A, h, hz⟩ := M.tripod
  exact ⟨h.star.square_of_limit h.uniform hz, h.star.rigidity_of_limit h.uniform hz⟩

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion.K0.Leaves
end
