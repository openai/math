import OAI.Computability.VPVNP.MotifGrid
import Mathlib.Data.Nat.Log

/-!
# Selector and payload widths in a fixed motif

Theorem 6.1 of *VP and VNP differ over every field* first fixes a denominator
multiple and then a power of the base identity. This order matters because the
number of direct-sum copies can depend on the chosen multiple. Every subsequent
input uses repetitions of that single base block. Its selector overhead can
be made arbitrarily small, and its padding costs a constant in squared width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifWidths

open MotifGrid

/-- The least number of bits for a base selector, indexing a direct-sum
copy and the `h` independent choices of supply grid point. -/
def selectorBits (K n h : ℕ) : ℕ := Nat.clog 2 (K * n ^ h)

theorem selector_capacity (K n h : ℕ) : K * n ^ h ≤ 2 ^ selectorBits K n h :=
  Nat.le_pow_clog (by decide) _

private theorem selectorBits_le (K n h : ℕ) :
    selectorBits K n h ≤ Nat.clog 2 K + h * Nat.clog 2 n := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  rw [pow_add, Nat.mul_comm h, pow_mul]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) _)
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _)

/-- Arbitrarily small selector fraction, with an arbitrary dependence of the
number `K t` of direct-sum copies on the denominator multiple `t`. -/
theorem exists_selector_block (den n : ℕ) (hd : 0 < den) (K : ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t h : ℕ, 0 < t ∧ 0 < h ∧
      (selectorBits (K t) n h : ℝ) / (h * (t * den) : ℝ) < δ := by
  obtain ⟨t, ht⟩ := exists_nat_gt (2 * (Nat.clog 2 n : ℝ) / δ)
  have ht0 : 0 < t := Nat.cast_pos.mp ((by positivity : 0 ≤ 2 * (Nat.clog 2 n : ℝ) / δ).trans_lt ht)
  obtain ⟨h, hh⟩ := exists_nat_gt (2 * (Nat.clog 2 (K t) : ℝ) / δ)
  have hh0 : 0 < h :=
    Nat.cast_pos.mp ((by positivity : 0 ≤ 2 * (Nat.clog 2 (K t) : ℝ) / δ).trans_lt hh)
  let B : ℝ := t * den
  have htB : (t : ℝ) ≤ B := by
    change (t : ℝ) ≤ t * den
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (by exact_mod_cast hd)
  have hB1 : 1 ≤ B := (show (1 : ℝ) ≤ t by exact_mod_cast ht0).trans htB
  have hn : 2 * (Nat.clog 2 n : ℝ) < B * δ :=
    ((div_lt_iff₀ hδ).mp ht).trans_le (mul_le_mul_of_nonneg_right htB hδ.le)
  have hK := (div_lt_iff₀ hδ).mp hh
  have hs : (selectorBits (K t) n h : ℝ) ≤ (Nat.clog 2 (K t) : ℝ) + h * (Nat.clog 2 n : ℝ) :=
    by exact_mod_cast selectorBits_le (K t) n h
  have hhB : 0 < (h : ℝ) * B := mul_pos (Nat.cast_pos.mpr hh0) (zero_lt_one.trans_le hB1)
  refine ⟨t, h, ht0, hh0, (div_lt_iff₀ hhB).mpr ?_⟩
  have hK' := hK.trans_le (le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg h) hδ.le) hB1)
  nlinarith only [hs, hK', mul_lt_mul_of_pos_left hn (Nat.cast_pos.mpr hh0)]

/-- A single strictly positive tolerance leaves room for the selector bits
inside the prescribed squared energy coefficient. -/
theorem exists_selector_tolerance (R Q H' : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hR' : R < √H') : ∃ δ > 0, ∀ x : ℝ, 0 ≤ x → x < δ → (R + x * Q) ^ 2 < H' := by
  have hq1 : 0 < Q + 1 := by linarith only [hQ]
  refine ⟨(√H' - R) / (Q + 1), div_pos (sub_pos.mpr hR') hq1, fun x hx hxt => ?_⟩
  have hlt := (lt_div_iff₀ hq1).mp hxt
  have hsq := (sq_lt_sq₀ (add_nonneg hR (mul_nonneg hx hQ)) (Real.sqrt_nonneg H')).mpr
    (show R + x * Q < √H' by linarith only [hx, hlt])
  rwa [Real.sq_sqrt (Real.sqrt_pos.mp (hR.trans_lt hR')).le] at hsq

variable {I : Type*} [Fintype I]

/-- Triangle inequality for the aggregate payload over any finite selector list. -/
theorem widthNorm_sum_le {T : Type*} [Fintype T] (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (x : T → I → ℝ) :
    widthNorm p (fun i => ∑ t, x t i) ≤ ∑ t, widthNorm p (x t) := by
  let y := fun i => ∑ t, x t i
  let d := fun i => y i / p i
  have he : √(distanceEnergy p d) = widthNorm p y := by
    unfold distanceEnergy widthNorm
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [d]
    field_simp [(hp i).ne']
  have hy : wireValue y d = widthNorm p y ^ 2 := by
    rw [norm_sq _ _ hp]
    unfold wireValue
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [d]
    ring
  have hval : wireValue y d = ∑ t, wireValue (x t) d := by
    unfold wireValue y
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hn := Finset.sum_le_sum (s := Finset.univ) (fun t _ => wireValue_le p (x t) d hp)
  rw [he, ← Finset.sum_mul, ← hval, hy, sq] at hn
  rcases (Real.sqrt_nonneg (∑ i, y i ^ 2 / p i)).eq_or_lt with h0 | hpos
  · change widthNorm p y ≤ _
    rw [show widthNorm p y = 0 from h0.symm]
    exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  · exact le_of_mul_le_mul_right hn hpos

/-- Number of repetitions of a block of width scale `L`. -/
noncomputable def copies (t : ℝ) (L : ℕ) : ℕ := ⌈t / L⌉₊

theorem copies_spec {t : ℝ} (ht : 0 ≤ t) {L : ℕ} (hL : 0 < L) :
    t ≤ (copies t L : ℝ) * L ∧ (copies t L : ℝ) * L ≤ t + L := by
  have hL' : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  constructor
  · exact (div_le_iff₀ hL').mp (Nat.le_ceil _)
  · have h := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg ht hL'.le)).le hL'.le
    rwa [add_mul, div_mul_cancel₀ _ hL'.ne', one_mul] at h

/-- The surplus demand bits can be fixed at both endpoints. -/
theorem copies_dominate (p : I → ℝ) (b base : I → ℕ) {L : ℕ} (hL : 0 < L)
    (z : I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hcover : ∀ i, (b i : ℝ) ≤ widthNorm p (fun j => b j) * z i)
    (hbase : ∀ i, (base i : ℝ) = L * z i) :
    ∀ i, b i ≤ copies (widthNorm p (fun j => b j)) L * base i := by
  intro i
  have hn : 0 ≤ widthNorm p (fun j => b j) := Real.sqrt_nonneg _
  have h := mul_le_mul_of_nonneg_right (copies_spec hn hL).1 (hz i)
  exact_mod_cast (show (b i : ℝ) ≤ (copies (widthNorm p (fun j => b j)) L : ℝ) * base i by
    rw [hbase, ← mul_assoc]; exact (hcover i).trans h)

/-- Given any admitted total payload vector, add the selector bits on every
supply edge. The linear term from rounding the number of blocks is absorbed
by the strict margin in the quadratic coefficient. -/
theorem padded_energy_le (q : I → ℝ) (hq : ∀ i, 0 < q i) {L s : ℕ} (hL : 0 < L)
    {R H' : ℝ} (hR : 0 ≤ R)
    (hgap : (R + s / (L : ℝ) * widthNorm q (fun _ => 1)) ^ 2 < H') :
    ∃ C : ℝ, ∀ (t : ℝ) (v : I → ℕ), 0 ≤ t →
      widthNorm q (fun i => v i) ≤ (copies t L : ℝ) * L * R →
      widthNorm q (fun i => (v i + copies t L * s : ℕ)) ^ 2 ≤ H' * t ^ 2 + C := by
  let A := R + s / (L : ℝ) * widthNorm q (fun _ => 1)
  have hA : 0 ≤ A := add_nonneg hR (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hg : 0 < H' - A ^ 2 := sub_pos.mpr hgap
  refine ⟨H' * A ^ 2 * L ^ 2 / (H' - A ^ 2), fun t v ht hv => ?_⟩
  let u := copies t L
  let c := fun i => ((v i + u * s : ℕ) : ℝ)
  have hnorm : widthNorm q c ≤
      widthNorm q (fun i => v i) + (u * s : ℝ) * widthNorm q (fun _ => 1) :=
    widthNorm_round_le q _ c hq (by positivity) (fun i => Nat.cast_nonneg _) (fun i => by simp [c])
  have hpad : widthNorm q c ≤ (t + L) * A := by
    calc
      _ ≤ (u : ℝ) * L * R + (u * s : ℝ) * widthNorm q (fun _ => 1) :=
        hnorm.trans (add_le_add hv le_rfl)
      _ = ((u : ℝ) * L) * A := by unfold A; field_simp [Nat.cast_ne_zero.mpr hL.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right (copies_spec ht hL).2 hA
  have hpadded : 0 ≤ (t + L) * A := mul_nonneg (add_nonneg ht (Nat.cast_nonneg L)) hA
  apply ((sq_le_sq₀ (Real.sqrt_nonneg _) hpadded).mpr hpad).trans
  rw [← sub_le_iff_le_add']
  apply (le_div_iff₀ hg).mpr
  nlinarith only [sq_nonneg ((H' - A ^ 2) * t - A ^ 2 * L)]

variable {D S : Type*} [Fintype D] [Fintype S]
variable {p : D → ℝ} {q : S → ℝ} {H R : ℝ}

/-- Choosing the upper demand grid point makes the repeated integer base
widths large enough at every edge, including when all demand widths vanish. -/
theorem exists_padded_grid (G : StrictGrids p q H R) (hp : ∀ i, 0 < p i)
    (t h : ℕ) (ht : 0 < t) (hh : 0 < h) (b : D → ℕ) :
    ∃ z : G.demands, ∀ i,
      b i ≤ copies (widthNorm p (fun j => b j)) (h * (t * G.denominator)) *
        (h * G.demandWidths t z i) := by
  let N := widthNorm p (fun j => (b j : ℝ))
  have hn : 0 ≤ N := Real.sqrt_nonneg _
  let x := fun i => N⁻¹ * (b i : ℝ)
  have hx i : 0 ≤ x i := mul_nonneg (inv_nonneg.mpr hn) (Nat.cast_nonneg _)
  have hnorm : widthNorm p x ≤ 1 := by
    rw [show x = (fun i => N⁻¹ * (b i : ℝ)) from rfl, widthNorm_scale _ _ (inv_nonneg.mpr hn)]
    change N⁻¹ * N ≤ 1
    rcases eq_or_ne N 0 with he | he <;> simp [he]
  obtain ⟨z, hz, hcover⟩ := G.cover x hx hnorm
  refine ⟨⟨z, hz⟩, copies_dominate p b _ (Nat.mul_pos hh (Nat.mul_pos ht G.denominator_pos))
    (realWidths z) (fun i => (hx i).trans (hcover i).1) ?_ ?_⟩
  · intro i
    rcases hn.eq_or_lt with hn0 | hn0
    · have h := coordinate_le p (fun j => (b j : ℝ)) hp i
      change (b i : ℝ) ≤ √(p i) * N at h
      change (b i : ℝ) ≤ N * _
      simpa [← hn0] using h
    · have h := mul_le_mul_of_nonneg_left (hcover i).1 hn
      dsimp only [x] at h
      rwa [← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul] at h
  · intro i
    simp [realWidths, mul_assoc]

/-- Adding the `h` supply grid points for a base selector costs at most `hBR`. -/
theorem base_payload_bound (G : StrictGrids p q H R) (hq : ∀ i, 0 < q i)
    (t h : ℕ) (w : Fin h → G.supplies) :
    widthNorm q (fun i => ((∑ j, G.supplyWidths t (w j) i : ℕ) : ℝ)) ≤
      (h * (t * G.denominator) : ℕ) * R := by
  push_cast
  calc
    _ ≤ ∑ j, widthNorm q (fun i => (G.supplyWidths t (w j) i : ℝ)) := widthNorm_sum_le _ hq _
    _ ≤ ∑ _j : Fin h, ((t * G.denominator : ℕ) : ℝ) * R :=
      Finset.sum_le_sum fun j _ => G.supplyWidths_norm_le t (w j)
    _ = _ := by simp [mul_assoc]

/-- The number of base copies and every coordinate of every admitted outer
payload are bounded linearly in the largest input width. -/
theorem outer_indices_linear (p : D → ℝ) (q : S → ℝ) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, 0 < q i) {L : ℕ} (hL : 0 < L) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∀ (M : ℕ) (b : D → ℕ) (v : S → ℕ), (∀ i, b i ≤ M) →
      widthNorm q (fun i => v i) ≤ (copies (widthNorm p (fun i => b i)) L : ℝ) * L * R →
      (copies (widthNorm p (fun i => b i)) L : ℝ) ≤ C * (M + 1) ∧
      ∀ i, (v i : ℝ) ≤ C * (M + 1) := by
  let P := widthNorm p (fun _ => 1)
  let Q := ∑ i, √(q i)
  let C := max (P + L) (Q * R * (P + L))
  refine ⟨C, fun M b v hb hv => ?_⟩
  let N := widthNorm p (fun i => (b i : ℝ))
  let u := copies N L
  have hN : N ≤ M * P := by
    calc
      N ≤ widthNorm p (fun _ => (M : ℝ) * 1) := norm_mono p _ _ hp
        (fun i => Nat.cast_nonneg _) (fun i => by simpa using hb i)
      _ = M * P := widthNorm_scale _ _ (Nat.cast_nonneg _)
  have hp0 : 0 ≤ P := Real.sqrt_nonneg _
  have hu : (u : ℝ) * L ≤ (P + L) * (M + 1) := by
    have h := (copies_spec (show 0 ≤ N from Real.sqrt_nonneg _) hL).2
    change (u : ℝ) * L ≤ N + L at h
    nlinarith only [h, hN, hp0, mul_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) (Nat.cast_nonneg L)]
  constructor
  · have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    exact (le_mul_of_one_le_right (Nat.cast_nonneg u) h1).trans
      (hu.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  · intro i
    have hi : √(q i) ≤ Q := Finset.single_le_sum (fun j _ => Real.sqrt_nonneg (q j))
      (Finset.mem_univ i)
    have hq0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
    calc
      (v i : ℝ) ≤ √(q i) * widthNorm q (fun j => v j) := coordinate_le q (fun j => (v j : ℝ)) hq i
      _ ≤ Q * ((u : ℝ) * L * R) := mul_le_mul hi hv (Real.sqrt_nonneg _) hq0
      _ = Q * R * ((u : ℝ) * L) := by ring
      _ ≤ Q * R * ((P + L) * (M + 1)) := mul_le_mul_of_nonneg_left hu (mul_nonneg hq0 hR)
      _ ≤ C * (M + 1) := by rw [← mul_assoc]; gcongr; exact le_max_right _ _

end MotifWidths

end VPVNP
end Computability
end OAI
