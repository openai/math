import OAI.ThreeFlat.Diagonal.RefreshMotif
import OAI.ThreeFlat.Diagonal.CommonMotifGrid
import OAI.ThreeFlat.Diagonal.MotifChosenEnergy

namespace OAI
/-! # One numbered refresh table for each fixed temporary degree -/

namespace ThreeFlat.Diagonal.RefreshMotif

open LinearAlgebra.SpectralBooks Expander HyperbolicObstruction Computability.VPVNP.MotifGrid Computability.VPVNP.MotifWidths
open MotifIntegerChoice MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

abbrev Ties (m : ℕ) := Bool × Fin m × Fin m
def leading (h d₀ : ℕ) (γ : ℝ) : ℝ := 2*γ*d₀/h

def selected {m k : ℕ} (b : Ties m → ℕ) (base : Fin (k+1) → Ties m → ℕ) :=
  best (score b base) 0 ((List.finRange k).map Fin.succ)

/-- All tensor entries, binary codes, and constants are chosen before the
old graph and before any incoming demand. Its row indices match the native
strict-improvement fold, even if two rows have the same score. -/
structure Table (F : Type) [Field F] {m : ℕ} (c : Fin m → Fin m → ℕ) (d₀ : ℕ) (H : ℝ) where
  last : ℕ
  base : Fin (last+1) → Ties m → ℕ
  block : ∀ j, FixedMotifTile (denseGraph m) (sparseGraph c) (base j) F
  error : ℝ
  nonneg : 0 ≤ error
  fits : ∀ b e, let j := selected b base; b e ≤ base j e * score b base j
  energy : ∀ b, let j := selected b base; let r := score b base j
    ∀ z : Histogram (block j).Alphabet r,
      widthNorm (fun _ : Arc c => (m:ℝ)/d₀)
        (fun e => ((histWidth (block j).output z e+r*(block j).bits:ℕ):ℝ))^2 ≤
        H * widthNorm (fun _ : Ties m => (1:ℝ)) (fun e => (b e:ℝ))^2+error

theorem exists_table (F : Type) [Field F] {m h d₀ : ℕ} (hm : 0 < m) (hh : 0<h) (hd : 0<d₀)
    (c : Fin m → Fin m → ℕ) {γ : ℝ} (hγ : 0≤γ)
    (spectral : ∀ (Y : Type) [MetricSpace Y] [CompleteSpace Y], SpectralPlacementPrices F Y →
      CATZero Y → Bound (transition c h) Y γ) :
    Nonempty (Table F c d₀ (leading h d₀ γ+1)) := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  let H := leading h d₀ γ
  have hH : 0≤H := by dsimp [H,leading]; positivity
  let p := fun _ : Ties m => (1:ℝ)
  let q := fun _ : Arc c => (m:ℝ)/d₀
  have hp (e) : 0<p e := zero_lt_one
  have hq (e) : 0<q e := by dsimp [q]; positivity
  let R := (√H+√(H+1))/2
  have grow : √H < √(H+1) := Real.sqrt_lt_sqrt hH (by linarith)
  have low : √H<R := by dsimp [R]; linarith
  have hR : 0≤R := (Real.sqrt_nonneg _).trans low.le
  have high : R<√(H+1) := by dsimp [R]; linarith
  let norm := widthNorm q (fun _ => (1:ℝ))
  have hn : 0≤norm := Real.sqrt_nonneg _
  let η := (√(H+1)-R)/(2*(norm+1))
  have hη : 0<η := div_pos (sub_pos.mpr high) (by positivity)
  have slack : R+η*norm < √(H+1) := by
    have hh : η*norm ≤ η*(norm+1) := by gcongr; linarith
    have eq : η*(norm+1) = (√(H+1)-R)/2 := by
      dsimp [η]
      field_simp [show norm+1≠0 by linarith]
    linarith
  obtain ⟨G⟩ := exists_strict_grids p q hp hq hH low
  have comparison := energy_bound (K := F) c hh hd spectral
  obtain ⟨B,hB,tiles⟩ := PortMotifGrid.common_grid (denseGraph m) (sparseGraph c) G hp hq comparison
    (t:=1) zero_lt_one hη
  choose T fee radius using tiles
  let L := B*(1*G.denominator)
  have hL : 0<L := Nat.mul_pos hB (Nat.mul_pos (by decide) G.denominator_pos)
  have scale : (B:ℝ) ≤ (L:ℝ) := by exact_mod_cast Nat.le_mul_of_pos_right B (Nat.mul_pos (by decide) G.denominator_pos)
  have gap (z : G.demands) : (R + (T z).bits/(L:ℝ)*norm)^2 < H+1 := by
    have frac := (div_le_iff₀ (Nat.cast_pos.mpr hL)).mpr ((fee z).trans (mul_le_mul_of_nonneg_left scale hη.le))
    have ub : R + (T z).bits/(L:ℝ)*norm < √(H+1) := by
      have product:=mul_le_mul_of_nonneg_right frac hn
      linarith
    have pos : 0 ≤ R + (T z).bits/(L:ℝ)*norm := by positivity
    exact (pow_lt_pow_left₀ ub pos (by decide : (2:ℕ) ≠ 0)).trans_eq (Real.sq_sqrt (by linarith))
  choose C bound using fun z : G.demands => chosen_histogram_energy hq hL hR (gap z)
  let k := Fintype.card G.demands
  let first : G.demands := ⟨fun _ => 0,G.zero_mem_demands⟩
  let decode : Fin (k+1) → G.demands := Fin.cases first (Fintype.equivFin G.demands).symm
  let widths := fun (j : Fin (k+1)) e => B*G.demandWidths 1 (decode j) e
  have chooseBound (b : Ties m → ℕ) :
      let j := selected b widths
      score b widths j ≤ copies (widthNorm p (fun e => (b e:ℝ))) L ∧
        ∀ e, b e ≤ widths j e*score b widths j := by
    obtain ⟨z,hz⟩ := exists_padded_grid G hp 1 B zero_lt_one hB b
    let i := (Fintype.equivFin G.demands) z
    have same : decode i.succ = z := (Fintype.equivFin G.demands).symm_apply_apply z
    apply best_grid b widths 0 ((List.finRange k).map Fin.succ) i.succ
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
    · intro e
      simpa only [widths,same,Nat.mul_comm (copies _ _)] using hz e
  let total := ∑ z, |C z|
  refine ⟨{
    last := k
    base := widths
    block := fun j => T (decode j)
    error := total
    nonneg := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    fits := fun b e => (chooseBound b).2 e
    energy := ?_ }⟩
  intro b j r z
  have hlocal := bound (decode j) (widthNorm p (fun e => (b e:ℝ))) (Real.sqrt_nonneg _) r (chooseBound b).1
    (T (decode j)).Alphabet (T (decode j)).output (radius (decode j)) z
  have maxC : C (decode j) ≤ total := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (decode j)))
  exact hlocal.trans (by dsimp only [H,p,q] at *; linarith)

end
end ThreeFlat.Diagonal.RefreshMotif

end OAI
