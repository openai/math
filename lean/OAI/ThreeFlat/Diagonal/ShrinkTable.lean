import OAI.ThreeFlat.Diagonal.ShrinkFixedGrid
import OAI.ThreeFlat.Diagonal.MotifChosenEnergy

namespace OAI
/-! # A single finite shrink table for every later trace size -/

namespace ThreeFlat.Diagonal.ShrinkMotif

open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifGrid Computability.VPVNP.MotifWidths MotifIntegerChoice MotifOuterTerms
open scoped BigOperators Classical
noncomputable section

abbrev Demand := (⟨demandSrc,demandDst⟩ : PortGraph (Fin 6) (Fin 2))
abbrev SupplyPorts := (⟨supply.src,supply.dst⟩ : PortGraph (Fin 6) (Fin 8))

/-- The finite, ordered catalogue remains fixed for all old graphs. Its integer choice and
its per-histogram energy inequality refer to precisely the same row and repetition count. -/
structure Table (F : Type) [Field F] where
  Row : Type
  [rowFinite : Fintype Row]
  first : Row
  more : List Row
  base : Row → Fin 2 → ℕ
  block : ∀ z, FixedMotifTile Demand SupplyPorts (base z) F
  error : ℝ
  error_nonneg : 0≤error
  fits : ∀ b e, let z := best (score b base) first more; b e ≤ base z e * score b base z
  energy : ∀ b, let z := best (score b base) first more; let r := score b base z
    ∀ a : Histogram (block z).Alphabet r,
      widthNorm supplyMass (fun e => ((histWidth (block z).output a e + r*(block z).bits : ℕ):ℝ))^2 ≤
        (63/32 : ℝ)*widthNorm demandMass (fun e => (b e:ℝ))^2+error

attribute [instance] Table.rowFinite

theorem exists_table (F : Type) [Field F] : Nonempty (Table F) := by
  let norm := widthNorm supplyMass (fun _ => (1:ℝ))
  have hnorm : 0≤norm := Real.sqrt_nonneg _
  let δ := (1/1000 : ℝ)/(norm+1)
  have hδ : 0<δ := by dsimp only [δ]; positivity
  have small : δ*norm ≤ 1/1000 := by
    calc
      δ*norm ≤ δ*(norm+1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = _ := by dsimp only [δ]; field_simp [show norm+1≠0 by linarith]
  have start : √(31/16 : ℝ)<7/5 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  obtain ⟨G,t,h,ht,hh,tiles⟩ := exists_shrink_tiles F start hδ
  choose T fee radius using tiles
  let l := h*(t*G.denominator)
  have hl : 0 < l := Nat.mul_pos hh (Nat.mul_pos ht G.denominator_pos)
  have hp (i : Fin 2) : 0<demandMass i := by fin_cases i <;> norm_num [demandMass]
  have hq (i : Fin 8) : 0<supplyMass i := by fin_cases i <;> norm_num [supplyMass]
  have gap (z : G.demands) : ((7/5:ℝ)+(T z).bits/(l:ℝ)*norm)^2 < 63/32 := by
    have up : ((T z).bits : ℝ)/(l:ℝ)*norm ≤ 1/1000 := (mul_le_mul_of_nonneg_right (fee z).le hnorm).trans small
    have pos : 0 ≤ ((T z).bits : ℝ)/(l:ℝ)*norm := by positivity
    calc
      _ ≤ ((7/5:ℝ)+1/1000)^2 := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ < _ := by norm_num
  choose C bound using fun z : G.demands => chosen_histogram_energy hq hl (by norm_num : 0≤(7/5:ℝ)) (gap z)
  let total : ℝ := ∑ z, |C z|
  let first : G.demands := ⟨fun _ => 0,G.zero_mem_demands⟩
  let more := (Finset.univ : Finset G.demands).toList
  let base := fun z e => h*G.demandWidths t z e
  have covered (z : G.demands) : z∈first::more := by simp [more]
  refine ⟨{
    Row := G.demands
    first := first
    more := more
    base := base
    block := T
    error := total
    error_nonneg := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    fits := ?_
    energy := ?_ }⟩
  · intro b e
    exact (choose_grid G hp ht hh first more covered b).2 e
  · intro b
    let z := best (score b base) first more
    let r := score b base z
    change ∀ a : Histogram (T z).Alphabet r,
      widthNorm supplyMass (fun e => ((histWidth (T z).output a e + r*(T z).bits : ℕ) : ℝ))^2 ≤
        (63/32 : ℝ)*widthNorm demandMass (fun e => (b e : ℝ))^2 + total
    intro a
    have e := bound z _ (Real.sqrt_nonneg _) r (choose_grid G hp ht hh first more covered b).1
      (T z).Alphabet (T z).output (radius z) a
    exact e.trans (add_le_add_right ((le_abs_self _).trans (Finset.single_le_sum
      (fun i _ => abs_nonneg (C i)) (Finset.mem_univ z))) _)

end
end ThreeFlat.Diagonal.ShrinkMotif

end OAI
