import OAI.LinearAlgebra.FiniteFourier.AtTwoCost.AtTwoCost
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointCost
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridSectorCircuit

/-! # Uniform costs for the packed two-local transform

On each active sector, the short change of coordinates uses its data wires
and the long change uses fourteen times as many wires. The Taylor shift acts
only on the data wires. Summing over sectors counts the full grid once.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace AtTwoCost

open Deformation ConvolutionGrid Finset
open scoped Classical

/-- The two directions of the protected endpoint compiler cost the same
per-row upper bound, including the larger workspace of the long endpoint. -/
theorem endpointCosts_le {n e r H w s B D : ℕ} {β C : ℝ}
    (hn : 0 < n) (hs : 0 < s) (hB : 6 ≤ B) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hw : 0 < w) (hwn : w ≤ n) (hr : 0 < r) (hH : 0 < H) (hHr : H ≤ 4*r)
    (hD : D ≤ 6400*(1+Nat.clog 2 (2+B))) :
    let short := atTwoWordCost e r w s 37 β C
    let long := atTwoWordCost e H (14*w) s (243*D+37) β C
    let shift (h : ℕ) := (w:ℝ)*(8*(e:ℝ)*h*(1+Real.logb 2 h)*convolutionEnvelope s)
    let cost := (2*wordConstant C β+192)*(w*e*r)*rate n r s B β
    short + shift r + long ≤ cost ∧ long + shift H + short ≤ cost := by
  have hr4 : r ≤ 4*r := by omega
  have hB' : 1 ≤ (B:ℝ) := by exact_mod_cast (show 1 ≤ B by omega)
  have short := stage_le (e := e) (W := w) (D := 37) hn hs hB hβ hC hwn hw
    (by omega) hr4 (by omega)
  have long := stage_le (e := e) (W := 14*w) (D := 243*D+37) hn hs hB hβ hC hwn
    (by positivity) le_rfl hHr (by omega)
  have t₁ := taylor_le (e := e) (v := w) (β := β) hn hr hr4 hs hB'
  have t₂ := taylor_le (e := e) (v := w) (β := β) hn hH hHr hs hB'
  dsimp only [atTwoWordCost]
  constructor <;> linarith only [short, long, t₁, t₂]

variable {σ : Type*} [Fintype σ]

/-- Number of data rows in an active two-local sector. -/
noncomputable abbrev sectorWidth (p : σ → ℕ) (S : Finset σ) : ℕ :=
  Fintype.card (∀ i : S, Fin 2 × Fin ((p i.val-1)/2))

/-- Every sector has at least one row. Its row count is bounded by the
volume of the whole grid, including when no prime axes are active. -/
theorem atTwoSector_card_pos_le (p : σ → ℕ) (hp : ∀ i, p i % 4 = 3)
    (S : Finset σ) : 0 < sectorWidth p S ∧ sectorWidth p S ≤ ∏ i, p i := by
  classical
  constructor
  · apply Fintype.card_pos_iff.mpr
    exact ⟨fun i => (0, ⟨0, by have := hp i.val; omega⟩)⟩
  · rw [← sum_card_atTwoSectors p hp]
    exact single_le_sum (f := fun T : Finset σ => sectorWidth p T)
      (fun _ _ => Nat.zero_le _) (mem_univ S)

/-- Total work for the two input transforms and one output transform, using
each sector's own data width in the endpoint estimates. -/
theorem weighted_cost_le (p : σ → ℕ) (hp : ∀ i, p i % 4 = 3)
    {n e r s B : ℕ} {β C a d : ℝ} {b c : Finset σ → ℝ}
    (hN : 0 < ∏ i, p i) (hNn : ∏ i, p i ≤ n) (hn : 0 < n) (hs : 0 < s)
    (hB : 6 ≤ B) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (ha : a ≤ atTwoPrimeGridCost β C B (∏ i, p i) e r s)
    (hd : d ≤ atTwoPrimeGridCost β C B (∏ i, p i) e r s)
    (hb : ∀ S, b S ≤ (2*wordConstant C β+192)*((sectorWidth p S : ℝ)*e*r)*rate n r s B β)
    (hc : ∀ S, c S ≤ (2*wordConstant C β+192)*((sectorWidth p S : ℝ)*e*r)*rate n r s B β) :
    2*a+d+(∑ S, (2*b S+c S)) ≤
      3*(3*wordConstant C β+192)*(((∏ i, p i : ℕ):ℝ)*e*r)*rate n r s B β := by
  let K := wordConstant C β
  let Q := rate n r s B β
  let T := 3*(2*K+192)*e*r*Q
  have hprime := prime_word_le (e := e) hn hs hB hβ hC hN hNn (by omega : r ≤ 4*r)
  have hsum : ∑ S, (2*b S+c S) ≤ ((∏ i, p i : ℕ):ℝ)*T := calc
    _ ≤ ∑ S, (sectorWidth p S:ℝ)*T := Finset.sum_le_sum fun S _ => by
      have h₁ := hb S
      have h₂ := hc S
      dsimp [T, K, Q]
      linarith only [h₁, h₂]
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast sum_card_atTwoSectors p hp
  dsimp [T, K, Q] at hsum
  linarith only [ha.trans hprime, hd.trans hprime, hsum]

/-- Converting the packed transform budget to the packing lemma's unnormalized
work bound uses the volume estimate once, for a factor of nine. -/
theorem weighted_cost_le_widthWork {P : Finset ℕ} {n e s : ℕ} {B β C : ℝ}
    (pack : PrimeJetPacking P n e B) (hn : 0 < n) (hs : 0 < s) (hB : 1 ≤ B) (hC : 0 ≤ C) :
    3*(3*wordConstant C β+192)*(((∏ p ∈ pack.axes, p : ℕ):ℝ)*e*pack.jet)*
        rate n pack.jet s B β ≤ pack.widthWork (27*(3*wordConstant C β+192)) β s := by
  have hN : ((∏ p ∈ pack.axes, p : ℕ):ℝ)*e*pack.jet ≤ 9*n := by exact_mod_cast pack.volume_upper
  have hQ : 0 ≤ rate n pack.jet s B β := (zero_le_one.trans (convolutionEnvelope_one_le hs)).trans
    (envelope_le_rate hn hs hB)
  have hK := wordConstant_nonneg (β := β) hC
  calc
    _ ≤ 3*(3*wordConstant C β+192)*(9*n)*rate n pack.jet s B β := by gcongr
    _ = _ := by unfold rate PrimeJetPacking.widthWork; ring

end AtTwoCost

end FiniteFourier
end LinearAlgebra
end OAI
