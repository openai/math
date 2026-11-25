import OAI.Computability.BorderVNP.PackedSiteGrid
import OAI.Computability.BorderVNP.PackedGridWidthBudget
import OAI.Computability.BorderVNP.PackedGridExternal
import OAI.Computability.BorderVNP.PackedSiteDecay

/-! # Feeding the grouped public bottom grid to the physical epochs

The topology and cable width of this grid are the ones used by the public
slot placement. Each interval port serves all bottom copies. The potential
bound charges the copies in their actual widths while leaving their literal
and exterior bit assignments available individually through the grouping.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PhysicalEpochs

open Crossing Shortening Cover Epoch GridPlacement DeckGrid TeamScales
open scoped Classical

variable {D q d p : ℕ} {P A : Type} (width : A → ℕ)
variable (position : (Fin q → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
variable (input : P ≃ Fin p) (order : Fin (Fintype.card (Fin q → Deck (d+2))) ≃ (Fin q → Deck (d+2)))
variable {r n : ℕ} (fit : p ≤ r*n) (s b : ℕ) (owner : A → (Fin q → Deck (d+2)))

/-- The precise grouped bottom topology of Proposition 7.2. -/
noncomputable abbrev groupedGrid := (publicGridSlots position (step q (d+2)) input order (fun _ => 1)
  (r*n) fit s (q*(1+3*d^3))).groupedRepeat width owner b

/-- The same site and channel identifiers still describe the grid after the
private computation is repeated and its live external bits are grouped. -/
def groupedShape : GridShape (groupedGrid width position input order fit s b owner) q (d+1) where
  vertex := Equiv.refl _
  channel := Equiv.refl _
  source _ := rfl
  target _ := rfl

variable {K : Type*} [Field K] (F : Factory D K) (ord : Cube D ≃ Fin q)

/-- The true routed bottom state, including the grouped free ports and its
actual local field tables, in the representation used by the outer history. -/
noncomputable def groupedBottom (table : (groupedGrid width position input order fit s b owner).Tables K) :
    F.State (fun a => b*width a) (d+1) 0 :=
  ⟨⟨_,table⟩,(groupedShape width position input order fit s b owner).routes ord F table⟩

set_option maxHeartbeats 1500000 in
/-- The real initial cost per copy is within the cubic-logarithmic routing
budget, uniformly in the topology of the private box factors. -/
theorem grouped_initial_cost_with_factor {τ C : ℝ} (hC : 1 ≤ C) (hn : 1 ≤ n) (hr : 1 ≤ r) (hb : 0 < b) (hτ : 0 ≤ τ)
    (hsite : (CoverScale.sites (Cube D) (d+1) : ℝ) ≤ r*(n : ℝ)^(9/10 : ℝ))
    (hs : (s : ℝ) ≤ C * volume τ r n) (table : (groupedGrid width position input order fit s b owner).Tables K) :
    (groupedBottom width position input order fit s b owner F ord table).route.potential F.weight / b ≤
      ((1+2*F.weight) * Fintype.card (Direction q) * (96*(4*q+1)+1)) *
        (C * volume τ r n) * (logWidth r n : ℝ)^3 := by
  let G := Fin q → Deck (d+2)
  let _ : Nonempty (Fin q) := ord.symm.nonempty
  let V := CoverScale.sites (Cube D) (d+1)
  let H := cableWidth G (endpointBudget (r*n) s (Fintype.card G)) (q*(1+3*d^3))
  let J := Fintype.card (Direction q)
  let S := groupedShape width position input order fit s b owner
  have vq : CoverScale.sites (Fin q) (d+1) = V := by
    rw [← card_eq_sites (Fin q) (d+1) (inferInstance : Fintype G)]
    exact (Fintype.card_congr (GridShape.coordinate (d := d+1) ord)).trans (card_eq_sites (Cube D) (d+1) _)
  have hp := S.potential_le ord F table (W := b*H) (fun _ => le_rfl)
  have hv : (CoverScale.sites (Fin q) (d+1) : ℝ) ≤ r*(n : ℝ)^(9/10 : ℝ) := by rw [vq]; exact hsite
  have hh := grid_width_budget_with_factor (q := q) (Fin q) hC hn hr hτ hv hs
  have hh' : (V : ℝ)*H ≤ (96*(4*q+1)+1 : ℝ)*(C * volume τ r n)*(logWidth r n : ℝ)^3 := by
    rw [← vq]
    simpa only [H,G,CoverScale.sites,cableWidth,← Nat.card_eq_fintype_card] using hh
  apply (div_le_iff₀ (by exact_mod_cast hb : 0 < (b : ℝ))).mpr
  apply hp.trans
  rw [Nat.cast_mul]
  have hw : 0 ≤ 1+2*F.weight := by linarith [F.weight_pos]
  have hz := mul_le_mul_of_nonneg_left hh' (mul_nonneg (mul_nonneg hw (Nat.cast_nonneg J)) (Nat.cast_nonneg b))
  change (1+2*F.weight) * V * J * (b*H) ≤ ((1+2*F.weight) * J * _) * _ * _ * b
  linarith only [hz]


/-- The per-copy routing cost when the private site budget fits one volume. -/
theorem grouped_initial_cost {τ : ℝ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hb : 0 < b) (hτ : 0 ≤ τ)
    (hsite : (CoverScale.sites (Cube D) (d+1) : ℝ) ≤ r*(n : ℝ)^(9/10 : ℝ))
    (hs : (s : ℝ) ≤ volume τ r n) (table : (groupedGrid width position input order fit s b owner).Tables K) :
    (groupedBottom width position input order fit s b owner F ord table).route.potential F.weight / b ≤
      ((1+2*F.weight) * Fintype.card (Direction q) * (96*(4*q+1)+1)) *
        volume τ r n * (logWidth r n : ℝ)^3 := by
  simpa only [one_mul] using
    (grouped_initial_cost_with_factor width position input order fit s b owner F ord
      (C := 1) le_rfl hn hr hb hτ hsite (by simpa only [one_mul] using hs) table)

section Final

open Filter

/-- On the cover chosen from the actual batch and processor length, run all
epochs on the grouped public grid. Uniformly over all valid histories, the
normalized nonlocal bits are little-o of the exterior allowance. The same
histories sum to the independent bottom tensors on every external assignment. -/
theorem eventually_grouped_histories {τ α : ℝ} (hτ : 0 < τ) (hτ' : τ < 1/2)
    (hgrowth : τ*Real.logb 2 ((CoverScale.factor (Cube D) : ℝ)^F.drop) ≤ α/10)
    (hα : α/10 < 9/10) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ ε > (0:ℝ), ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
    (r : ℝ) ≤ 2 ^ ((n : ℝ)^ω) →
    let d := CoverScale.initialDepth (Cube D) r n - 1
    ∃ deep : F.floor+1+F.drop*epochs τ n ≤ d+1,
    ∀ {p s b : ℕ} {P A : Type} [Fintype A] (width : A → ℕ)
      (position : (Fin q → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
      (input : P ≃ Fin p) (order : Fin (Fintype.card (Fin q → Deck (d+2))) ≃ (Fin q → Deck (d+2)))
      (fit : p ≤ r*n) (owner : A → Fin q → Deck (d+2))
      (table : (groupedGrid width position input order fit s b owner).Tables K),
      0 < b → (s : ℝ) ≤ volume τ r n →
      let bottom := groupedBottom width position input order fit s b owner F ord table
      let T := epochs τ n
      let H := F.histories deep bottom T
      (∀ x, (F.copies bottom.pack T).tensor x = ∑ j, (H.term j).pack.tensor x) ∧
      ∀ j, (H.term j).route.nonlocalWidth / ((b : ℝ)*F.fan^T) ≤ ε*exterior (τ/5) r n := by
  let C := (1+2*F.weight) * (Fintype.card (Direction q) : ℝ) * (96*(4*(q:ℝ)+1)+1)
  have hw : 0 ≤ 1+2*F.weight := by linarith [F.weight_pos]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨ω,hω,decay⟩ := F.eventually_nonlocal_width hτ hτ' 3
  refine ⟨ω,hω,?_⟩
  intro ε hε
  filter_upwards [eventually_ge_atTop 1,decay C ε hC hε,
    CoverScale.eventually_depths (Cube D) F.drop F.floor hτ.le hgrowth hα] with n hn hd hc
  intro r hr hbatch d
  obtain ⟨hfloor,heq,_,hsite,_⟩ := hc r hr
  have hs : d+1 = CoverScale.initialDepth (Cube D) r n := by
    dsimp only [d,CoverScale.initialDepth]
    omega
  have deep : F.floor+1+F.drop*epochs τ n ≤ d+1 := by rw [hs]; omega
  refine ⟨deep,?_⟩
  intro p s b P A _ width position input order fit owner table hb hsize bottom T H
  have hv : (CoverScale.sites (Cube D) (d+1) : ℝ) ≤ r*(n : ℝ)^(9/10 : ℝ) := by rw [hs]; exact hsite
  have hstart := grouped_initial_cost width position input order fit s b owner F ord hn hr hb hτ.le hv hsize table
  exact ⟨F.histories_tensor (P := A) (bits := fun a => b*width a) deep bottom.pack bottom rfl T le_rfl,hd r hr hbatch hb deep hv bottom hstart⟩

end Final

end Packing.PhysicalEpochs

end BorderVNP
end Computability
end OAI
