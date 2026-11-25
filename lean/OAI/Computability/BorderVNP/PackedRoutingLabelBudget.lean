import OAI.Computability.BorderVNP.PackedRoutingIncidence
import OAI.Computability.BorderVNP.CubeGroupChargeRoom
import OAI.Computability.BorderVNP.CubeLabelProducerVolumes
import OAI.Computability.BorderVNP.DiagonalExternalSewVolume

/-! # The label-selection budget on the actual compact demand array

At the chosen paper scales both variance estimates hold for the cable and data rows
emitted by geometry. Cell incidences use the local expanded weight. The total data
volume uses the per-team processor tails, independent of the placement of their contents.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing Shortening CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA Finset
open BorderVNP.Cube Cube.Physical Cube.Balancing TeamScales Filter
open scoped Classical
open private list_get_sum from OAI.Computability.BorderVNP.CubeLabelProducerVolumes

private theorem live_volume {D C : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) :
    Fintype.card (LiveBit N cell) = Diagonal.ExternalSew.intercellWidth N cell := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Diagonal.ExternalSew.intercellWidth,testedWidth]
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro e unused
    have h : ¬ cell (N.src e) ≠ cell (N.dst e) := fun live => unused ⟨⟨e,live⟩,rfl⟩
    simp [h]
  · intro e
    simp [e.property]

private theorem data_volume (rows : List Directory.Row) :
    Fintype.card (Bits (fun i : Fin rows.length => rows[i.val].width)) = (rows.map Directory.Row.width).sum := by
  rw [Fintype.card_sigma, list_get_sum]
  simp only [Fintype.card_fin]
  rfl

/-- The balancing scan receives a genuine `PackedLabelBudget` for every sufficiently
large processor size and for every realized native layout at that size. The length
threshold precedes the choice of the field-dependent local programs, number of teams,
compact row pointers, network, and receiving-cell map. -/
theorem eventually_native_labelBudget {α ξ : ℝ} (hα : 0 < α) (a : ℕ) (hξ : ξ < α/3)
    (hgap : 24*α*a+1/4 < 1-ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ {D C s m t d k w W : ℕ} {P σ : Type} [Fintype P] [Fintype σ]
      {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ)
      (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin t)
      (F : Fields s m t C d k w σ) (x : σ → Bool)
      (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
      (head origin gap : ℕ) (before after : ℕ → ℕ) (prior payload : N.Site → ℕ),
      Represents N cell aux siteID edgeID portID F x → (∀ c, (F.cells c).val = c.val) →
      (∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w) →
      (∀ p, bits (live p) = dir.block) → dir.DestinationBounds → 0 < dir.teams → 0 < dir.fields →
      dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2) →
      dir.literal = literal α n → (∀ j, dir.description ≤ payload (old j)) →
      Image F (siteID ∘ old) (portID ∘ live ∘ finProdFinEquiv.symm) x origin before →
      (privateLayout head origin m C dir.entries dir.description gap).Image before dir.entries after →
      (privateLayout head origin m C dir.entries dir.description gap).Fits W before →
      let X := exterior ξ dir.processors n
      let rows := dir.directory (Directory.ISA.placement after (bases origin m C dir.entries).privatePairs)
        (Directory.ISA.placement after (bases origin m C dir.entries).livePairs)
      Diagonal.ExternalSew.intercellWidth N cell ≤ 2*dir.teams*X →
      (∀ c, localRecords N true prior payload (fun v => cell v = c) ≤ width n (1/5)) →
      ∀ recv : Fin rows.length → Fin C, (∀ i, (recv i).val = rows[i.val].cell) →
        PackedLabelBudget N cell recv (fun i => rows[i.val].width) (dir.teams*X : ℕ)
          (width n (1/4)) (labelCount α a n) := by
  have he : 0 < 1-ξ := by nlinarith [Nat.cast_nonneg (α := ℝ) a]
  filter_upwards [eventually_balancing_slack hα a hgap, eventually_exterior_volume_lower he,
    eventually_literals_le hξ 3, eventually_ge_atTop 1] with n variance volume outgoing hn
  intro D C s m t d k w W P σ _ _ bits N cell aux siteID edgeID portID F x dir old live head origin gap
    before after prior payload net code fit widthEq bound teams fields tails literalEq desc img run room X rows wires localCap recv atCell
  have hM := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (1/4 : ℝ))
  change (width n (1/4) : ℝ) ≤ (n:ℝ)^(1/4 : ℝ) at hM
  have hw := volume dir.processors dir.teams bound.processors teams
  rw [Nat.mul_comm] at hw
  have hv := variance (dir.teams*X : ℕ) (width n (1/4)) hw (Nat.cast_nonneg _) hM
  have localRoom : width n (1/5) ≤ width n (1/4) :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))
  have arrivals := img.private_incoming N cell aux siteID edgeID portID F net code fit dir old live
    widthEq bound head origin gap before after run room prior payload desc recv atCell
  refine ⟨?_,?_,fun c => (cable_incidence_le_records N cell prior payload c).trans ((localCap c).trans localRoom),
    fun c => (arrivals c).trans ((localCap c).trans localRoom),hv⟩
  · rw [live_volume]
    exact_mod_cast (wires.trans_eq (by ring : 2*dir.teams*X = 2*(dir.teams*X)))
  · let pp := Directory.ISA.placement after (bases origin m C dir.entries).privatePairs
    let lp := Directory.ISA.placement after (bases origin m C dir.entries).livePairs
    have h := dir.populated_width pp lp bound.processors fields bound.block tails
    rw [literalEq] at h
    have nf : dir.fields+1 ≤ 3 := by have := bound.fields; omega
    have data : (rows.map Directory.Row.width).sum ≤ dir.teams*X := calc
      _ ≤ dir.teams*((dir.fields+1)*(dir.processors*literal α n)) := h
      _ ≤ dir.teams*(3*(dir.processors*literal α n)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ nf)
      _ ≤ dir.teams*X := Nat.mul_le_mul_left _ (by simpa only [←Nat.mul_assoc] using outgoing dir.processors)
    rw [data_volume]
    exact_mod_cast data

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
