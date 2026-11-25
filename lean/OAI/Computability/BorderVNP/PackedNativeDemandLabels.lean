import OAI.Computability.BorderVNP.PackedNativeDemandRows
import OAI.Computability.BorderVNP.PackedRoutingLabelBudget
import OAI.Computability.BorderVNP.DiagonalPhysicalMeanOwner
import OAI.Computability.BorderVNP.CubeDirectedIntervalPhysical

/-! # The label placement fixed by a history's actual delivery directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing Shortening CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA Finset
open BorderVNP.Cube Cube.Physical Cube.Balancing TeamScales Filter
open scoped Classical
open private live_volume data_volume from OAI.Computability.BorderVNP.PackedRoutingLabelBudget
open private sum_lanes from OAI.Computability.BorderVNP.PackedDirectoryIncoming

/-- Construct the balancing budget for the semantic seven-word array before
installing any guessed shared or private bits. The cell and width of each
incoming item are read directly from its occupied delivery row. -/
theorem eventually_rows_budget {α ξ : ℝ} (hα : 0 < α) (a : ℕ) (hξ : ξ < α/3)
    (hgap : 24*α*a+1/4 < 1-ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ {D C ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
      (N : Network D P bits) (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np)
      (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
      (gap : ℕ) (bounds : dir.DestinationBounds) (prior payload : N.Site → ℕ),
      let list := rows N cell edge port dir old live gap
      let recv := receiver N cell edge port dir old live gap bounds
      let X := exterior ξ dir.processors n
      0 < dir.teams → 0 < dir.fields → dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2) →
      dir.literal = literal α n → (∀ j, dir.description ≤ payload (old j)) →
      (∀ p, bits (live p) = dir.block) → Diagonal.ExternalSew.intercellWidth N cell ≤ 2*dir.teams*X →
      (∀ c, localRecords N true prior payload (fun v => cell v=c) ≤ width n (1/5)) →
      PackedLabelBudget N cell recv (fun i : Fin list.length => list[i.val].width) (dir.teams*X : ℕ)
        (width n (1/4)) (labelCount α a n) := by
  have he : 0 < 1-ξ := by nlinarith [Nat.cast_nonneg (α := ℝ) a]
  filter_upwards [eventually_balancing_slack hα a hgap,eventually_exterior_volume_lower he,
    eventually_literals_le hξ 3,eventually_ge_atTop 1] with n variance volume outgoing hn
  intro D C ne np P _ bits N cell edge port dir old live gap bounds prior payload list recv X teams fields tails
    literalEq desc block wires cap
  let pp := privatePair N cell edge port dir old live gap
  let lp := livePair N cell edge port dir old live gap
  have priv (j : Fin dir.entries) : (pp j.val).1 = (cell (old j)).val :=
    congrArg Prod.fst (keyPair N cell edge port dir old live gap (.inl j))
  have liveCell (p : Fin dir.teams × Fin dir.sites) :
      (lp (p.1.val*dir.sites+p.2.val)).1 = (cell (N.attach (live p))).val :=
    congrArg Prod.fst (keyPair N cell edge port dir old live gap (.inr p))
  have hw := volume dir.processors dir.teams bounds.processors teams
  rw [Nat.mul_comm] at hw
  have hm := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (1/4 : ℝ))
  have var := variance (dir.teams*X : ℕ) (width n (1/4)) hw (Nat.cast_nonneg _) hm
  have room : width n (1/5) ≤ width n (1/4) :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))
  refine ⟨?_,?_,fun c => (cable_incidence_le_records N cell prior payload c).trans ((cap c).trans room),?_,var⟩
  · rw [live_volume]
    exact_mod_cast wires.trans_eq (by ring : 2*dir.teams*X = 2*(dir.teams*X))
  · have h := dir.populated_width pp lp bounds.processors fields bounds.block tails
    rw [literalEq] at h
    have nf : dir.fields+1 ≤ 3 := by have := bounds.fields; omega
    have data : (list.map Directory.Row.width).sum ≤ dir.teams*X :=
      h.trans ((Nat.mul_le_mul_left dir.teams (Nat.mul_le_mul_right _ nf)).trans
        (Nat.mul_le_mul_left _ (by simpa only [←Nat.mul_assoc] using outgoing dir.processors)))
    rw [data_volume]
    exact_mod_cast data
  · intro c
    have h := dir.incoming_le_records N cell pp lp bounds old live prior payload desc block priv liveCell c
    apply le_trans _ (h.trans ((cap c).trans room))
    rw [card_filter,sum_lanes (fun i : Fin list.length => list[i.val].width) (fun i => c = recv i)]
    apply le_of_eq
    congr 1
    funext i
    exact propext (Fin.ext_iff.trans (eq_comm.trans (by rw [receiver_val]; rfl)))

/-- Order occupied directed edges by the actual sparse physical RAM slot. -/
noncomputable def cableOrder {D C ne : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) :
    N.CrossingEdge cell ≃ Fin (Fintype.card (N.CrossingEdge cell)) :=
  (NativeIntervals.exists_ordered_rows ((Function.Embedding.subtype _).trans edge)).choose

/-- The monotone addresses of those ordered cables are exactly their stored row slots. -/
theorem cableOrder_stored {D C ne : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) :
    ∃ row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin ne,
      ∀ e : N.CrossingEdge cell, row (cableOrder N cell edge e) = edge e.val :=
  (NativeIntervals.exists_ordered_rows ((Function.Embedding.subtype _).trans edge)).choose_spec

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
