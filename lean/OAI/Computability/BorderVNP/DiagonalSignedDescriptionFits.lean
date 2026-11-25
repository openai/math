import OAI.Computability.BorderVNP.PackedGridSeedWordsFit
import OAI.Computability.BorderVNP.DiagonalJointSeedStorage

/-! # Length and representability of each opaque body at its signed descriptor pointer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes GridPlacement BottomGridBank BottomReports Inherited InheritedBank Cover TeamContraction
open Diagonal.CellEntries Diagonal.ExternalSew ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped BigOperators Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

open TeamScales
open private n_header from OAI.Computability.BorderVNP.PackedGridSeedWordsFit

variable (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (siteID : (W.routedFine position).Site ↪ Fin s) (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channelID : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groupID : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2))

/-- Each original factor body fits the physical description section after
its published length header. That length is itself representable in the
header, even if the encoded original uses none of the reserved payload. -/
theorem seed_body_source_fits (factor : ℕ) (hr : 1≤r) (hf : 8≤factor) :
    let H := factor*logWidth r n
    let budget := bodyBudget (seedBoxCapacity n r q depth (Fintype.card (Direction q)))
    let description := seedDescriptionWidth n r q depth H budget
    let bytes := Packet.Source.boxBody (W.seedStored position code siteID edgeID portID channelID groupID c)
    description ≤ n → H+bytes.length ≤ description ∧ bytes.length < 2^H := by
  intro H budget description bytes small
  have body := W.seedBody_room position code siteID edgeID portID channelID groupID c
  have full : H+bytes.length ≤ description := (Nat.add_le_add_left body H).trans (Nat.le_add_right _ _)
  exact ⟨full,((Nat.le_add_left _ _).trans (full.trans small)).trans_lt (n_header hr hf)⟩

end Packing.DeckGrid.WiredWitness

namespace Diagonal

open Filter Cover Epoch Crossing Packing Inherited DeckGrid TeamScales Shortening.PublicCapacity
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- The very seed description used in the reserved packet satisfies the
bound needed by the header decoder at every later field and layout. -/
theorem JointSchedule.eventually_signed_description_fit (b : JointSchedule s E deg Q A B j) (factor : ℕ) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let axes := Fintype.card (Cube D)
      seedDescriptionWidth n r axes d (factor*logWidth r n)
        (BottomGridBank.bodyBudget (seedBoxCapacity n r axes d (Fintype.card (Direction axes)))) ≤ n := by
  filter_upwards [b.eventually_programSeedStorage factor,eventually_ge_atTop 1] with n store hn
  have alpha : 0 ≤ (s.α : ℝ) := by exact_mod_cast s.alpha_pos.le
  have fits : literal s.α n ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1≤(n:ℝ)) (by linarith : 1-(s.α:ℝ)/3≤1)).trans_eq (Real.rpow_one _))
  exact store.2.2.2.1.trans ((Nat.div_le_self _ _).trans fits)

end Diagonal

end BorderVNP
end Computability
end OAI
