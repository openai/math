import OAI.Computability.BorderVNP.PackedBankPublicBottom
import OAI.Computability.BorderVNP.PackedHistoryNormalizedGrid
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites

/-! # Initial bank caps on the saved seed state of the outer program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Cover Crossing BorderVNP.Epoch Shortening Packing Packing.DeckGrid Packing.PhysicalEpochs
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction GridPlacement Shortening.PreparedBins
open ParseBatch ParseBatchVerifier Prewire VPVNP Inherited BottomGridBank BottomReports
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] [Fintype K] {e : PaidIdentity K D m}
    (S : SiteSchedule e) {R r t pins link inner n g d : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {len : Fin n} {state : Fin g}
    {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ns ne np : ℕ} (siteID : (W.routedFine position).Site ↪ Fin ns)
    (edgeID : (W.routedFine position).Edge ↪ Fin ne) (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np)
    (table : (W.routedFine position).Tables K) (copies : ℕ)

local notation "axes" => Fintype.card (Cube D)
local notation "V₀" => GridHosts.tileCount axes d
local notation "degree" => Fintype.card (Direction axes)
local notation "H₀" => seedChannelWidth n r axes d
local notation "cap₀" => seedBoxCapacity n r axes d degree
local notation "pr" => finiteSeedPrograms W position siteID edgeID portID table copies
local notation "bottom" => finiteSeedPack W position table copies

open BorderVNP.Epoch.Round
attribute [local instance] portFintype

variable {w : ℕ} (words : Pins S (d+1) (SelectedSchedule.boundary S (d+1)) w 0 → Bool)
local notation "state₀" => seedState S G d order position copies (Pack.table bottom) words

/-- Present the finite-field bottom programs on the actual normalized seed state,
whose layer-zero port enumeration is the one consumed by the outer machine. -/
noncomputable abbrev finiteSeedStatePrograms : Site.Programs ((state₀).pack.layout) :=
  changePrivateInstance _ pr

private theorem siteCap_instance {D lev : ℕ} {P I K : Type} [Fintype I]
    {bits : P → ℕ} {L : ℝ} {p : Pack D P bits K} (r : SiteRoutes p I lev L)
    {f g : Fintype P} (old : @Site.Programs D P f bits p.layout) (full ex : Bool) (B : ℕ)
    (h : @SiteCap D K P I f _ bits lev L p r
      (if full then @Site.Programs.fullFields D P f bits _ old else @Site.Programs.bankFields D P f bits _ old) ex B) :
    let next := changePrivateInstance (fin := f) (fin' := g) p.layout old
    @SiteCap D K P I g _ bits lev L p r
      (if full then @Site.Programs.fullFields D P g bits _ next else @Site.Programs.bankFields D P g bits _ next) ex B := by
  obtain rfl : f = g := Subsingleton.elim _ _
  cases full <;> exact h

set_option maxHeartbeats 1200000 in
/-- The public count, the full stored-and-expanded count and the scalar bound of the actual
seed lineage hold in the port enumeration consumed by the outer program at level zero. -/
theorem finiteSeedStatePrograms_bounds (dB : ℕ) :
    let programs := finiteSeedStatePrograms S W position siteID edgeID portID table copies words
    SiteCap (state₀).route programs.bankFields false (seedPublicBase degree) ∧
    (∀ ex, SiteCap (state₀).route programs.fullFields ex (baseMass degree cap₀ H₀ copies dB)) ∧
    ∀ v, (programs v).program.ScalarBound (max (max 2 (max copies cap₀)) (max 1 (programs v).program.size)) := by
  intro programs
  let route := seedRoutes S G d order position copies (Pack.table bottom)
  let outer := portFintype (P := Fin V₀) (k := fan S) (b := 0)
  obtain ⟨pub,_,scalar⟩ := finiteSeedPrograms_bounds S W position siteID edgeID portID table copies
  refine ⟨?_,?_,scalar⟩
  · have cap := siteCap_instance (f := Fin.fintype V₀) (g := outer) route pr false false (seedPublicBase degree) pub
    exact cap
  · intro ex
    have cap := siteCap_instance (f := Fin.fintype V₀) (g := outer) route pr true ex (baseMass degree cap₀ H₀ copies dB)
      (finiteSeedPrograms_full_within S W position siteID edgeID portID table copies ex dB)
    exact cap

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
