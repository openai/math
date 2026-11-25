import OAI.Computability.BorderVNP.DiagonalSelectedReportRows
import OAI.Computability.BorderVNP.PackedSeedLiteralMatrix
import OAI.Computability.BorderVNP.DiagonalGridReportRoom

/-! # Physical word and shift bounds for the marked slots of selected signed reports -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes GridPlacement BottomGridBank BottomReports Inherited Cover TeamContraction
open Diagonal.CellEntries Diagonal.ExternalSew ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar TeamScales
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p : ℕ} (siteID : (W.routedFine position).Site ↪ Fin s) (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p)

/-- Decoding a marked position identifies its original grammar label and a bit of
a bounded exponent. In particular the decoded place is a valid machine shift. -/
theorem sidecarPositions_markRoom (c : Fin q → Deck (depth+2)) (next : ℕ) {w : ℕ}
    (labels : ∀ a, code a < 2^w) (hr : 1 ≤ r) (width : logWidth r n ≤ w) :
    ∀ x ∈ W.sidecarPositions position code siteID edgeID portID c next, x.parameter < 2^w ∧ x.place < w := by
  intro x mem
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp mem
  let a := W.sidecarEquiv position code siteID edgeID portID c next i
  have fields := W.sidecarEquiv_fields position code siteID edgeID portID c next i
  have bits : Nat.clog 2 (r*(2*d.val+1)+1) ≤ logWidth r n := by
    rw [Shortening.PublicCapacity.public_logWidth]
    apply Nat.clog_mono_right
    have h : 2*d.val+2 ≤ 2*n := by have := d.isLt; omega
    nlinarith [Nat.mul_le_mul_left r h]
  exact ⟨fields.1.trans_lt (labels a.val.1),fields.2.1.trans_lt (a.val.2.isLt.trans_le (bits.trans width))⟩

end Packing.DeckGrid.WiredWitness

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP
open VPVNP.ParseGrammar EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K Gadget : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pins link k d a regs rw ec width s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)

variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
    (q : (packHistory (Subtype.mk (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words) good)
      plan.compiled.machine.epoch T).Index)
open BorderVNP.Cube (TableEntry)
open BorderVNP.Cube.Physical Packing.CellAddresses Packing.BottomReports
open BorderVNP.Packing.RoutingOutputs.NativeDemands
open RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open DiagonalTallyAllocation DiagonalTallyCellReports ReportDirectory

variable {F : Type} [Field F] (cube : FixedCube F) (α ξ : ℝ)
    (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)

variable (parameters : RoutingISA.SignedTaskArena.Parameters)
variable (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (arenaBase profileBits : ℕ) (frame origin : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "code" => (ParseTable.numberedLabelEquiv ord k s).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "B" => signedCoreDirectory plan p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters.privateGap
local notation3 (prettyPrint := false) "rc" => plan.signedReceivedRows p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin

/-- Every mark of every cell received by a selected team fits the physical word.
The parameter and shift bounds are uniform over all routes and all teams. -/
theorem signedReceivedRows_markRoom {w : ℕ} (labels : Branch.pairedTableParameters (k+1) s ≤ 2^w)
    (hr : 1 ≤ r) (width : logWidth r (k+1) ≤ w)
    (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1)) :
    ∀ c ∈ (rc v).cells u, ∀ b ∈ c.bundles, ∀ x ∈ b.positions, x.parameter < 2^w ∧ x.place < w := by
  intro c hc b hb x hx
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hc
  rw [plan.signedReceivedRows_bundles p fit W position code sites edges ports table words
    good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v u i] at hb
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
  exact W.sidecarPositions_markRoom position code sites edges ports _ _
    (fun a => (ParseTable.numberedLabelEquiv ord k s a).isLt.trans_le labels) hr width x hx

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

namespace Diagonal

open Filter Crossing Branch TeamScales PackedHistoryCircuit.Normalized

universe u
variable {F : Type*} [Field F] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {a extra E d Q A B j : ℕ} {s : EpochScales S a extra}

/-- The selected marked reports all fit the word on this same large-length
range, before choosing any of their potential routed cells. -/
theorem JointSchedule.eventually_markRoom (b : JointSchedule.{u} s (E+1) d Q A B j) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let w := b.physical.word n
      pairedTableParameters n (stretch b.σ n) ≤ 2^w ∧ 1 ≤ r ∧ logWidth r n ≤ w :=
  b.eventually_gridMarkWidths

end Diagonal

end BorderVNP
end Computability
end OAI
