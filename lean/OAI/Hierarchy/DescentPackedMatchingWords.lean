import OAI.Hierarchy.DescentPackedStageRun
import OAI.Hierarchy.DescentPackedMatchSourceChart

namespace OAI
/-! # The chooser publishes the very colony and paint used by the recorded stage -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentPackedColony DescentColonies DescentGL DescentBinaryField DescentAffineColors StarKeys DescentHostDirectory
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {C L k ℓ Δ d b w hBits : ℕ} {J V F P : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {p ε : ℝ}
variable (A : GroupStage W G p ε J V k) (ej : J≃Fin C) (ev : V≃Fin L) (h : L≤2^ℓ)
local notation "fee" => A.wire*(A.z*G.b)
local notation "D" => DescentHostDegree.gap A.degree
local notation "a" => DescentHostDegree.packExponent 20 A.degree
local notation "cap" => 2^a*(fee*A.cap)
local notation "full" => W.siteUnits (fun v => A.hub (Prod.snd (A.pos v))) A.records A.wire 256 A.hist
local notation "outgoing" => fun v : W.graph.Site => Finset.card (Finset.filter (fun edge => W.graph.src edge = v) W.core)
local notation "wt" => (fun g=>Padded.table (H:=2^ℓ) (A.groupedCounts ej ev full g))
local notation "amt" => (fun g=>Padded.table (H:=2^ℓ) (A.groupedCounts ej ev outgoing g))
open DescentStageEdgeReceipt DescentKernelHistory.BitDescription

def publishedTicket (rs : DynamicSplit.Roster ℓ Δ) (i : Fin (2^k-1)) (j : Candidate k)
    (v : Fin (2^ℓ)) (g : Fin C) (x : Block k) :=
  PackedWinnerKey.value A.fieldBits i j x (PackedSplit.state (DynamicSplit.incoming rs) wt D cap
    (modulus A.fieldBits) (seedAt k i) v g)

theorem published_actor (he : 0≤ε) (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v z:V,i=(ev v).castLE h ∧ j=(ev z).castLE h ∧ v∈A.near z)
    (i : Fin (2^k-1)) (j : Candidate k) (mu : seedAt k i=(scannedRows he A.stage).μ)
    (paint : j=code (scannedRows he A.stage).α (scannedRows he A.stage).β) (u : W.graph.Site) :
    (A.publishedTicket ej ev rs i j ((ev (A.pos u).2).castLE h) (ej (A.pos u).1) (A.block u)).val =
      1+2*DescentPacking.PackedMatch.Local.heap
        (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 + (scanColorAt he A.stage u).toNat := by
  let actor (seed : Nonzero k) (side : Candidate k) :=
    let blocks := reindexedBlock W.graph A.block (multiplier A.fieldBits seed)
    let bound := small_reindexed W.graph A.pos A.block full A.small (multiplier A.fieldBits seed)
    let home := occupiedHome W.graph A.pos blocks full (groupedNear A.near) D a (fee*A.cap) bound
    let address := occupiedAddress W.graph (fee*A.cap) (groupedNear A.near) D a
      (blockMass W.graph A.pos blocks full) bound A.pos blocks
    1+2*DescentPacking.PackedMatch.Local.heap (address (home u)).2+(thick side (blocks u)).toNat
  have current : (A.publishedTicket ej ev rs i j ((ev (A.pos u).2).castLE h)
      (ej (A.pos u).1) (A.block u)).val = actor (seedAt k i) j := by
    dsimp only [actor]
    rw [publishedTicket,PackedWinnerKey.value_actual,A.grouped_cell_at ej ev h rs members (seedAt k i) u]; rfl
  refine current.trans ?_
  rw [mu,paint]
  let recorded := scannedRows he A.stage
  let block := scanBlocks A.stage recorded.μ u
  let color (α : DescentWalshTables.Bits k) (β : ZMod 2) :=
    decide (DescentWalshTables.binaryRow α ((address k).symm block) + β = 0)
  have sameColor : thick (code recorded.α recorded.β) block = scanColorAt he A.stage u :=
    congrArg₂ color (@linear_code k recorded.α recorded.β) (@offset_code k recorded.α recorded.β)
  exact congrArg (fun side : Bool => 1 + 2*DescentPacking.PackedMatch.Local.heap
    (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 + side.toNat) sameColor

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
