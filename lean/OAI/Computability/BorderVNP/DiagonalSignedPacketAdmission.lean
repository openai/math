import OAI.Computability.BorderVNP.DiagonalSignedDemandLabels
import OAI.Computability.BorderVNP.DiagonalNativeDemandAdmission

/-! # Eligible cube headers on the calibrated signed histories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Packing PhysicalEpochs DeckGrid
open Diagonal Diagonal.CellEntries Diagonal.ExternalSew TeamContraction TeamScales Filter EnrichedOuter
open ParseBatch ParseBatchVerifier Prewire VPVNP RoutingOutputs
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxRecDepth 6000
set_option maxHeartbeats 2400000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {n r d T copies header work R ell : ℕ}
    (plan : SeedPlan S n r d T copies header work)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "block" => GridHosts.inputBlockWidth r n axes d
local notation "mass" => initialMass (D := D) n r d copies header
local notation "admit" => Boundary.Good (S:=S) (start:=d+1)
  (bits:= fun _ : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) => copies*GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d)
  (shape:=boundaryShape S (d+1)) (w:=60*logWidth r n) (boundaryBudget S mass)
local notation "cap" => seedBoxCapacity n r axes d (Fintype.card (Direction axes))
local notation "desc" => seedDescriptionWidth n r axes d (header*logWidth r n) (BottomGridBank.bodyBudget cap)

/-- The eligible header test on the one packet per attained history, with
the actual receiver and width of every delivered private or exterior field. -/
def AdmitsSignedPackets {F : Type} [Field F] (cube : FixedCube F) (α ξ : ℝ)
    (count : (fan S)^T*copies=R+1)
    (calibrated : plan.SignedLabelRows count ell (cube.pred+1) α ξ) : Prop :=
  ∀ {t pins inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring R r t pins ell inner n Edge),
  ∀ (lit : G.program.length+t = literal α n) (order : Fin tiles ≃ (Fin axes → Deck (d+2)))
    (pos : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {g : ℕ} {len : Fin n} {st : Fin g} (W : WiredWitness G len D axes d order st)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G axes d order pos copies).Tables K)
    (words : Boundary.Pins S (d+1) (boundaryShape S (d+1)) (60*logWidth r n) 0 → Bool)
    (ready : admit 0 (Boundary.seedState S G d order pos copies table words)),
    let dir := freeDirectory R r (G.program.length+t) ell tiles block ((fan S)^T*tiles) desc
    let bounds := (calibrated G lit order pos W tag sites edges ports table words ready).choose
    let bottom : Admissible admit 0 := ⟨_,ready⟩
    let M := plan.compiled.machine
    ∀ (hd : 0 < BorderVNP.Cube.alphabet α n) (hp : (fieldSewParams G axes d).Valid)
      (q : (packHistory bottom M.epoch T).Index) {cells : ℕ}
      (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells) (gap : ℕ),
      let state := ((packHistory bottom M.epoch T).term q).val
      let N := enrichedSewnLayout G axes d order pos count M bottom rfl q
      let cell (v : N.Site) := number (reduceMove (depth S (d+1) T) (state.route.origin v))
      let old := originalDescriptionRows M bottom q dir rfl order
      let live := (Equiv.refl (FreeBlock R tiles)).toEmbedding
      let edge := FieldExport.mergedEdges (fieldSewParams G axes d) hp state.rows.edge
      let port : FreeBlock R tiles ↪ Fin ((R+1)*tiles) := finProdFinEquiv.toEmbedding
      let list := NativeDemands.rows N cell edge port dir old live gap
      let recv := NativeDemands.receiver N cell edge port dir old live gap bounds
      let packet := plan.signedPackets count G order pos W tag sites edges ports table words ready cube α ξ
        calibrated lit hd hp number gap q
      ∀ select : BorderVNP.Cube.Packet cube.pred (BorderVNP.Cube.alphabet α n) packet.blocks →
          BorderVNP.Cube.Selector cube.pred cube.copies cube.h,
        BorderVNP.Cube.Physical.broadcastAllowed R (exterior ξ r n) packet.blocks cube.b cube.copies cube.h
          packet.label recv (fun i : Fin list.length => list[i.val].width) (BorderVNP.Cube.Physical.broadcast cube.b cube.width select)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

namespace Diagonal

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Packing PhysicalEpochs DeckGrid
open TeamScales Filter ExternalSew ParseBatch ParseBatchVerifier Prewire
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxRecDepth 6000
set_option maxHeartbeats 2400000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- All sufficiently large lengths of this single chosen schedule admit
every original routed selector on the same cube packets as the numbered
polynomial expansion, uniformly over the later rows and pin valuations. -/
theorem JointSchedule.eventually_signed_packet_admission {F : Type} [Field F] (cube : FixedCube F)
    {scales : EpochScales S (cube.pred+1) extra} (b : JointSchedule scales E deg Q A B j) (header : ℕ) :
    ∀ᶠ n : ℕ in atTop,
    let r := stretch b.ρ n
    let d := CoverScale.initialDepth (Cube D) r n-1
    let T := epochs scales.τ n
    let copies := width n scales.α
    let R := b.physical.teamsPred n
    ∀ work : ℕ, ∀ plan : SeedPlan S n r d T copies header work, ∃ count : (fan S)^T*copies=R+1,
      ∃ calibrated : plan.SignedLabelRows count (b.physical.link n) (cube.pred+1) scales.α ((scales.τ:ℝ)/5),
        plan.AdmitsSignedPackets cube scales.α ((scales.τ:ℝ)/5) count calibrated := by
  have pos : 0 < (scales.α:ℝ) := by exact_mod_cast scales.alpha_pos
  filter_upwards [b.eventually_signed_label_rows header,b.eventually_geometricSeedStorage header,b.eventually_lengths 0,
    RoutingOutputs.NativeDemands.eventually_packet_admission cube pos scales.label_slack.1
      (by simpa only [Nat.cast_add,Nat.cast_one] using scales.label_slack.2.2)]
    with n rows storage length admission
  intro r d T copies R work plan
  obtain ⟨count,calibrated⟩ := rows work plan
  refine ⟨count,calibrated,?_⟩
  intro t pins inner Edge _ G lit order pos g len st W tag ns ne np sites edges ports table words ready dir
    bounds bottom M hd hp q cells number gap state N cell old live edge port list recv packet select
  have budget := (calibrated G lit order pos W tag sites edges ports table words ready).choose_spec q number edge port gap
  have heads := (Nat.mul_comm copies ((fan S)^T)).trans count
  have tails : dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2) := by
    change _ ≤ (R+1)*r*((G.program.length+t)/2)
    rw [←heads,lit]
    exact storage.2.2.2.2
  exact admission r R (BorderVNP.Cube.alphabet scales.α n) cells N cell edge port dir old live gap bounds
    (CellEntries.SewnTape.teamNumber (fan S) T copies R count).symm hd (TeamScales.width n (1/4)) budget (stretch_one ..)
    (by simpa only [Nat.cast_add,Nat.cast_one] using length.teams.2) rfl rfl rfl lit (by decide : 0<2) tails select

end Diagonal

end BorderVNP
end Computability
end OAI
