import OAI.Computability.BorderVNP.PackedFrozenProfilePins
import OAI.Computability.BorderVNP.PackedSewnFragmentSelectedFields
import OAI.Computability.BorderVNP.PackedTerminalStagedSewnImage

/-! # The actual signed, sewn terminal packet source on the selected frozen profile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained.Terminal
open Packing.Inherited FrozenTape VPVNP.VerifierNetwork
variable {X Geo : Type} [Fintype X] [Fintype Geo] {sites w d res : ℕ}
    (S : Format) (x : ((X ⊕ Fin res) ⊕ S.Output Geo sites w d) → Bool)
private theorem saved_history_read (z : Pins S.Rows S.Payload d) : (saved S).eval x (.inr z) = (history S).eval x z := by
  simp [saved,history]
private theorem saved_width_read (v : Fin sites) (b : Bool) (j : Fin w) :
    (saved S).eval x (.inl (.inr (v,b,j))) = (width S b).eval x (v,j) := by
  simp [saved,width]
end PackedHistoryCircuit.Retained.Terminal

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Shortening.PreparedBins
open Packing.PhysicalEpochs
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales VPVNP.VerifierNetwork
open TerminalCells FieldExport GridHosts Diagonal.ExternalSew.RowTrace Packing.CellAddressCircuit Packing.SewnField
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {σ : Type} [Fintype σ] {g : ℕ} {len : Fin n} {state : Fin g}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K) (x : σ → Bool)

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*logWidth r n
local notation "mass" => initialMass (D:=D) n r d copies headerFactor
local notation "V" => CoverScale.sites (Cube D) (d+1)
local notation "extent" => copies*GridHosts.inputBlockWidth r n axes d
local notation "header" => WorkWords.grouped V extent
local notation "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "geom" => (plan.execute G order position σ).choose.eval x
local notation3 (prettyPrint := false) "old₀" => Boundary.seedBirthPrograms S order position W tag sites edges ports table geom
local notation3 "fmt" => Boundary.seedFormat G order position copies
local notation3 "source" => plan.frozenStart G order position σ

local notation3 (prettyPrint := false) "seed₀" => plan.frozenLeaf G order position W tag sites edges ports table x

variable (wr : WidthRanges S (d+1) T (60*logWidth r n)) (hm : 0 < m)
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ)

local notation3 "compiled" => plan.compiled
local notation3 (prettyPrint := false) "steps" => (compiled).tapeSteps fmt header key wr hm
local notation3 (prettyPrint := false) "names" => (compiled).privateSiteRows key seeds


variable {reserve : ℕ} (widths : ℕ → ℕ)
    (ord : ∀ j, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n) j ≃ Fin (widths j))
    (fit : broadcastWidth (fan S) widths T ≤ reserve)

local notation3 (prettyPrint := false) "epochFormat" => ProgramSchemas.epoch S (d+1) w fmt T
local notation3 (prettyPrint := false) "aug" => compile steps T le_rfl (repeatLeaf (fan S) source T)
local notation3 (prettyPrint := false) "base" => (plan.execute G order position σ).choose


private theorem merged_mask {az ay : Type} [Fintype az] [Fintype ay] {old : ℕ} {Edge : Type}
    (p : FieldExport.Params) (hp : p.Valid) (edge : Edge ↪ Fin old) (occupied : Fin old → az)
    (f : Frame ay az) (y : ay → Bool)
    (live : ∀ i, (withSewnFields f).eval y (.inl (occupied i))=true ↔ i ∈ Set.range edge)
    (i : Fin (old+p.slots)) :
    (withSewnFields f).eval y (FinalTies.sewnPresent p occupied i) = true ↔ i ∈ Set.range (mergedEdges p hp edge) := by
  apply FinalTies.sewn_present p hp edge occupied f y
  intro j
  simpa only [withSewnFields,Frame.subst_eval,constants_eval,Sum.elim_inl] using live j

private theorem castGroupPort_val {a a' : ℕ} (h : a=a') (j : ℕ)
    (v : Fin ((fan S)^j) × Fin a) :
    (finProdFinEquiv v).val = (Flat.portRows j (privatePorts S (finCongr h).toEmbedding j) v).val := by
  subst a'
  exact (fieldIncomingPorts_val S a j v).symm

variable {R rTime rPins ell rInner : ℕ} {Wire : Type}
    (actual : Wiring R r rTime rPins ell rInner n Wire) (count : (fan S)^T*copies=R+1)
    {cells k packetWidth : ℕ} (cellNumber : (Cube D → Deck (EnrichedOuter.depth S (d+1) T+1)) ≃ Fin cells)
    (vf : (boundaryShape S (d+1) T).sites ≤ 2^(60*logWidth r n)) (cf : cells ≤ 2^k)
    (hg : 0 < inputBlockWidth r n (Fintype.card (Cube D)) d) (short : inputBlockWidth r n (Fintype.card (Cube D)) d ≤ ell)
    (pw : copies*inputBlockWidth r n (Fintype.card (Cube D)) d < 2^(60*logWidth r n))
    (extend : 60*logWidth r n ≤ packetWidth) (room : 15*(S.publicProgramFactor^T*initialMass (D:=D) n r d copies headerFactor) < 2^(60*logWidth r n))
    (hook : Compiled.HookRoom S T (60*logWidth r n) (initialMass (D:=D) n r d copies headerFactor))
    (q : (packHistory (plan.frozenLeaf G order position W tag sites edges ports table x) plan.compiled.machine.epoch T).Index)

local notation3 (prettyPrint := false) "s₁" => ((packHistory seed₀ (compiled).machine.epoch T).term q).val
local notation3 (prettyPrint := false) "N₀" => (flattenPack T (s₁).pack).layout
local notation3 (prettyPrint := false) "code₁" => ((compiled).machine.nativeCode seed₀ base x rfl widths ord fit q).val
local notation3 (prettyPrint := false) "input₁" => Retained.branch aug (broadcastOrder (fan S) widths ord T) fit x code₁
local notation3 (prettyPrint := false) "prior₁" => (compiled).machine.terminalPrivatePrograms names number seed₀ old₀ q
local notation "offs" => flatOffset (compiledOffset S (d+1)) T
local notation "g₁" => inputBlockWidth r n axes d
local notation3 (prettyPrint := false) "p₁" => (⟨R,r,actual.program.length+rTime,ell,g₁,tiles⟩ : FieldExport.Params)
local notation3 (prettyPrint := false) "hp₁" => (⟨hg,short,gridRoom actual Fintype.card_pos⟩ : (p₁).Valid)
local notation3 (prettyPrint := false) "h₁" => attachedHosts actual Fintype.card_pos count N₀
local notation3 (prettyPrint := false) "lane₁" => groupedLane actual tiles Fintype.card_pos ((fan S)^T) copies count
local notation3 (prettyPrint := false) "edge₁" => mergedEdges p₁ hp₁ (s₁).rows.edge
local notation3 (prettyPrint := false) "port₁" => (finProdFinEquiv : FreeBlock R tiles ≃ Fin ((R+1)*tiles)).toEmbedding
local notation3 (prettyPrint := false) "oldPort" => Flat.portRows T (privatePorts S key T)
local notation3 (prettyPrint := false) "finalN" => finalLayout p₁ h₁
local notation3 (prettyPrint := false) "cells₁" => fun v => cellNumber (reduceMove (EnrichedOuter.depth S (d+1) T) ((s₁).route.origin v))
local notation3 (prettyPrint := false) "F₀" => TerminalCells.fields (Move := allowedMoves (Cube D) S.budget) (q := axes)
  (d := EnrichedOuter.depth S (d+1) T) (E := (boundaryShape S (d+1) T).edges) vf cf (@groupRow ((fan S)^T) tiles offs)
  (fun _ => copies*g₁)
local notation3 (prettyPrint := false) "route₁" => Retained.Terminal.route (X := σ) (reserve := reserve) epochFormat
local notation3 (prettyPrint := false) "ext₁" => Retained.Terminal.width (X := σ) (reserve := reserve) epochFormat true
local notation3 (prettyPrint := false) "source₁" => withSewnFields (boundFrame (factorEnum D) cellNumber cf route₁ ext₁)
local notation3 (prettyPrint := false) "F₁" => FieldExport.fields F₀ p₁ (attachedName offs copies)
local notation3 (prettyPrint := false) "source₂" => stagedSource F₁ source₁
local notation3 (prettyPrint := false) "F₂" => Fields.widenWidths (stagedFields F₁) extend (Sum.inr false)
local notation3 (prettyPrint := false) "hist₁" => stagedHistory (Sewn.terminalHistory epochFormat (F₀).sites
  (Grid.physicalOperands actual Fintype.card_pos count hg short F₀ (attachedName offs copies) FinalTies.routePresent))
local notation3 (prettyPrint := false) "saved₁" => (Retained.Terminal.saved epochFormat).eval input₁
local notation3 (prettyPrint := false) "rawState" => sewnPrograms N₀ lane₁ (h₁).bundle (fun _ : FreeBlock R tiles => g₁)
    (freeLane hg (gridRoom actual Fintype.card_pos)) (h₁).groupOwner ((h₁).groupAligned hg (gridRoom actual Fintype.card_pos))
    (s₁).rows.edge oldPort edge₁ port₁ prior₁
local notation3 (prettyPrint := false) "scp" => (epochFormat).schema.append
  (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*tiles) w)

open private oldWire staged_old from OAI.Computability.BorderVNP.PackedTerminalStagedFields

include pw room hook in
/-- With the frozen native code for this history, the actual signed terminal
provides the post-sewing program tape, all its field addresses, and the
true occupied cable and port masks on the same staged output. -/
theorem frozen_signed_packet_geometry :
    (scp).Image ((hist₁).eval (Sum.elim ((source₂).eval input₁) saved₁))
        ((s₁).rows.site.trans Fin.valEmbedding) (fun v => (rawState v).program) ∧
    CellAddressPhysical.Represents finalN cells₁ (fun v => (rawState v).program.size)
      (s₁).rows.site edge₁ port₁ F₂ ((source₂).eval input₁) ∧
    (∀ i, (source₂).eval input₁ (oldWire (FinalTies.sewnPresent p₁ FinalTies.routePresent i)) = true ↔
      i ∈ Set.range edge₁) ∧ ∀ i, true = true ↔ i ∈ Set.range port₁ := by
  have room₂ : 2*(S.publicProgramFactor^T*mass)<2^w := by omega
  have pins := plan.frozen_profile_pins G order position W tag sites edges ports table x wr hm seeds number
    widths ord fit room₂ hook q
  have pin := (pins.2.1 true)
  have row := (Boundary.seedState_rows S G d order position copies table geom).1
  have bounds := plan.frozenLeaf_bankCap G order position W tag sites edges ports table x
  have geo := compiled_terminalFieldReads actual axes d (compiled) seed₀ row key seeds number mass old₀ room
    bounds count cellNumber vf cf hg short pw q route₁ ext₁ input₁ pins.1 pin
  have capPort : ((fan S)^T)*tiles = portCapacity S V T := by
    rw [seedPortCount (D:=D) d]
    simpa only [Parallel.nestedCapacity,pow_zero,one_mul] using (path_count (np:=V) S T 0).symm
  have one : 1 < 2^w := by
    have copiesPos : 0 < copies := Nat.pos_of_ne_zero (fun h => by rw [h,Nat.mul_zero] at count; omega)
    exact (show 1 ≤ copies*g₁ from Nat.mul_pos copiesPos hg).trans_lt pw
  have earlier : (fun z => saved₁ (.inr z)) = (Retained.Terminal.history epochFormat).eval input₁ := by
    exact funext (Retained.Terminal.saved_history_read epochFormat input₁)
  have savedWidth (i : Fin (boundaryShape S (d+1) T).sites) (b : Bool) (j : Fin w) :
      saved₁ (.inl (.inr (i,b,j))) = (Retained.Terminal.width epochFormat b).eval input₁ (i,j) :=
    Retained.Terminal.saved_width_read epochFormat input₁ i b j
  have idEq : (((s₁).rows.site.trans (F₀).sites).trans Fin.valEmbedding) = (s₁).rows.site.trans Fin.valEmbedding :=
    DFunLike.ext _ _ fun _ => rfl
  have image := Grid.staged_terminal_joint_image actual Fintype.card_pos count N₀ h₁ hg short F₀ (attachedName offs copies)
    FinalTies.routePresent epochFormat (s₁).rows.site (s₁).rows.edge oldPort prior₁ source₁ input₁ saved₁ geo.2.zero capPort
    (castGroupPort_val (S:=S) (seedPortCount (D:=D) d) T) geo.2.before geo.2.after geo.2.occupied (by rw [earlier,idEq]; exact pins.2.2)
    (fun v b => (congrArg ParseBatchSort.value (funext (savedWidth ((s₁).rows.site v) b))).trans ((pins.2.1 b).live v)) geo.2.stagedRoom one
  rw [idEq] at image
  refine ⟨image,?_,?_,FinalTies.grouped_port_present p₁⟩
  · let runs := fun v => intervals ((sewnRead N₀ lane₁ (h₁).bundle (fun _ : FreeBlock R tiles => g₁)
      (freeLane hg (gridRoom actual Fintype.card_pos)) (h₁).groupOwner ((h₁).groupAligned hg (gridRoom actual Fintype.card_pos))
      (s₁).rows.edge oldPort edge₁ port₁ v) ∘ Fin.cast (prior₁ v).size)
    have after := staged_represents F₁ source₁ finalN (s₁).rows.site edge₁ port₁ cells₁ (fun v => (prior₁ v).program)
      runs input₁ geo.1 geo.2.stagedRoom
    have zero := staged_constant F₁ source₁ input₁ false
    exact widened_represents (stagedFields F₁) finalN cells₁ _ (s₁).rows.site edge₁ port₁ extend (.inr false)
      ((source₂).eval input₁) (zero.trans geo.2.zero) after
  · intro i
    rw [staged_old]
    exact merged_mask p₁ hp₁ (s₁).rows.edge FinalTies.routePresent
      (boundFrame (factorEnum D) cellNumber cf route₁ ext₁) input₁ geo.2.occupied i

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
