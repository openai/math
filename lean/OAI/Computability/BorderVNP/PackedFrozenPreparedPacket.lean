import OAI.Computability.BorderVNP.PackedFrozenChosenOperandBounds
import OAI.Computability.BorderVNP.FiniteEvaluatorReturnedTerminalOperands
import OAI.Computability.BorderVNP.DiagonalFrozenPacketNumerals
import OAI.Computability.BorderVNP.FiniteEvaluatorDescriptorOrder
import OAI.Computability.BorderVNP.PackedFrozenPacketDirectories
import OAI.Computability.BorderVNP.CellPacketGeometryPhysicalRanks
import OAI.Computability.BorderVNP.PackedFrozenSignedPacketGeometry
import OAI.Computability.BorderVNP.PackedFrozenSignedBoxResolution
import OAI.Computability.BorderVNP.CellPacketGeometryProfileReturn
import OAI.Computability.BorderVNP.PackedFrozenSignedEmitter
import OAI.Computability.BorderVNP.PackedTerminalDirectStagedCost

/-! # Public packet publication on the actual frozen signed seed and its own native code -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Shortening.PreparedBins
open Packing.PhysicalEpochs
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales VPVNP.VerifierNetwork
open TerminalCells FieldExport GridHosts Diagonal.ExternalSew.RowTrace Packing.CellAddressCircuit Packing.SewnField
open scoped Classical BorderVNP.Epoch.Cube
open CellPacketGeometry CellPacketGeometry.History CellPacketGeometry.History.Native CellPacketGeometry.LiveWords
open Packing.CellAddresses Packing.CellAddressPhysical Packing.RoutingOutputs CellSparse.Packet SiteWords
set_option quotPrecheck false
open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator ParseBatchSort
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
local notation3 (prettyPrint := false) "a₀" => Boundary.seedState S G d order position copies table geom
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
open private select_id from OAI.Computability.BorderVNP.PackedTerminalDirectStagedCost

variable (dir : Directory.Layout) (sitePos : 0 < (boundaryShape S (d+1) T).sites)
    (cellPos : 0 < cells) (ownerFits : k ≤ packetWidth)
local notation "H₁" => boundaryShape S (d+1) T
local notation "J₁" => (fan S)^T*tiles
local notation "live₁" => (R+1)*tiles
local notation "actualShape" => (⟨(H₁).sites,(H₁).edges+(p₁).slots⟩ : Shape)
local notation3 (prettyPrint := false) "publicDir" => {dir with sites := tiles, entries := J₁}
local notation3 (prettyPrint := false) "boxes₁" => scheduledBoxes publicDir rfl number sitePos
local notation3 (prettyPrint := false) "old₁" => (originalPins sitePos offs : Fin J₁ → Fin (H₁).sites)
local notation3 (prettyPrint := false) "roles₁" => (⟨(s₁).rows.site,edge₁⟩ : Rows actualShape finalN)
local notation3 (prettyPrint := false) "channels" => (groupedGridRows G axes d order position copies).edge
local notation "groups" => Equiv.toEmbedding (Equiv.refl (Fin tiles))
local notation3 (prettyPrint := false) "body₁" => fun j : Fin J₁ => W.seedStored position tag sites edges ports channels groups
  (order (finProdFinEquiv.symm j).2)
local notation3 (prettyPrint := false) "occupied₁" => fun i => oldWire (FinalTies.sewnPresent p₁ FinalTies.routePresent i)
local notation3 (prettyPrint := false) "keep₁" => Retained.Terminal.saved (X := σ) (reserve := reserve) epochFormat

variable {qbits tagCap control : ℕ} (arena stride gap desc gadgets digits : ℕ)
    (controls : Fin control → Fin (2^packetWidth))
local notation3 (prettyPrint := false) "final₁" => FinalTies.tieSchema ((H₁).edges+(p₁).slots) live₁ packetWidth
local notation3 (prettyPrint := false) "priv₁" => FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J₁)
local notation3 (prettyPrint := false) "reports₁" => FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J₁)
local notation3 (prettyPrint := false) "signed₁" => SignedFields.liveFrame F₂ boxes₁ old₁ arena stride gap desc gadgets digits
local notation3 (prettyPrint := false) "feeds₁" => Terminal.feeds (s:=actualShape) F₂ occupied₁ (fun _ => true) boxes₁ hist₁ signed₁ (.inr true)
variable (hs : ∀ j, (((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))).tags j).length≤tagCap) (hf : ∀ j, ((FinalTies.tieSchema ((boundaryShape S (d+1) T).edges+4*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) packetWidth).tags j).length≤tagCap)
    (keyFits : 60*logWidth r n≤qbits) (sitesFit : (boundaryShape S (d+1) T).sites<2^qbits)
    (keysFit : cells+1<2^k) (sw : ∀ j, ((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))).width j≤packetWidth)
local notation3 (prettyPrint := false) "tpl₁" => template scp final₁ boxes₁ hs hf priv₁ reports₁
local notation3 (prettyPrint := false) "ptr₁" => (fun i : Fin J₁ => Sum.inl (Sum.inr i) : Fin J₁ → (tpl₁).Fields)
variable (pad : (roster (boundaryShape S (d+1) T).sites ((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))) (FinalTies.tieSchema ((boundaryShape S (d+1) T).edges+4*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) packetWidth)).length<2^qbits)
    (dest hdr : ℕ)
local notation3 (prettyPrint := false) "at₁" => Retained.packetBase dest ((H₁).edges+(p₁).slots) cells J₁ live₁ control
local notation3 (prettyPrint := false) "packet₁" => (feeds₁).ordered scp final₁ boxes₁ hs hf priv₁ reports₁ keyFits keyFits sitesFit
  (Nat.lt_trans (Nat.lt_succ_self cells) keysFit) sw (fun _ => le_rfl) (fun _ => Fin.last cells) ptr₁ pad at₁ hdr
local notation3 (prettyPrint := false) "out₁" => frozenPacketEmitter (reserve := reserve) S G order position σ actual
  count cellNumber vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits controls
  hs hf keyFits sitesFit keysFit sw pad dest hdr
local notation3 (prettyPrint := false) "read₁" => Sum.elim ((source₂).eval input₁) saved₁
local notation3 (prettyPrint := false) "cell₁" => TerminalTable.cell F₂ cellPos ((source₂).eval input₁)
local notation3 (prettyPrint := false) "bit₁" => TerminalTable.bitStart F₂ ((source₂).eval input₁)
local notation3 (prettyPrint := false) "box₁" => TerminalTable.boxStart F₂ boxes₁ cellPos ((source₂).eval input₁)
local notation3 (prettyPrint := false) "args₁" => (feeds₁).arguments read₁
local notation3 (prettyPrint := false) "directory₁" => directory scp final₁ boxes₁ hs hf priv₁ reports₁
  args₁ ((hist₁).eval read₁) ((feeds₁).binding.eval read₁) cell₁ bit₁ box₁
local notation3 (prettyPrint := false) "field₁" => fun (i : Fin (roster (H₁).sites scp final₁).length) =>
  scalarArgs (cap := tagCap) scp final₁ ((hist₁).eval read₁) ((feeds₁).binding.eval read₁) bit₁ box₁ ((roster (H₁).sites scp final₁).get i)

/-- Complete contents of the selected signed geometry output, expressed
with the natural control words of its installed task and the exact
interpreter directory at every real placed cell. -/
def FrozenPreparedImage (controlWords : Fin control → ℕ) (ram : ℕ → ℕ) : Prop :=
    Image F₂ old₁ id ((source₂).eval input₁) dest ram ∧
      (∀ i : Fin control, ram (controlsBase dest ((H₁).edges+(p₁).slots) cells J₁ live₁+i.val)=controlWords i) ∧
      Published directory₁ (tpl₁).publicDepth (tpl₁).chunkDepth at₁ hdr ptr₁ ((tpl₁).arguments args₁ field₁) ram ∧
      ∀ c : Fin cells,
        ((directory₁).privateWires c.castSucc = FinalCell.privateBits finalN (fun v => (cells₁ v).val) (fun v => (rawState v).program) c.val ∧
         (directory₁).reports c.castSucc = DiagonalTallyCellReports.countFields
           (FinalCell.countBase finalN (fun v => (cells₁ v).val) (fun v => (rawState v).program) c.val) gadgets digits) ∧
        ∀ slot pb db eb scratch burst bytes,
          ((directory₁).placed c.castSucc hdr slot body₁ pb db eb scratch burst bytes).directory =
            FinalCell.directory (fun i => (cell₁ i).val) finalN (fun v => (cells₁ v).val) (s₁).rows.site edge₁ port₁
              (fun v => (rawState v).program) c.val ((directory₁).reports c.castSucc)

include pw room hook in
/-- The original private-bit count and every reported count address can be
read on the frozen public geometry alone, before any team's guessed pin or
opaque description is evaluated. -/
theorem frozen_private_extent
    (sizeFit : ∀ c, guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)
      +suppliedSize finalN cells₁ c < 2^packetWidth)
    (c : Fin cells)
    (countRoom : guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)
      +suppliedSize finalN cells₁ c+gadgets*digits ≤ 2^packetWidth) :
    (directory₁).privateWires c.castSucc = externalBase finalN cells₁ c (fun v => (rawState v).program.size) ∧
      (directory₁).reports c.castSucc = DiagonalTallyCellReports.countFields
        (FinalCell.countBase finalN (fun v => (cells₁ v).val) (fun v => (rawState v).program) c.val) gadgets digits := by
  have physical := (plan.frozen_signed_packet_geometry G order position W tag sites edges ports table x wr hm seeds number
    widths ord fit actual count cellNumber vf cf hg short pw extend room hook q).2.1
  have observed := SignedFields.directory_real (a := (H₁).sites) (m := (H₁).edges+(p₁).slots) (n := live₁)
    (C := cells) (d := w) (k := k) («w» := packetWidth) (entries := J₁) F₂ boxes₁ old₁ arena stride gap desc gadgets digits ((source₂).eval input₁)
    saved₁ scp final₁ hs hf ((hist₁).eval read₁) ((feeds₁).binding.eval read₁) cell₁ bit₁ box₁ finalN cells₁
    (fun v => (rawState v).program) (s₁).rows.site edge₁ port₁ physical sizeFit c countRoom
  have same := FinalReports.bank_sizes finalN cells₁ (fun v => (rawState v).program) c
  exact ⟨observed.1.trans (congrArg₂ Nat.add same.1 same.2.1), observed.2⟩

include pw room hook in
/-- A returning path on the real code of this public history, with the joint
word of every team, yields the exact signed directory and all scalar-address
and report fields on the chosen packet. The opaque data are the actual
protected verifier factors on the named original tile of each source key. -/
theorem frozen_prepared_packet
    (sizeFit : ∀ c, guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)
      +suppliedSize finalN cells₁ c < 2^packetWidth)
    (countRoom : ∀ c, guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)
      +suppliedSize finalN cells₁ c+gadgets*digits ≤ 2^packetWidth)
    (wide : 2^(tpl₁).recordDepth≤2^(packetWidth+k))
    (boxRoom : (∑ i, (boxes₁ i).length)<2^packetWidth)
    (rowRoom : (scp).rows.length+(final₁).rows.length<2^packetWidth)
    (capRoom : tagCap<2^packetWidth) (three : 3<2^packetWidth)
    (known : ∀ i t, t∈boxWords (boxes₁ i) → t<2^packetWidth)
    (reportRows : ∀ c, (reports₁ c).length<2^packetWidth)
    (vectors : ∀ c r, r∈reports₁ c → r.length<2^packetWidth)
    (limit : Fin cells → ℕ) (limitRoom : ∀ c, limit c<2^packetWidth)
    (bounds : ∀ c : Fin cells, ∀ r ∈ (FinalCell.directory (fun i => (cell₁ i).val) finalN (fun v => (cells₁ v).val)
      (s₁).rows.site edge₁ port₁ (fun v => (rawState v).program) c.val ((directory₁).reports c.castSucc)).records,
      RecordFields r (limit c))
    (bufferRoom : at₁+2^(tpl₁).publicDepth<2^packetWidth) (descRoom : 2^(tpl₁).chunkDepth≤2^packetWidth) (headerRoom : hdr<2^packetWidth)
    {code : Code} {guess time hw : ℕ} {ok : Prop} {pub : Arg → Word hw} {mac : TeamOpcode.Macros hw 8}
    {bank : RoutingISA.Bank hw} {mem : Memory hw} {resident : (Fin guess → Bool) → Memory hw → Prop} (wfit : packetWidth≤hw)
    (paths : ProfilePaths code guess pub mac bank mem ok time dest (emittedWords aug (broadcastOrder (fan S) widths ord T)
      fit out₁ x code₁) resident)
    (run : Returns code pub mac bank mem) :
    let ram := readings run.val.2.2
    Image F₂ old₁ id ((source₂).eval input₁) dest ram ∧
      (∀ i : Fin control, ram (controlsBase dest ((H₁).edges+(p₁).slots) cells J₁ live₁+i.val)=(controls i).val) ∧
      Published directory₁ (tpl₁).publicDepth (tpl₁).chunkDepth at₁ hdr ptr₁ ((tpl₁).arguments args₁ field₁) ram ∧
      ∀ c : Fin cells,
        ((directory₁).privateWires c.castSucc = FinalCell.privateBits finalN (fun v => (cells₁ v).val) (fun v => (rawState v).program) c.val ∧
         (directory₁).reports c.castSucc = DiagonalTallyCellReports.countFields
           (FinalCell.countBase finalN (fun v => (cells₁ v).val) (fun v => (rawState v).program) c.val) gadgets digits) ∧
        ∀ slot pb db eb scratch burst bytes,
          ((directory₁).placed c.castSucc hdr slot body₁ pb db eb scratch burst bytes).directory =
            FinalCell.directory (fun i => (cell₁ i).val) finalN (fun v => (cells₁ v).val) (s₁).rows.site edge₁ port₁
              (fun v => (rawState v).program) c.val ((directory₁).reports c.castSucc) := by
  intro ram
  obtain ⟨historical,physical,occupied,used⟩ := plan.frozen_signed_packet_geometry G order position W tag sites edges ports
    table x wr hm seeds number widths ord fit actual count cellNumber vf cf hg short pw extend room hook q
  have resolved (i : Fin (H₁).sites) := plan.frozen_signed_boxes_resolved G order position W tag sites edges ports
    table x names number q dir sitePos i
  have constants (bit : Bool) : (source₂).eval input₁ (.inr bit)=bit := by
    rw [staged_constant]
    simp [withSewnFields,constants_eval]
  let direct := Retained.emitter F₂ ownerFits old₁ id (Retained.privateControls F₂ old₁ controls packet₁) source₂ keep₁
  have same : out₁ = direct := by
    simp only [frozenPacketEmitter,signedGridEmitter,frozenPrimary,select_id]
    rfl
  rw [same] at paths
  have observed := Terminal.prepared_packet (s := actualShape) (n := live₁) (C := cells) (d := w) (k := k)
    («w» := packetWidth) (t := w) (J := J₁) (P := live₁) (cap := tagCap) (q := qbits) (control := control) F₂ occupied₁ (fun _ => true) boxes₁ hist₁ signed₁ (.inr true)
    scp hs hf priv₁ reports₁ sw keyFits keyFits sitesFit keysFit (fun _ => Fin.last cells) ptr₁ pad hdr
    ownerFits old₁ id controls source₂ keep₁ aug (broadcastOrder (fan S) widths ord T) fit x code₁ cellPos finalN roles₁ port₁
    cells₁ (fun v => (rawState v).program) body₁ historical physical resolved sizeFit (fun v => (rawState v).size)
    (fun _ => rfl) occupied used wide boxRoom rowRoom capRoom three known reportRows vectors limit limitRoom bounds
    bufferRoom descRoom headerRoom wfit constants paths run
  refine ⟨observed.1,observed.2.2.1,observed.2.2.2.1,fun c => ⟨?_,observed.2.2.2.2 c⟩⟩
  exact SignedFields.directory_real (a := (H₁).sites) (m := (H₁).edges+(p₁).slots) (n := live₁)
    (C := cells) (d := w) (k := k) («w» := packetWidth) (entries := J₁) F₂ boxes₁ old₁ arena stride gap desc gadgets digits ((source₂).eval input₁)
    saved₁ scp final₁ hs hf ((hist₁).eval read₁) ((feeds₁).binding.eval read₁) cell₁ bit₁ box₁
    finalN cells₁ (fun v => (rawState v).program) (s₁).rows.site edge₁ port₁ physical sizeFit c (countRoom c)

/-- The four contiguous physical sections read from the signed packet on
this original history. The raw private views and complete ordered packet
words are available on the very same RAM return as the controls. -/
theorem frozen_prepared_words
    {hw guess timeBound : ℕ} {code : Code} {pub : Arg → Word hw} {mac : TeamOpcode.Macros hw 8}
    {bank : RoutingISA.Bank hw} {mem : Memory hw} {ok : Prop} {resident : (Fin guess → Bool) → Memory hw → Prop}
    (wfit : packetWidth≤hw)
    (paths : ProfilePaths code guess pub mac bank mem ok timeBound dest (emittedWords aug (broadcastOrder (fan S) widths ord T)
      fit out₁ x code₁) resident) (run : Returns code pub mac bank mem) :
    let ram := readings run.val.2.2
    Image F₂ old₁ id ((source₂).eval input₁) dest ram ∧
      (∀ i : Fin (cells+(J₁+cells)), ram (dest+((H₁).edges+(p₁).slots)*3+
        Packing.RoutingOutputs.count ((H₁).edges+(p₁).slots) cells J₁ live₁+i.val) =
          value (fun j => (privateViews F₂ old₁).eval ((source₂).eval input₁) (i,j))) ∧
      (∀ i : Fin control, ram (controlsBase dest ((H₁).edges+(p₁).slots) cells J₁ live₁+i.val)=(controls i).val) ∧
      ∀ i : Fin (Total (tpl₁).publicDepth (tpl₁).chunkDepth), ram (at₁+i.val) =
        value (fun j => (packet₁).eval read₁ (.inl (i,j))) := by
  intro ram
  have constants (bit : Bool) : (source₂).eval input₁ (.inr bit)=bit := by
    rw [staged_constant]
    simp [withSewnFields,constants_eval]
  let direct := Retained.emitter F₂ ownerFits old₁ id (Retained.privateControls F₂ old₁ controls packet₁) source₂ keep₁
  have same : out₁ = direct := by
    simp only [frozenPacketEmitter,signedGridEmitter,frozenPrimary,select_id]
    rfl
  rw [same] at paths
  exact Retained.packet_image_of_words F₂ ownerFits wfit old₁ id controls packet₁ source₂ keep₁ input₁
    constants dest run.val.2.2 (paths.words_of_return run)

/-- Every returning geometry on a real profile reads the inverse descriptor
rank for each start and exclusive-stop marker. The same fixed directory gives
the exact number of chunk rows on this particular original history. -/
theorem frozen_prepared_markerBounds (fixed : control=37) (bundleBits : ℕ)
    (wide : 2^(tpl₁).chunkDepth ≤ 2^packetWidth)
    {hw guess timeBound : ℕ} {code : Code} {pub : Arg → Word hw} {mac : TeamOpcode.Macros hw 8}
    {bank : RoutingISA.Bank hw} {mem : Memory hw} {ok : Prop} {resident : (Fin guess → Bool) → Memory hw → Prop}
    (wfit : packetWidth≤hw)
    (paths : ProfilePaths code guess pub mac bank mem ok timeBound dest (emittedWords aug (broadcastOrder (fan S) widths ord T)
      fit out₁ x code₁) resident) (run : Returns code pub mac bank mem) :
    (frozenPacketDirectories tpl₁ dest ((H₁).edges+(p₁).slots) J₁ live₁ bundleBits).MarkerBounds cells (readings run.val.2.2) ∧
      ((directory₁).referenceRows ptr₁).length=(tpl₁).chunkLabels.length := by
  have output := (plan.frozen_prepared_words G order position W tag sites edges ports table x wr hm number widths ord fit actual
    count cellNumber vf cf hg short extend q dir sitePos ownerFits arena stride gap desc gadgets digits controls hs hf keyFits
    sitesFit keysFit sw pad dest hdr wfit paths run).2.2.2
  let lim := descriptorBank at₁ (tpl₁).publicDepth+2^(tpl₁).chunkDepth
  have rank := (feeds₁).descriptor_room scp final₁ boxes₁ hs hf priv₁ reports₁ keyFits keyFits sitesFit
    (Nat.lt_trans (Nat.lt_succ_self cells) keysFit) sw (fun _ => le_rfl) (fun _ => Fin.last cells) ptr₁ pad at₁ hdr
    read₁ (readings run.val.2.2) wide lim le_rfl output
  have baseEq : at₁=Retained.packetBase dest ((H₁).edges+(p₁).slots) cells J₁ live₁ 37 :=
    congrArg (Retained.packetBase dest ((H₁).edges+(p₁).slots) cells J₁ live₁) fixed
  refine ⟨frozenPacketDirectories_of_inverse tpl₁ dest ((H₁).edges+(p₁).slots) J₁ live₁ bundleBits _ ?_,?_⟩
  · intro i
    rw [← baseEq]
    exact (rank i).1
  · exact directory_reference_count scp final₁ boxes₁ hs hf priv₁ reports₁ args₁ ((hist₁).eval read₁)
      ((feeds₁).binding.eval read₁) cell₁ bit₁ box₁ ptr₁

/-- The physical inverse descriptor sort strictly separates the last marker of
each earlier cell from the first marker of every later one. The public inverse
sort and every cell, including the spare, use this same returned RAM. -/
theorem frozen_prepared_ranks
    (publicRoom : at₁+2^(tpl₁).publicDepth<2^packetWidth)
    (wide : 2^(tpl₁).chunkDepth≤2^packetWidth) (headerRoom : hdr<2^packetWidth) (one : 1<2^packetWidth)
    {hw guess timeBound : ℕ} {code : Code} {pub : Arg → Word hw} {mac : TeamOpcode.Macros hw 8}
    {bank : RoutingISA.Bank hw} {mem : Memory hw} {ok : Prop} {resident : (Fin guess → Bool) → Memory hw → Prop}
    (wfit : packetWidth≤hw)
    (paths : ProfilePaths code guess pub mac bank mem ok timeBound dest (emittedWords aug (broadcastOrder (fan S) widths ord T)
      fit out₁ x code₁) resident) (run : Returns code pub mac bank mem) :
    CellPacketGeometry.PacketRanks (cells+1) (cells+1+(CellPacketGeometry.Schema.coords (tpl₁).chunkLabels.length).length)
      (tpl₁).publicDepth (tpl₁).chunkDepth at₁ (readings run.val.2.2) := by
  have output := (plan.frozen_prepared_words G order position W tag sites edges ports table x wr hm number widths ord fit actual
    count cellNumber vf cf hg short extend q dir sitePos ownerFits arena stride gap desc gadgets digits controls hs hf keyFits
    sitesFit keysFit sw pad dest hdr wfit paths run).2.2.2
  exact (feeds₁).ordered_descriptor_ranks scp final₁ boxes₁ hs hf priv₁ reports₁ keyFits keyFits sitesFit
    keysFit sw (fun _ => le_rfl) (fun _ => Fin.last cells) ptr₁ pad at₁ hdr read₁ (readings run.val.2.2)
    publicRoom wide headerRoom one output

variable (bankLayout : CellBanks.Layout) (bundleBits : ℕ) (shapes : Fin ((fan S)^T*GridHosts.tileCount (Fintype.card (Cube D)) d) → BottomReports.BundleSort.Shape)
local notation3 (prettyPrint := false) "banks" => ({bankLayout with cells := cells} : CellBanks.Layout)
local notation3 (prettyPrint := false) "bankValid" => VPVNP.VerifierNetwork.Frame.initial (fun _ : Unit => Sum.inr true)
local notation3 (prettyPrint := false) "bankSource" => BottomReports.BundleSort.source cells bundleBits
  (BottomReports.BundleSort.geometryHeaders F₂ old₁ desc (BottomReports.BundleSort.bankConfig banks gap bankValid) shapes)
local notation3 (prettyPrint := false) "packetSize" => signedGridOutputCount ((H₁).edges+4*(R+1)*tiles) cells J₁ live₁
  control (Total (tpl₁).publicDepth (tpl₁).chunkDepth)
local notation3 (prettyPrint := false) "fullSize" => packetSize+(2^bundleBits+2^bundleBits)
local notation3 (prettyPrint := false) "fullEmit" => frozenPacketWithBundles (reserve := reserve) S G order position σ actual
  count cellNumber vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits controls hs hf
  keyFits sitesFit keysFit sw pad dest hdr bankLayout bundleBits shapes

/-- The task builder reads its two real-cell marker bounds, all descriptor
chunk positions and the two source-bundle banks from the *same* returning RAM.
The physical directory and its word addresses were selected before the profile. -/
theorem frozen_bundle_directory_return (fixed : control=37) (wide : 2^(tpl₁).chunkDepth≤2^packetWidth)
    {hw guess timeBound : ℕ} {code : Code} {pub : Arg → Word hw} {mac : TeamOpcode.Macros hw 8}
    {bank : RoutingISA.Bank hw} {mem : Memory hw} {ok : Prop} {resident : (Fin guess → Bool) → Memory hw → Prop}
    (wfit : packetWidth≤hw)
    (paths : ProfilePaths code guess pub mac bank mem ok timeBound dest (emittedWords aug (broadcastOrder (fan S) widths ord T)
      fit fullEmit x code₁) resident) (run : Returns code pub mac bank mem) :
    let dirs := frozenPacketDirectories tpl₁ dest ((H₁).edges+(p₁).slots) J₁ live₁ bundleBits
    let ram := readings run.val.2.2
    dirs.MarkerBounds cells ram ∧ ((directory₁).referenceRows ptr₁).length=(tpl₁).chunkLabels.length ∧
      ∀ i : Fin (2^bundleBits+2^bundleBits), ram (dirs.bundlePayload+i.val) =
        value (fun z => (CellPacketGeometry.geometry bankSource).eval ((source₂).eval input₁) (.inl (i,z))) := by
  intro dirs ram
  have split := ProfilePaths.split_headerBanks aug (broadcastOrder (fan S) widths ord T) fit x code₁ out₁ source₂
    banks F₂ old₁ desc gap shapes bankValid paths
  obtain ⟨ranks,refs⟩ := plan.frozen_prepared_markerBounds G order position W tag sites edges ports table x wr hm
    number widths ord fit actual count cellNumber vf cf hg short extend q dir sitePos cellPos ownerFits arena stride gap desc
    gadgets digits controls hs hf keyFits sitesFit keysFit sw pad dest hdr fixed bundleBits wide wfit split.1 run
  refine ⟨ranks,refs,fun i => ?_⟩
  have start : dirs.bundlePayload=dest+packetSize := by
    have loc := (frozenPacketDirectories_locations tpl₁ dest ((H₁).edges+(p₁).slots) J₁ live₁ bundleBits).2.2.2.1
    exact loc.trans (congrArg (fun c : ℕ => dest+signedGridOutputCount ((H₁).edges+(p₁).slots)
      cells J₁ live₁ c (Total (tpl₁).publicDepth (tpl₁).chunkDepth)) fixed.symm)
  rw [start]
  exact split.2 run i

include pw room hook in
/-- The real placed cell retains the private width and report-vector addresses
of this selected public history at its global ordinal in the deployed table. -/
theorem frozen_placed_extent
    (pl : Fin (cells+1) → RoutingISA.CellPacket.Placed (Fin J₁))
    (shape : RoutingISA.TypedBatch.SourceShape pl directory₁)
    (sizeFit : ∀ c, guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)
      +suppliedSize finalN cells₁ c < 2^packetWidth)
    (c : Fin cells)
    (countRoom : guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)
      +suppliedSize finalN cells₁ c+gadgets*digits ≤ 2^packetWidth) :
    (Terminal.placeAt pl c.val).privateWires = externalBase finalN cells₁ c (fun v => (rawState v).program.size) ∧
      (Terminal.placeAt pl c.val).reports = DiagonalTallyCellReports.countFields
        (FinalCell.countBase finalN (fun v => (cells₁ v).val) (fun v => (rawState v).program) c.val) gadgets digits := by
  have actual : (directory₁).privateWires c.castSucc = externalBase finalN cells₁ c (fun v => (rawState v).program.size) ∧
      (directory₁).reports c.castSucc = DiagonalTallyCellReports.countFields
        (FinalCell.countBase finalN (fun v => (cells₁ v).val) (fun v => (rawState v).program) c.val) gadgets digits := by
    apply frozen_private_extent <;> assumption
  have ordinal : Terminal.placeAt pl c.val=pl c.castSucc :=
    congrArg pl (Fin.ext (Nat.min_eq_left c.isLt.le))
  rw [ordinal,shape.privateWires,shape.reports]
  exact actual

local notation "loaded₁" => S.publicProgramFactor^T*initialMass (D:=D) n r d copies headerFactor
local notation "birth₁" => max 2 (max copies (seedBoxCapacity n r axes d (Fintype.card (Direction axes))))
local notation "coefficient₁" => (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
local notation "scalar₁" => max (15*loaded₁) (H₁).sites +
    max (max birth₁ (coefficient₁*(loaded₁+1))) (max 1 (15*loaded₁))+1
local notation3 (prettyPrint := false) "stack₁" => fun c =>
  guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)+suppliedSize finalN cells₁ c
local notation3 (prettyPrint := false) "output₁" depth => signedGridOutputCount ((H₁).edges+(p₁).slots) cells J₁ live₁ 37
  (Total (tpl₁).publicDepth (tpl₁).chunkDepth) + (2^depth+2^depth)

include pw room hook in
/-- All numerical premises of the returning signed-packet theorem for the
installed seed. The scalar and row certificates are chosen on the schedule;
the address check is the stop of the complete native allocation. -/
theorem frozen_packet_operands {H E A : ℕ}
    (digitsChoice : digits=packetWidth) (capChoice : tagCap=ProgramSchemas.signedTagCapacity (e:=e))
    (controlChoice : control=37)
    (input : Diagonal.SignedPacketInputBounds S (d+1) T cells live₁ w packetWidth H E A gadgets fmt publicDir rfl number)
    (numbers : Diagonal.FrozenPacketNumerals e number gadgets hdr packetWidth scalar₁ loaded₁)
    (installed : (seed₀).val.pack.layout = (wiredGrid actual axes d order position).groupedRepeat
      (fun _ : Fin tiles => GridHosts.inputBlockWidth r n axes d) order copies)
    (fresh gates bundleBits : ℕ)
    (destination : GeometryAdvice.Allocation.dest fresh reserve gates (output₁ bundleBits) packetWidth=dest)
    (address : GeometryAdvice.Allocation.stop fresh reserve gates (output₁ bundleBits) packetWidth packetWidth<2^packetWidth) :
    (∀ c, stack₁ c < 2^packetWidth) ∧ (∀ c, stack₁ c+gadgets*digits ≤ 2^packetWidth) ∧
    2^(tpl₁).recordDepth ≤ 2^(packetWidth+k) ∧ (∑ i, (boxes₁ i).length)<2^packetWidth ∧
    (scp).rows.length+(final₁).rows.length<2^packetWidth ∧ tagCap<2^packetWidth ∧ 3<2^packetWidth ∧
    (∀ i t, t∈boxWords (boxes₁ i) → t<2^packetWidth) ∧
    (∀ c, (reports₁ c).length<2^packetWidth) ∧ (∀ c r, r∈reports₁ c → r.length<2^packetWidth) ∧
    ∃ limit : Fin cells → ℕ, (∀ c, limit c<2^packetWidth) ∧
    (∀ c : Fin cells, ∀ row ∈ (FinalCell.directory (fun i => (cell₁ i).val) finalN (fun v => (cells₁ v).val)
      (s₁).rows.site edge₁ port₁ (fun v => (rawState v).program) c.val ((directory₁).reports c.castSucc)).records,
      RecordFields row (limit c)) ∧
    at₁+2^(tpl₁).publicDepth < 2^packetWidth ∧ 2^(tpl₁).chunkDepth≤2^packetWidth ∧ hdr<2^packetWidth := by
  subst digits tagCap control
  have fragments : 2*(H₁).edges+6*(R+1)*tiles=2*(H₁).edges+6*live₁ := by rw [Nat.mul_assoc 6]
  have cables : (H₁).edges+(p₁).slots=(H₁).edges+4*live₁ := by
    change (H₁).edges+4*(R+1)*tiles=(H₁).edges+4*live₁
    rw [Nat.mul_assoc 4]
  obtain ⟨depth,boxes,rows,cap,three,words,reports,vectors,addresses⟩ :=
    input.emitter_words numbers sitePos _ _ fragments cables hs hf
  have loc := addresses fresh reserve gates bundleBits address
  rw [destination] at loc
  obtain ⟨sizes,counts,limit,limits,bounds⟩ := plan.frozen_chosen_operand_bounds G order position W tag sites edges ports
    table x wr hm seeds number widths ord fit actual count cellNumber vf cf hg short pw extend room hook q dir sitePos cellPos
    gadgets packetWidth le_rfl installed numbers.operands numbers.counts
  exact ⟨sizes,counts,Nat.pow_le_pow_right (by decide) (depth.trans (Nat.le_add_right ..)),boxes,rows,cap,three,words,
    reports,vectors,limit,limits,(fun c => bounds c _),loc⟩

include pw room hook in
/-- Reindex the attained private bank of the emitted directory by the
original network's extents. The inverse leaves every submitted cell's
ordered private bit string unchanged. -/
theorem frozen_submitted_bank {Private : Type}
    (bank : Private ≃ ((c : Fin cells) → Fin ((directory₁).privateWires c.castSucc) → Bool))
    (read : Private → Fin cells → List Bool)
    (original : ∀ bits c, read (bank.symm bits) c=List.ofFn (bits c))
    (sizeFit : ∀ c, guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)
      +suppliedSize finalN cells₁ c < 2^packetWidth)
    (countRoom : ∀ c, guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)
      +suppliedSize finalN cells₁ c+gadgets*digits ≤ 2^packetWidth) :
    ∃ E : Private ≃ ((c : Fin cells) → Fin (externalBase finalN cells₁ c (fun v => (rawState v).program.size)) → Bool),
      ∀ bits c, read (E.symm bits) c=List.ofFn (bits c) := by
  have same (c : Fin cells) : (directory₁).privateWires c.castSucc = externalBase finalN cells₁ c (fun v => (rawState v).program.size) := by
    have actual : (directory₁).privateWires c.castSucc = externalBase finalN cells₁ c (fun v => (rawState v).program.size) ∧
        (directory₁).reports c.castSucc = DiagonalTallyCellReports.countFields
          (FinalCell.countBase finalN (fun v => (cells₁ v).val) (fun v => (rawState v).program) c.val) gadgets digits := by
      apply frozen_private_extent <;> first | assumption | exact countRoom c
    exact actual.1
  let reindex := Equiv.piCongrRight fun c : Fin cells => Equiv.arrowCongr (finCongr (same c)) (Equiv.refl Bool)
  refine ⟨bank.trans reindex,?_⟩
  intro bits c
  change read (bank.symm (reindex.symm bits)) c=_
  rw [original]
  have eqBits {i j : ℕ} (h : i=j) (v : Fin j → Bool) :
      List.ofFn (fun k => v (Fin.cast h k))=List.ofFn v := by
    subst j
    rfl
  exact eqBits (same c) (bits c)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
