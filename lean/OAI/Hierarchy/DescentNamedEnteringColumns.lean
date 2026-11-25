import OAI.Hierarchy.DescentNamedLeafCoordinates
import OAI.Hierarchy.DescentNamedTerminalLeaf
import OAI.Hierarchy.DescentTerminalBranchInputs

namespace OAI
/-! # Actual reached records used by the fixed native terminal leaf -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentTerminalEmitter DescentTerminalEmitter.Branch DescentTerminalChipRuntime
open DescentTerminalVertexFields DescentTerminalHeaderScatter DescentTerminalSiteShelves
open DescentTerminalScalarTransposes DescentTerminalDenseWindow DescentTerminalRecipeRows
open DescentTerminalScalarPadded DescentTerminalCompiledPrefix DescentEpochTagKeys
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 600000
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<W*piece) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
variable (c : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice)
local notation "b" => issued X G S ordinary reset branch positive room shorten c
local notation "world" => (last).state c
local notation "net" => (world).graph
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "U" => Label G s Z rot
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => S.epochPower^S.localTokenExponent
local notation "venues" => S.groupCount S.length*2^k
local notation "palette" => Palette.relabel X G S ordinary reset branch positive room shorten c
local notation "sh" => Palette.leafShape X G S ordinary reset branch positive room shorten c
local notation "archive" => Branch.archive X G S b positive

variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
variable (age : 0<S.height) (wFit : NativeBranch.binLimit (k:=k) S ≤ W)
  (qFit : NativeBranch.localLimit G S ≤ q) (qh : 0<q)
local notation "ord" => Branch.leafOrder X G S b positive base width
local notation "seedOne" => (Nat.le_max_left 1 (max reset.bitsR (C*reset.bitsR)))

variable (cfg : DescentTerminalCompiledPrefix.Shape)
    (pool : terminalPool X G S (W*piece) q W n h C f g ≤ cfg.terminal.pool)
    (raw : terminalRawRows X G S (W*piece) q n h C f g ≤ cfg.terminal.plane.rawRows)
local notation "leaf" => normalizedLeaf X G S ordinary reset branch positive room shorten c
  base width age wFit qFit qh cfg pool raw
local notation "groupsAt" => S.groupCount S.length
local notation "hostGraph" => (world).graph
local notation "sites" => (ord).site
local notation "arityCap" => Branch.leaf_arity X G S b positive base width qFit
local notation "box" => Branch.leaf_local_room X G S b positive base width
local notation "rowNames" => Branch.leaf_name X G S b positive base width
local notation "argNames" => Branch.leaf_arg X G S b positive base width
variable {arity groups stride oldTags K B bw : ℕ} (old : DescentEpochTagKeys.Codec (Label G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) oldTags)
variable (abi : DescentTerminalCompiledPrefix.Layout) (ms : MaskedShelf (2^k)) (meter : Memory bw)
variable (banks : Banks) (pay : RowBit cfg.terminal.plane.rawRows (q*(W*piece)) → Bool)
    (outer : Ports (fun _ : Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width)) => S.firstWidth G.b (W*piece)*1))
variable (size : cfg.terminal.pool=K*W)
local notation "T" => DescentBundleTagKeys.capacity oldTags arity groups p stride
variable (sheet : (S.groupCount S.length*2^k) * DescentTerminalVertexFields.span q
    (DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride)
    (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))
    (S.epochPower^S.localTokenExponent)
    (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (W*piece) ≤ B)
local notation "S₀" => cfg.terminal
local notation "E₀" => abi.emit
local notation "D₀" => abi.directory
local notation "sockets" => Suffix.sockets cfg abi meter
local notation "actualMem" => DescentTerminalEmitter.issued cfg.terminal (E₀) (D₀) (maskedMem ms (D₀) (S.hostSize S.length) sockets)
local notation "rsite" => fun v => (((leaf).shape v).recipe positive).restricted
local notation "bookCode" => DescentBundleTagKeys.codec old arity groups p stride
local notation "recipes" => DescentTerminalBundleRows.recipes ord rsite positive (leaf).birth (bookCode).store
local notation "ranks" => DescentTerminalChronologicalChip.charts (arity:=arity) (groups:=groups) (stride:=stride)
  hostGraph (leaf).home (leaf).native (leaf).external (leaf).nodes (leaf).ops
  (leaf).bit (leaf).shape positive (leaf).birth (leaf).hidden old
local notation "hH" => fun i v => (DescentTerminalRestrictedRows.hidden_bound (leaf).bit (leaf).shape
  positive ((ord).node i v)).trans ((leaf).countsFit ((ord).node i v))
local notation "hN" => fun i v => (leaf).atoms ((ord).node i v)
local notation "hA" => fun i v u => (((leaf).shape ((ord).node i v)).recipe_refs positive u).symm ▸
  (leaf).refs ((ord).node i v) u

/-- The original calendar chooses the identity of the raw resident. The prefix ROM
and its socket scatter read its primitive record at that exact address. The two
subsequent stable sorts then supply the rows for chip inputs and its local routes. -/
def normalized_entering (retained : j ≤ S.groupWidth k tail S.length+k)
    (occ : ∀ i c', blankAt (measured ms sockets (q:=q) (t:=T) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔ ∃ u, (b).target.chart ord rfl i u = c')
    (previous : ∀ i v, PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranks i)
      (hH i) (hN i) (hA i) v (venueField (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
        (cellAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
        (measured ms sockets (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) i)
        ((b).target.rawResident ord rfl i v))))
    (shared : MountedMask (groups:=groupsAt) ms sockets sheet)
    (acquired : Controls (B:=B) (n:=cfg.terminal.pool) abi.directory sockets sites (leaf).fit
      (fun i => DescentTerminalSiteShelves.actual (w:=p) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
        (fun _ _ => le_refl p) ((leaf).vertsFit i) (arityCap i)))
    (printedPorts : ControlColumns (S₀) (E₀) actualMem hostGraph (leaf).home (leaf).native
      (leaf).external (leaf).nodes (leaf).ops rsite positive (leaf).birth (leaf).wp qh
      ((leaf).binsFit cfg size) banks)
    (cables : SourceRows (W:=W) (q:=q) (piece:=piece) (S₀) (E₀) actualMem (leaf).external pay outer banks)
    (routes : DescentTerminalRouteIssue.Reads (K:=K) (W:=W) (q:=q) (a:=Nat.clog 2 (W*2^DescentTerminalLocalPortBook.nameBits 4 (venues*NativeBranch.localLimit G S))) (E₀).route
      (DescentTerminalLocalPortBook.rows (K₀:=K) (q:=q) sites (leaf).wp box rowNames argNames) (DescentTerminalEmitter.named (S₀) (E₀) actualMem)) :
    (leaf).Entering cfg (arity:=arity) (groups:=groups) (stride:=stride) old abi ms meter
      banks pay outer size sheet where
  clustered := Branch.leaf_clustered X G S b positive base width retained
  short := arityCap
  homeId := Branch.leaf_home X G S b positive base width
  ranking := Branch.leaf_ranking X G S b positive base width
  occupied := occ
  previous := previous
  shared := shared
  controls := acquired
  ports := printedPorts
  cables := cables
  VG := 4
  VV := venues
  VM := venues*NativeBranch.localLimit G S
  VA := NativeBranch.localLimit G S
  nameBits := DescentTerminalLocalPortBook.nameBits 4 (venues * NativeBranch.localLimit G S)
  localFit := box
  names := rowNames
  args := argNames
  matchNames := Branch.leaf_arg_matches X G S b positive base width
  routeColumns := routes

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
