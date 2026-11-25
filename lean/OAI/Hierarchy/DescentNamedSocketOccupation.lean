import OAI.Hierarchy.DescentNamedPurchasedSockets
import OAI.Hierarchy.DescentTerminalSocketOccupation

namespace OAI
/-! # Complete reached-venue chart at the dated physical socket memory -/
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
set_option maxHeartbeats 1300000
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape

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

open DescentTerminalPrimitiveArena DescentTerminalPointerDigits DescentTerminalPointerIssue
open DescentOperandStateBanks DescentSharedCableNames DescentLocalPrivateNames DescentTerminalPortChart DescentColonies
open DescentSIMDLookup DescentTerminalChronologicalBooks
open ThreeFlat.Routing
open scoped Fin.CommRing
local notation "T" => DescentBundleTagKeys.capacity oldTags arity groups p stride
variable (sheet : (S.groupCount S.length*2^k) * DescentTerminalVertexFields.span q
    (DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride)
    (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))
    (S.epochPower^S.localTokenExponent)
    (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (W*piece) ≤ B)
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


local notation "A" => (b).target.placement
local notation "hosts" => S.hostSize S.length
local notation "blocks" => 2^k
local notation "native" => (b).target.order.trans Fin.valEmbedding
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groupsAt)) ((b).target.vertex.trans Fin.valEmbedding))
local notation "pinRank" => fun v=>(Branch.densePinEquiv X G S b positive base v).toEmbedding.trans Fin.valEmbedding
local notation "aliases" => Branch.privateSlot X G S b positive seedOne age branch
local notation "psize" => poolBatchCount (s*1) p
local notation "atNode" i:arg z:arg => (ord).node i z
local notation "blk" i:arg z:arg => (A).block (atNode i z)
local notation "grp" i:arg z:arg => ((A).pos (atNode i z)).1

variable {d0 : ℕ} (config : Widths) (index : ℕ→ℕ→ℕ→ℕ) (scale frozenBits : ℕ)
    (whole : (issued X G S ordinary reset branch positive room shorten c).target.placement.z*G.b=scale*(W*piece))
    (pages : Gather.Pages (2^k) (issued X G S ordinary reset branch positive room shorten c).target.placement.cap
      (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))))
    (initial original : Memory bw) (rawRoles : Fin 6→Bank) (advice start pop maskBase : ℕ)
    (actors : Fin (2^k)→Bank)
local notation "wholeBits" => groupsAt*span q T cap nodeCap cap p
local notation "arena" => DescentTerminalPrimitiveArena.actual blocks hosts (A).cap nodeCap cap d0 wholeBits
local notation "bits6" => fun f:Fin 6=>DescentTerminalCombinedRole.width oldTags arity groups p stride f*nodeCap*groupsAt
local notation "first" => DescentTerminalRoleTables.role bits6 rawRoles advice
local notation "second" => DescentTerminalRoleTables.arity bits6 rawRoles advice
local notation "warm" => DescentTerminalCombinedRole.memory first second start (arena).rows initial
local notation "chan" => (arena).channels start pop actors
local notation "ms" => MaskAllocation.shelf (q:=q) (t:=T) (H:=cap) (N:=nodeCap) («A»:=cap) («p»:=p) (groups:=groupsAt) chan maskBase
local notation "f0" => publicCell («cap»:=(A).cap) (N:=nodeCap) («A»:=cap) (d:=d0) (A).degree q scale psize frozenBits groupsAt config
local notation "f7" => DescentTerminalPointerDigits.output (A).cap nodeCap cap (A).degree groupsAt d0
  (Nat.clog 2 (q+cap+1)) q scale psize config index
local notation "after" => DescentTerminalPrimitiveArena.image (n:=oldTags) (a:=arity) (g:=groups) («p»:=p) (r:=stride)
  (N:=nodeCap) (groups:=groupsAt) (shops:=hosts) (dc:=wholeBits) rawRoles advice start pop pages f0 f7 q cap initial
local notation "vfmt" => (⟨q,T,cap,nodeCap,cap,p,groupsAt⟩ : Home.Format)
variable (I : AddressPlan.Input) (header : ℕ) (literal : DescentTerminalEmitter.Compact.Literals I.sources)
local notation "next" => AddressPlan.afterMeter vfmt cfg chan maskBase
local notation "regs" => AddressPlan.registers vfmt cfg chan maskBase header
local notation "abi" => AddressPlan.layout cfg I next regs
local notation "sockets" => Suffix.sockets cfg abi ((AddressPlan.rowArena cfg I next).mount
  (AddressPlan.input vfmt cfg I chan maskBase header sheet literal after))
local notation "cell" i:arg z:arg => pages.source (N:=nodeCap) (d:=d0) warm (blk i z) i
local notation "roleData" => DescentTerminalCombinedRole.observed (n:=oldTags) («A»:=arity) (G:=groups)
  («p»:=p) («R»:=stride) (N:=nodeCap) (M:=groupsAt)
local notation "rk" i:arg z:arg => rank A native S (b).target.valid names (atNode i z) (pinRank (atNode i z))


/-- A true occupancy word from the earlier physical census is retained by the
executed primitive issuer and then observed at the final socket. Each direction
of the occupancy criterion uses the same ranked terminal placement. -/
theorem normalized_occupied
    (bound : (arena).Prior start pop actors) (limit : (arena).finish start<2^bw)
    (inputs : ∀f,(rawRoles f).Fits bw start) (romEnd : advice+DescentTerminalRoleTables.count bits6≤ start)
    (bounded : ∀j block,(pages.address (N:=nodeCap) j block).Fits ((arena).gather start) hosts bw)
    (mounted : ∀j,advice≤j→j<advice+DescentTerminalRoleTables.count bits6→initial j=
      DescentStaticWordColumn.image advice
        (DescentTerminalRoleTables.literal («A»:=arity) (G:=groups) («p»:=p) («R»:=stride) (N:=nodeCap) (groups:=groupsAt) old cap)
        original (DescentTerminalRoleTables.count bits6) j)
    (wide : groupsAt ≤ bw) (nextStage : (arena).finish start≤ maskBase)
    (earlier : AddressPlan.Earlier cfg I next ms bw) (word : AddressPlan.last vfmt cfg I chan maskBase<2^bw)
    (actorWord : ∀(i : Fin hosts) (block : Fin blocks),initial ((actors block).base+i.val)=((encode 1 groupsAt (fun j=>
      (if ∃v,(b).target.home v=i ∧ ((A).pos v).1=j ∧ (A).block v=block then 1 else 0):Fin groupsAt→Cell 1)).val:Computability.VPVNP.BurstRAM.Word bw))
    (i : Fin hosts) (c' : Fin (groupsAt*blocks)) :
    blankAt (measured ms sockets (q:=q) (t:=T) (H:=cap) (N:=nodeCap) («A»:=cap)
      (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔ ∃ u,(b).target.chart ord rfl i u=c' := by
  have ran := DescentTerminalPrimitiveArena.native (a:=arity) (g:=groups) («p»:=p) (r:=stride)
    (N:=nodeCap) (groups:=groupsAt) (shops:=hosts) (dc:=wholeBits)
    old rawRoles advice start pop actors pages f0 f7 q cap initial original bound limit inputs romEnd bounded mounted
  have startLe : start ≤ (arena).finish start := by
    unfold DescentTerminalPrimitiveArena.Shape.finish DescentTerminalPrimitiveArena.Shape.widths
      DescentTerminalPrimitiveArena.Shape.number DescentTerminalPrimitiveArena.Shape.counting
      DescentTerminalPrimitiveArena.Shape.pointers DescentTerminalPrimitiveArena.Shape.public
      DescentTerminalPrimitiveArena.Shape.rom DescentTerminalPrimitiveArena.Shape.gather
    omega
  have hostFit : hosts ≤ 2^bw := by
    let x : Fin blocks := ⟨0,Nat.two_pow_pos _⟩
    have has := bound.actorSize x
    have ends := bound.actorEnd x
    exact has.trans ((Nat.le_add_left _ _).trans (ends.trans (startLe.trans limit.le)))
  exact (b).target.sockets_occupation ord rfl cfg I chan maskBase header sheet literal
    initial after earlier word hostFit wide bound.actorSize (fun x h => actorWord h x)
    start (startLe.trans nextStage) bound.actorEnd ran.2.2.1 i c'

end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape
