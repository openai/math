import OAI.Hierarchy.DescentNamedSocketOccupation
import OAI.Hierarchy.DescentNamedTerminalPreflight
import OAI.Hierarchy.DescentTerminalPreflightReelFrame

namespace OAI
/-! # Named primitive readbacks at the end of the physical preprocessing schedule -/

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
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "U" => Label G s Z rot
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => S.epochPower^S.localTokenExponent
local notation "venues" => S.groupCount S.length*2^k

variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
variable (age : 0<S.height) (wFit : NativeBranch.binLimit (k:=k) S ≤ W)
  (qFit : NativeBranch.localLimit G S ≤ q) (qh : 0<q)
local notation "ord" => Branch.leafOrder X G S b positive base width

variable (cfg : DescentTerminalCompiledPrefix.Shape)
    (pool : terminalPool X G S (W*piece) q W n h C f g ≤ cfg.terminal.pool)
    (raw : terminalRawRows X G S (W*piece) q n h C f g ≤ cfg.terminal.plane.rawRows)
local notation "leaf" => normalizedLeaf X G S ordinary reset branch positive room shorten c
  base width age wFit qFit qh cfg pool raw
local notation "groupsAt" => S.groupCount S.length
local notation "hostGraph" => (world).graph
local notation "sites" => (ord).site
variable {arity groups stride oldTags B bw : ℕ} (old : DescentEpochTagKeys.Codec (Label G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) oldTags)
variable (fmt : Branch.PreflightFormat) (origin header : ℕ) (I : AddressPlan.Input)
local notation "pre" => Branch.preflightSpec X G S k g p tail fmt
local notation "T" => DescentBundleTagKeys.capacity oldTags arity groups p stride
local notation "V" => (⟨q,T,cap,nodeCap,cap,p,groupsAt⟩ : Home.Format)
variable (sheet : (S.groupCount S.length*2^k) * DescentTerminalVertexFields.span q
    (DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride)
    (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))
    (S.epochPower^S.localTokenExponent)
    (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (W*piece) ≤ B)
    (literal : DescentTerminalEmitter.Compact.Literals I.sources)
local notation "floor_" => (pre).maskBase origin
local notation "chan" => (pre).channels origin
local notation "ms" => (AddressPlan.meter V chan floor_).layout
local notation "regs" => AddressPlan.registers V cfg chan floor_ header
local notation "next" => AddressPlan.afterMeter V cfg chan floor_
local notation "abi" => AddressPlan.layout cfg I next regs
local notation "arena" => AddressPlan.rowArena cfg I next
local notation "sockets" m:arg => Suffix.sockets cfg abi ((arena).mount (AddressPlan.input V cfg I chan floor_ header sheet literal m))

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

/-- Occupation and primitive operands are acquired once. They can be read again
after the Book, controls, two width scans, and header draft have all run. -/
theorem normalized_socket_dates (primitive ports : Memory bw)
    (prior : ∀ j<(pre).weights origin,ports j=primitive j)
    (early : AddressPlan.Earlier cfg I next ms bw)
    (room_ : AddressPlan.last V cfg I chan floor_<2^bw)
    (occ : ∀ (i : Fin (S.hostSize S.length)) (c' : Fin (groupsAt*2^k)),
      blankAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
        (measured ms (sockets primitive) (q:=q) (t:=T) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔ ∃ u,(b).target.chart ord rfl i u=c')
    (previous : ∀ i u,PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranks i)
      (hH i) (hN i) (hA i) u
        (venueField (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
          (cellAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
            (measured ms (sockets primitive) (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) i)
        ((b).target.rawResident ord rfl i u)))) :
    (∀ (i : Fin (S.hostSize S.length)) (c' : Fin (groupsAt*2^k)),
      blankAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
        (measured ms (sockets ports) (q:=q) (t:=T) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔ ∃ u,(b).target.chart ord rfl i u=c') ∧
    (∀ i u,PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranks i)
      (hH i) (hN i) (hA i) u
        (venueField (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
          (cellAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
            (measured ms (sockets ports) (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) i)
        ((b).target.rawResident ord rfl i u)))) := by
  have same (i : Fin (S.hostSize S.length)) :=
    (pre).measured_after_preflight origin V cfg I header sheet literal primitive primitive ports
      (fun _ _ => rfl) prior early room_ i
  constructor
  · intro i cell
    exact ((congrArg (fun view => blankAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) view cell ≠ 0) (same i)).to_iff).trans (occ i cell)
  · intro i u
    exact (congrArg (fun view => PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranks i)
      (hH i) (hN i) (hA i) u
        (venueField (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
          (cellAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) view
        ((b).target.rawResident ord rfl i u)))) (same i)).mpr (previous i u)

variable (rom K codes front : ℕ) (peer : Bank)
  (wing : Fin (2^k) → Fin (2*((capCalendar G.b S.rounds g S.height).prod*256)) → Bank)
  (total modulo homes : Bank) (boundary : ℕ) (other : AddressPlan.Input)
  (tables : AddressPlan.RouteSources.Tables)
local notation "lateInput" => (pre).reachedInput origin rom q piece W K codes front peer wing
  total modulo homes boundary cfg V other tables venues B
local notation "lateABI" => AddressPlan.layout cfg lateInput next regs
local notation "lateArena" => AddressPlan.rowArena cfg lateInput next
local notation "lateSocket" lit:arg m:arg => Suffix.sockets cfg lateABI ((lateArena).mount
  (AddressPlan.input V cfg lateInput chan floor_ header sheet lit m))

/-- The mask, role tuple and occupied-venue chart are measured again after the
seventeen-column reel and its verdict fold, using its actual surviving intervals. -/
theorem normalized_reel_socket_dates (literalLate : DescentTerminalEmitter.Compact.Literals (lateInput).sources)
    (primitive ports folded : Memory bw)
    (prior : ∀ j<(pre).weights origin,ports j=primitive j)
    (fence firstFree dst : ℕ)
    (saved : ∀ a,a<fence → (a<firstFree ∨ dst<a) → folded a=ports a)
    (late : dst<(pre).cohortEnd origin) (ceiling : floor_≤fence)
    (early : AddressPlan.Earlier cfg lateInput next ms bw)
    (room_ : AddressPlan.last V cfg lateInput chan floor_<2^bw)
    (occ : ∀ (i : Fin (S.hostSize S.length)) (c' : Fin (groupsAt*2^k)),
      blankAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
        (measured ms (lateSocket literalLate primitive) (q:=q) (t:=T) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔ ∃ u,(b).target.chart ord rfl i u=c')
    (previous : ∀ i u,PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranks i)
      (hH i) (hN i) (hA i) u
        (venueField (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
          (cellAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
            (measured ms (lateSocket literalLate primitive) (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) i)
        ((b).target.rawResident ord rfl i u)))) :
    (∀ (i : Fin (S.hostSize S.length)) (c' : Fin (groupsAt*2^k)),
      blankAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
        (measured ms (lateSocket literalLate folded) (q:=q) (t:=T) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔ ∃ u,(b).target.chart ord rfl i u=c') ∧
    (∀ i u,PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranks i)
      (hH i) (hN i) (hA i) u
        (venueField (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
          (cellAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
            (measured ms (lateSocket literalLate folded) (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) i)
        ((b).target.rawResident ord rfl i u)))) := by
  have same (i : Fin (S.hostSize S.length)) := ((pre).reel_measured origin rom q piece W K codes front
    peer wing total modulo homes boundary cfg V other tables venues B header sheet literalLate
    ports folded fence firstFree dst saved late ceiling early room_ i).trans
      ((pre).measured_after_preflight origin V cfg lateInput header sheet literalLate primitive primitive ports
        (fun _ _ => rfl) prior early room_ i)
  constructor
  · intro i cell
    exact ((congrArg (fun view => blankAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) view cell ≠ 0) (same i)).to_iff).trans (occ i cell)
  · intro i u
    exact (congrArg (fun view => PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranks i)
      (hH i) (hN i) (hA i) u
        (venueField (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
          (cellAt (q:=q) (t:=T) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) view
        ((b).target.rawResident ord rfl i u)))) (same i)).mpr (previous i u)

end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape
