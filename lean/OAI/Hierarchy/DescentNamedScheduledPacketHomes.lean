import OAI.Hierarchy.DescentRoleMountSpan
import OAI.Hierarchy.DescentNamedEarlyMatrixWord
import OAI.Hierarchy.DescentNamedTerminalPointerPins
import OAI.Hierarchy.DescentNamedOriginalReplayRead
import OAI.Hierarchy.DescentNamedPostEarlyPreflight
import OAI.Hierarchy.DescentSnapshotRankCapture

namespace OAI
/-! # The public packet homes and cohort counts on the scheduled terminal execution -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentMixedRouter Catalyst DescentInitialHost DescentExteriorReplay
open DescentTerminalPreflightSpace DescentTerminalFixedSlices DescentTerminalPrimitiveArena
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Routing CallPool
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage pinSpine publicSpine publicLayout originalPin
  postEarlyPreflightMemory fixedPreflightPrimitive
set_option maxRecDepth 2400
set_option maxHeartbeats 500000

variable {F:Type} [Field F] {cp ar:ℕ} (X:Approximation F cp ar) (G:PoweredGadget F) (S:AtomSchedule)
  {k tail:ℕ} (baseGroups:S.baseGroups=2^tail) (radix:S.radix=2^k)
  (g p q drift:ℕ) (op:RotorSpec) (headerRows paidRows:ℕ)
local notation "spec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
local notation "ports" => Fintype.card (Port ar X.width)
variable (j r t base compact:ℕ) (tag:ℕ→Bool) (rotation:ℕ→ℕ)
  (phase:Phase F) (snapshots:Snapshots k)
local notation "C" => replayCalendar X S k tail j r snapshots
local notation "early_" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t ports
local notation "slices_" => phase.stop early_
local notation "rom_" => (C).packetEnd slices_
local notation "shelf" => (spec).scanPages rom_ q
local notation "census_" => (shelf).stop
local notation "matrix" => DescentExteriorMatrixUpdate.Calendar.stop S k tail base+S.length
local notation "bks" => (spec).scalar.blocks
local notation "H" => (spec).scalar.shops
local notation "hw_" => phase.output.receiver
variable (blocks:2^k=phase.output.receiver.blocks) (shops:S.hostSize S.length=phase.output.receiver.hosts) (roleBase:ℕ)
  (peer:Bank) (paid actor:Fin (2^k)→Bank) (signed:Fin (2^k)→Fin (2*((capCalendar G.b S.rounds g S.height).prod*256))→Bank)
local notation "ptr" => fun (f:Fin 4) (j:Fin phase.output.argumentSlots) (b:Fin bks) =>
  phase.output.terminalPointers phase.dateBase f j (b.cast blocks)
variable {w:ℕ} (cohortRoom :
  let book := replayCalendar X S k tail j r snapshots
  let endAddress := DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t (Fintype.card (Port ar X.width))
  let layout := preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
  book.stop (layout.scanPages (book.packetEnd (phase.stop endAddress)) q).stop < 2^w)
local notation "out_" => postEarlyPreflightMemory X G S baseGroups radix g p q drift op headerRows paidRows j r t
  base phase snapshots blocks roleBase peer paid actor signed cohortRoom
variable (word :
    let layout := preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
    let book := replayCalendar X S k tail j r snapshots
    let stop := DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t (Fintype.card (Port ar X.width))
    let slices := phase.stop stop
    let pages := layout.scanPages (book.packetEnd slices) q
    layout.maskBase pages.stop < 2^w) (positive : 0<w) (alive : 0<S.hostSize S.length)
  (prev : ∀i<S.length, rotation i < base)
  (seed : compact+32*DescentExteriorShelf.span j r t (Fintype.card (Port ar X.width))≤base)
  (earlier : phase.output.metadataEnd phase.dateBase ≤
    DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t (Fintype.card (Port ar X.width)))
  (one : chunks phase.output.receiver.groups phase.output.receiver.lanes = 1)
  (roleEnd :
    let layout := preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
    let book := replayCalendar X S k tail j r snapshots
    let stop := DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t (Fintype.card (Port ar X.width))
    let slices := phase.stop stop
    let pages := layout.scanPages (book.packetEnd slices) q
    let paletteSize := DescentPrimitivePalette.colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
    let roleWidths := fun f : Fin 6 =>
      DescentTerminalCombinedRole.width paletteSize (max 8 (2^S.capGain))
        (NativeBranch.privateSlotCapacity G S drift) p drift f * (S.epochPower^S.localTokenExponent) * layout.groups
    roleBase + DescentTerminalRoleTables.count roleWidths ≤ layout.cohortEnd pages.stop)
  (before :
    let layout := preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
    let book := replayCalendar X S k tail j r snapshots
    let stop := DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t (Fintype.card (Port ar X.width))
    let slices := phase.stop stop
    let pages := layout.scanPages (book.packetEnd slices) q
    layout.Before pages.stop paid actor signed peer pages.total pages.modulo (book.homes slices) pages.boundaries)
  (paidRowsFit : ∀b, S.hostSize S.length ≤ (paid b).size)
  (signedRows : ∀b j, S.hostSize S.length ≤ (signed b j).size)

variable {n f h C₀ R : ℕ} {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
  {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
    (S.epochPower ^ S.priceExponent : ℝ)}
  {epoch : Epochs G hu he (h:=h) («C» := C₀) (Ht:=GroupStage.depthBound (atRound S.rounds) n f g)
    (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
  {choice : (Epochs.finish G hu he epoch).Choice} (b : Branch X G S radix R epoch choice) (hp : 0<p)
  (width : S.groupWidth k tail 0+k=j+(j+r))
variable (dated : Memory w) (captureFloor countStart countRows : ℕ) (source : ℕ→ℕ)
variable (roleMount:Chronology.RoleMount w roleBase base)
local notation "copied_" => DescentLowCountBook.output countStart source dated countRows
local notation "captured" => roleMount.phase.image copied_
local notation "reel" => DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail base tag rotation j r t ports compact captured
local notation "replayed" => (C).memory slices_ census_ cohortRoom (phase.memory early_ reel)
local notation "prim" => fixedPreflightPrimitive X G S (k:=k) (tail:=tail) g p q drift op headerRows paidRows
  census_ rom_ w paid actor signed matrix roleBase (phase.banks early_) ptr replayed
local notation "counts" => Computability.BorderVNP.FragmentBucket.count (cohortHome X G S b hp baseGroups)

include shops word positive alive prev seed earlier one roleEnd before paidRowsFit signedRows in
/-- The input rank facts refer to the original end-of-date memory. The count copy,
early relocation, role slices, replay, and fixed terminal prefix use a single halt image. -/
theorem scheduled_packet_homes
    (ranks : b.path.snapshotRanks snapshots captureFloor dated) (grows : captureFloor≤base) (rankRole:captureFloor≤roleBase)
    (disjoint : ∀d<S.length,∀B,snapshots.compact d=some B →
      B.base+B.size≤countStart ∨ countStart+countRows≤B.base)
    (labels : b.path.snapshotLabels snapshots) (hostFit : ∀d<S.length,S.hostSize d≤ snapshots.hosts d)
    (kept : j≤S.groupWidth k tail S.length+k) (bits : (k*S.length+1)*2^(8+S.capGain*S.length)≤w) :
    (∀i : Fin (ports*2^(j+r)), ((C).homes slices_).read (out_ reel) (i.val:Word w)=
      ((publicHost X G S b hp baseGroups width i).val:Word w)) ∧
    (∀i : Fin (S.hostSize S.length), (out_ reel) (((spec).census census_).base+i.val)=(counts i:Word w)) ∧
    (∀i : Fin (S.hostSize S.length), prim (((spec).census census_).base+i.val)=(counts i:Word w)) ∧
    ∀i : Fin (S.hostSize S.length), (prim (((spec).frozenRoster census_).base+i.val)).val=
      frozenRosterCode X G S b hp baseGroups i := by
  have prior:=b.path.snapshotRanks_count_capture snapshots source ranks le_rfl disjoint
  have copied:=b.path.snapshotRanks_frame snapshots prior grows
    (out:=captured) (fun i hi=>roleMount.frame copied_ i (.inl (hi.trans_le rankRole)))
  have earlyLe : base≤early_ := by
    unfold DescentExteriorMatrixUpdate.Calendar.earlyEnd DescentExteriorMatrixUpdate.Calendar.earlyAt
      DescentExteriorMatrixUpdate.Calendar.stop DescentExteriorMatrixUpdate.Calendar.tableAt
    simp only [Nat.add_assoc, Nat.le_add_right]
  have slicesLe : early_≤ slices_ := by
    unfold Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop DescentTerminalSliceShelf.fence
      DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    simp only [Nat.add_assoc, Nat.le_add_right]
  have scratch := (C).addresses slices_ census_
  have fits (a : ℕ) (ha : a<S.length) (B : Bank) (hb : snapshots.compact a=some B) :
      B.Fits w ((C).scratch slices_) := by
    have old := b.path.snapshot_rank_rooms snapshots base captured copied a ha B hb
    exact ⟨old.1,old.2.1,old.2.2.trans (earlyLe.trans (slicesLe.trans scratch.1))⟩
  have inOrder : rom_ ≤ census_ := Nat.le_add_right ..
  have seen := original_replay_from_dated
    (F:=F) (cp:=cp) (P:=ar) (k:=k) (n:=n) (h:=h) («C»:=C₀) (f:=f) (g:=g) (p:=p)
    (he:=he) (hu:=hu) (radix:=radix) (R:=R) (r:=epoch) (c:=choice)
    (tail:=tail) (j:=j) (rest:=r) (bw:=w)
    X G S b hp baseGroups width snapshots census_ phase base t compact
    tag rotation captured cohortRoom inOrder hostFit copied labels positive prev seed earlier
    one kept alive bits
  have preflight := post_early_preflight_run_and_census (F:=F) (cp:=cp) (ar:=ar) (k:=k) (tail:=tail) (w:=w)
    X G S baseGroups radix g p q drift op headerRows
    paidRows j r t base phase snapshots blocks shops roleBase peer paid actor signed cohortRoom word positive
    alive earlier one fits roleEnd before paidRowsFit signedRows reel
  have countWords (i : Fin (S.hostSize S.length)) :
      (out_ reel) (((spec).census census_).base+i.val)=(counts i:Word w) ∧
      prim (((spec).census census_).base+i.val)=(counts i:Word w) := by
    let address := ((spec).census census_).base+i.val
    have lower : census_≤address := by
      change census_≤census_+_+_+i.val
      simp only [Nat.add_assoc, Nat.le_add_right]
    have size : (S.hostSize S.length)≤((spec).census census_).size := Nat.le_pow_clog (by decide) _
    have upper : address<(spec).cohortEnd census_ :=
      (Nat.add_lt_add_left (i.isLt.trans_le size) _).trans_le ((spec).census_end census_)
    have held := preflight.2 address lower upper
    have read : replayed address=(counts i:Word w) := by
      have observed : (replayed address).val=counts i := (seen.census i).2
      exact (Fin.cast_val_eq_self (replayed address)).symm.trans
        (congrArg (fun n : ℕ => (n : Word w)) observed)
    exact ⟨held.1.trans read,held.2.trans read⟩
  have rosterWord (i:Fin (S.hostSize S.length)) :
      (prim (((spec).frozenRoster census_).base+i.val)).val=frozenRosterCode X G S b hp baseGroups i:=by
    let address:=((spec).frozenRoster census_).base+i.val
    have lower:census_≤address:=by
      change census_≤DescentTerminalCohortArena.tallyBase census_ _ _ _ _+_+i.val
      unfold DescentTerminalCohortArena.tallyBase DescentTerminalCohortArena.indexBase
        DescentTerminalPacketSlotRAM.out DescentTerminalCohortArena.order
      dsimp only
      simp only [Nat.add_assoc, Nat.le_add_right]
    have upper:address<(spec).cohortEnd census_:=by
      exact (Nat.add_lt_add_left i.isLt _).trans_le (Nat.le_succ _)
    have keep:prim address=replayed address:=(preflight.2 address lower upper).2
    exact (congrArg Fin.val keep).trans (seen.census i).1
  exact ⟨fun i=>(preflight.1.2.2.2.2 i).trans (seen.homes i),
    fun i=>(countWords i).1,(fun i=>(countWords i).2),rosterWord⟩

include shops word positive alive prev seed earlier one roleEnd before paidRowsFit signedRows in
/-- The public matrix consumed by the lookup is located below the first allocated
slice. Its attained primitive word is consequently the paid early matrix word. -/
theorem scheduled_primitive_matrix (ranks:b.path.snapshotRanks snapshots captureFloor dated)
    (grows:captureFloor≤base) (rankRole:captureFloor≤roleBase)
    (disjoint:∀i<S.length,∀B,snapshots.compact i=some B→B.base+B.size≤countStart ∨ countStart+countRows≤B.base)
    (rotations:b.path.RotationWords tag rotation captured) :
    prim matrix=((DescentExterior.matrixCode (pinSpine X G S b hp baseGroups).matrix).val:Word w) := by
  have prior:=b.path.snapshotRanks_count_capture snapshots source ranks le_rfl disjoint
  have copied:=b.path.snapshotRanks_frame snapshots prior grows
    (out:=captured) (fun i hi=>roleMount.frame copied_ i (.inl (hi.trans_le rankRole)))
  have same : matrix < early_ := (Nat.lt_succ_self _).trans_le (Nat.le_add_right ..)
  have baseBefore:base≤early_:=by
    unfold DescentExteriorMatrixUpdate.Calendar.earlyEnd DescentExteriorMatrixUpdate.Calendar.earlyAt
      DescentExteriorMatrixUpdate.Calendar.stop DescentExteriorMatrixUpdate.Calendar.tableAt
    simp only [Nat.add_assoc, Nat.le_add_right]
  have lower:early_≤ slices_:=by
    unfold Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop DescentTerminalSliceShelf.fence
      DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    simp only [Nat.add_assoc, Nat.le_add_right]
  obtain ⟨a₀,a₁,a₂,a₃,_⟩:=(C).addresses slices_ census_
  have packet:rom_≤census_:=Nat.le_add_right ..
  have toCensus:early_≤census_:=lower.trans (a₀.trans (a₁.trans (a₂.trans packet)))
  have fits (i:ℕ) (hi:i<S.length) (B:Bank) (hb:snapshots.compact i=some B) :
      B.Fits w ((C).scratch slices_) := by
    have old:=b.path.snapshot_rank_rooms snapshots base captured copied i hi B hb
    exact ⟨old.1,old.2.1,old.2.2.trans (baseBefore.trans (lower.trans a₀))⟩
  have runtime:=post_early_preflight_site_words (F:=F) (cp:=cp) (ar:=ar) (k:=k) (tail:=tail) (w:=w)
    X G S baseGroups radix g p q drift op headerRows paidRows
    j r t base phase snapshots blocks shops roleBase peer paid actor signed cohortRoom word positive alive earlier one
    fits roleEnd before paidRowsFit signedRows reel
  have layers:=(spec).layers census_
  have index:matrix<(spec).weights census_:=same.trans_le
    (toCensus.trans (((spec).cohort_le census_).trans (layers.1.trans layers.2.1)))
  have preserved:(out_ reel) matrix=reel matrix:=runtime.1.1.1.2.2.1 matrix (.inl same)
  exact (runtime.2.1 matrix index).symm.trans (preserved.trans
    (early_matrix_word X G S b hp baseGroups (j:=j) (rest:=r) (t:=t) base tag rotation compact captured
      rotations prev seed (toCensus.trans_lt (a₃.trans_lt cohortRoom))))

end
end Hierarchy.DescentSixParty.SeedNamed.Branch
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Branch.pinSpine Branch.publicSpine Branch.publicLayout
  Branch.originalPreflightMemory Branch.postEarlyPreflightMemory Branch.fixedPreflightPrimitive
