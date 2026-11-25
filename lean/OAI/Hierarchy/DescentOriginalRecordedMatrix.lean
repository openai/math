import OAI.Hierarchy.DescentCalendarMatrixOrigins
import OAI.Hierarchy.DescentOriginalOperandRow
import OAI.Hierarchy.DescentRecordedPublicBoard

namespace OAI
/-! # The original operand matrix of a real selected reset host -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentRotorWindowArchive DescentOldContactSender DescentSIMDLookup DescentSharedBookScan
open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentPaidResidentCount.Reset
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "cc" => B.terminals.commonDepth
local notation "r" => (Z).k-cc
local notation "dep" => GroupStage.depthBound D n f g
local notation "H" => S.hostSize i
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "pad" => input.valid.host
local notation "axis" => congrArg (fun m=>2^(m-cc)) B.keyWidth
variable {M field bw N K Rep hm lb tiny : ℕ}
    (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K Rep M hm lb tiny field dep bw)
    (book : RootBook (Z).n r deg (2^r) cap field) (space : rc.PreparedFits book) (mem : Memory bw)
    (hdr : OriginalHeader B pad rc book mem) (x : OriginalArrays B pad field)
local notation "snapshot" => root_snapshot B pad rc book space mem hdr x

local notation "home" => input.vertex.trans (Fin.castLEEmb pad)
local notation "slots" => 2^(S.groupWidth k tail i+k-cc)
local notation "countCast" => congrArg (fun t=>DescentRotorWindowArchive.count deg t cap) axis
local notation "adj" => PackedFlow.Padded.roster (D:=deg) (A) (Recorded.oldName input) pad
variable {src : RootSources deg (2^r) cap} {nbits tbits : ℕ}

/-- Every original matrix position is the recorded physical board position of
the same host and coarse group. The key-width cast changes only the bound of
its ordinal. The recorded packet supplies the actual predecessor roster. -/
theorem original_recorded_matrix (receipt : RootPacket B rc book space mem hdr src x nbits tbits)
    (v : input.V) (hi : Block cc) (j : DescentRotorWindowArchive.Input deg slots cap) :
    originalMatrix B rc book space mem x (home v) hi ((ix j).cast (countCast).symm)=
      recordedBoard B snapshot v hi j:=by
  let data : RowData deg slots cap field:=fun z=>senderMatrix B snapshot (home v) hi (ix z)
  have routes : (snapshot).peers=adj:=receipt.routes
  have arrived : data=recordedBoard B snapshot v hi:=by
    apply snapshot_matrix B snapshot v hi data
    intro z
    unfold data senderMatrix
    rw [routes]
    rfl
  have word:=congrFun (congrFun (congrFun (calendar_sender_matrix_eq B M field rc book space mem hdr x)
    (home v)) hi) ((ix j).cast (countCast).symm)
  change senderMatrix B snapshot (home v) hi (((ix j).cast (countCast).symm).cast countCast)=
    originalMatrix B rc book space mem x (home v) hi ((ix j).cast (countCast).symm) at word
  simpa only [Fin.cast_cast,Fin.cast_refl, id_eq] using word.symm.trans
    (show senderMatrix B snapshot (home v) hi (((ix j).cast (countCast).symm).cast countCast)=
      recordedBoard B snapshot v hi j by simpa only [Fin.cast_cast,Fin.cast_refl, id_eq] using congrFun arrived j)

theorem original_recorded_matrix_val (receipt : RootPacket B rc book space mem hdr src x nbits tbits)
    (v : input.V) (hi : Block cc) (j : DescentRotorWindowArchive.Input deg slots cap) :
    (originalMatrix B rc book space mem x (home v) hi ((ix j).cast (countCast).symm)).val=
      (recordedBoard B snapshot v hi j).val:=
  congrArg Fin.val (original_recorded_matrix B rc book space mem hdr x receipt v hi j)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
