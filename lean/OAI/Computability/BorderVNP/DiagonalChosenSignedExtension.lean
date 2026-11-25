import OAI.Computability.BorderVNP.RoutingISASignedStartupExtension
import OAI.Computability.BorderVNP.CubeISALocalRowPinnedBoot
import OAI.Computability.BorderVNP.TransmissionChosenArena

/-! # Actual boot operands shared by the cube and signed residue reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP.BurstRAM RoutingISA Branch Crossing TeamContraction TeamContraction.ProcessorSlots
open ResidueBox ResiduePins GeometryAdvice DiagonalResidueRAM PackedHistoryCircuit
open private PinClear.read from OAI.Computability.BorderVNP.PackedHistoryPreparedInput

variable {K : Type*} [Field K] {dim labels : ℕ} {ι : Type} [Fintype ι]
variable {paid : PaidIdentity K dim labels} {aux : ι → K} {q k s : ℕ}
variable {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {R : CommonField paid aux q k s ord}
variable {chart : AdvisedBranch R} [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
variable {teams r multBits tally w width : ℕ}
variable (reader : ChosenReader chart (teams+1) r multBits tally w width)
variable (l : SignedTaskArena.Layout) (A : StartupArena) (valuation entry totals raw team subtotal : ℕ)
    (old : Fin 81 → Word w) (fresh profile gates outputs bits off ell d n blocks b h t : ℕ)
local notation "signed" => l.extension raw team subtotal old
local notation "overlay" => fun v => CubeHeaderInstall.jointFields v fresh profile gates outputs bits off ell d n blocks b h t
local notation "initial" => CubeHeaderInstall.pinFields signed (Allocation.stop fresh profile gates outputs bits w)
  d (n+1) (h*b) blocks profile (Cube.Physical.declarationCap n d blocks b h t)
local notation "ext" => Allocation.fields initial fresh profile gates outputs bits off ell
local notation "packet" => reader.packetAt (ReaderPlacement.inArena A valuation entry totals ext)

/-- The actual stripe allocation and signed task directory define one reference
packet. On this packet the pinned cube fields have exactly the table used by
the cube checker and the residue reader has its required full extension. -/
theorem ChosenReader.signedStartup_packet :
    (packet).extension = overlay (l.cube.extension signed) ∧
    packet = reader.nativePacket valuation entry A.ibase A.hbase totals (l.extension raw team subtotal (overlay old)) := by
  constructor
  · rw [l.cube_extension_signed raw team subtotal old]
    rfl
  · exact congrArg (reader.nativePacket valuation entry A.ibase A.hbase totals)
      (l.extension_joint raw team subtotal old fresh profile gates outputs bits off ell d n blocks b h t)

/-- On every real post-boot memory the copied primary fields and common header
satisfy the cube checker and the same 81 words give all signed task controls. -/
theorem ChosenReader.signedStartup_boot {L : Pins.Layout}
    {F : Pins.ProcessorFields L} {f : BroadcastFrame} {loc : AdviceLayout}
    {pub : Arg → Word w} {header : List Bool} {reg : Bank w} {mem : Memory w}
    (boot : JointHeader.BootHeaderState F f loc packet pub header reg mem) :
    LocalRow.BootPins pub f (overlay (l.cube.extension signed)) header mem ∧
    ∀ j : Fin 81, mem ((pub 0).val+31+j.val) = l.extension raw team subtotal (overlay old) j := by
  have installed := reader.signedStartup_packet l A valuation entry totals raw team subtotal old
    fresh profile gates outputs bits off ell d n blocks b h t
  refine ⟨⟨boot.frame.broadcast.1,boot.frame.broadcast.2.1,boot.frame.broadcast.2.2.2.2.2.2,
    fun j => (boot.extension j).trans (congrFun installed.1 j),boot.header⟩,?_⟩
  intro j
  exact (boot.extension j).trans (congrArg (fun p => ReferencePacket.extension p j) installed.2)

/-- After the guessed pin writes and arbitrary successful geometry reconstruction,
the actual whole lower bank (including the residue advice), indexed cube operands
and signed tally operands still come from the one common boot. -/
theorem ChosenReader.signedStartup_afterGeometry {u : Fin A.teams} {adviceOffset : ℕ}
    {f : BroadcastFrame} {loc : AdviceLayout} {pub : Arg → Word w} {header : List Bool} {reg : Bank w}
    {F : Pins.ProcessorFields (A.operands u adviceOffset packet).layout}
    {before after : Memory w} (boot : JointHeader.BootHeaderState F f loc packet pub header reg before)
    (guess : ℕ → Bool) (sameFrame : (pub 0).val=A.frame)
    (copyEnd : f.dst+header.length ≤ A.ibase)
    (keep : ∀ i < A.next, after i = Pins.preparedMemory (A.operands u adviceOffset packet).layout guess before
      (A.operands u adviceOffset packet).layout.count i) :
    (∀ i < A.ibase, after i = before i) ∧
    LocalRow.BootPins pub f (overlay (l.cube.extension signed)) header after ∧
    ∀ j : Fin 81, after ((pub 0).val+31+j.val) = l.extension raw team subtotal (overlay old) j := by
  have clear : PinClear (A.operands u adviceOffset packet).layout 0 A.ibase := by
    refine ⟨Or.inl (Nat.zero_add _).le, Or.inl ?_⟩
    change 0+A.ibase ≤ A.ibase+A.count
    omega
  have low : ∀ i < A.ibase, after i = before i := by
    intro i hi
    have room : A.ibase ≤ A.next := by unfold StartupArena.next StartupArena.hbase; omega
    exact (keep i (hi.trans_le room)).trans (by simpa only [Nat.zero_add] using PinClear.read clear guess before i hi)
  have frameRoom : (pub 0).val+112 ≤ A.ibase := by
    rw [sameFrame]
    unfold StartupArena.ibase StartupArena.broadcastBase StartupArena.dense
    omega
  obtain ⟨pins,fields⟩ := reader.signedStartup_boot l A valuation entry totals raw team subtotal old
    fresh profile gates outputs bits off ell d n blocks b h t boot
  exact ⟨low,pins.below frameRoom copyEnd (fun i hi => congrArg Fin.val (low i hi)),fun j =>
    (low _ (by have := j.isLt; omega)).trans (fields j)⟩

end Diagonal

end BorderVNP
end Computability
end OAI
