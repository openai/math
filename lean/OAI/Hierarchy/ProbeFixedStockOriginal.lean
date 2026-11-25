import OAI.Hierarchy.ProbeFixedStockWindow
import OAI.Hierarchy.ProtocolRAMCalendarStripBuyIdle
import OAI.Hierarchy.ProtocolRAMCalendarEconomicBoot

namespace OAI
/-! # Original stock-commit operands of the priced fixed chart -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockBound StockCommit StripDirectory
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "G" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "g" => v.stamp P z width r banks src tab dst owners

/-- The row- and phase-independent joint half table and the one published port
header determine the original operands of every emitted signed stock update. -/
theorem stock_original (mem fixture : Memory W) («public» : (H).Resident mem)
    (half : let b:=JointHeader.half P.joint z N k
      ∀x,b.base ≤ x → x < b.base+b.size → mem x=FeedROM.halfAdvice b fixture x)
    (slots : D ≤ 2^W) (alphabet : v.menu.alphabet ≤ 2^W) (nb : v.menu.copiesAt v.copyScale width < 2^W)
    (mass : v.menu.alphabet*v.menu.copiesAt v.copyScale width < 2^W) (a : Attempt) :
    Original (f a) (g a) (StripChart.start B a) (G).first mem fixture := by
  have portRoom:=v.stock_port_room P z width
  let fmt:=f a
  let h:=fmt.occurrenceHeader (StripChart.start B a)
  let bank:=JointHeader.half P.joint z N k
  have eq : h=(H).ports.header 0 := by
    have shape:= (shape_header F B v.mesh G P.joint.initial a).1
    change h=StripChart.header F B a at shape
    rw [shape]
    cases a <;> simp only [PortROM.Table.header,Fin.val_zero,Nat.zero_mul,Nat.add_zero] <;> rfl
  have halfPtr : fmt.stockSource.half=bank := by cases a <;> rfl
  have portsBefore : h.stop ≤ (G).first := by
    rw [eq]
    exact ((H).ports.end_le 0).trans portRoom
  have bankBefore : bank.base+bank.size ≤ (H).ports.base := Nat.le_add_right ..
  have initial : (G).first ≤ (G).base v.mesh (.attempt a) := Nat.le_add_right ..
  have label:=v.stock_label P z width a
  have count:=(shape_header F B v.mesh G P.joint.initial a).2.trans (congrArg PortHeader.count (shape_header F B v.mesh G P.joint.initial a).1).symm
  have loaded := (v.catalogue_words (v.seed P z width) width).1
  have countBits := (v.ordinary_dimensions P z width a).2
  refine ⟨occurrence_sealed F B v.mesh G P.joint.initial a,count,?_,portsBefore,?_,?_,slots,?_,?_,?_,?_⟩
  · change h.Loaded mem
    rw [eq]
    exact «public».ports 0
  · change fmt.stockSource.half.base+fmt.stockSource.half.size ≤ (G).first
    rw [halfPtr]
    exact bankBefore.trans ((Nat.le_add_right (H).ports.base _).trans portRoom)
  · change h.stop ≤ fmt.board.verdict+1
    exact portsBefore.trans (initial.trans label)
  · exact loaded.le.trans alphabet
  · exact countBits.le.trans_lt nb
  · simpa only [← loaded,← countBits] using mass
  · change ∀x,fmt.stockSource.half.base ≤ x → x < fmt.stockSource.half.base+fmt.stockSource.half.size → mem x=FeedROM.halfAdvice fmt.stockSource.half fixture x
    simpa only [halfPtr] using half

/-- One booted tape suffices for every trial. The half memory is read back from
the authentic joint header, and the shared port table comes from the true
economic boot receipt. -/
theorem stock_boot_original {jobs phases size : ℕ} (phase : Fin phases→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (rest fixture : Boot.Tape z (2^v.W)) (markets : Fin jobs→Market z (2^v.W) k) (layout : Boot.Layout markets size)
    (first : 2^z ≤ P.joint.initial) (heap : heapEnd z (2^v.W) copies ≤ P.joint.initial)
    (fits : JointHeader.stop P.joint z N k phases ≤ size)
    (before : ∀i,JointHeader.stop P.joint z N k phases ≤ Boot.low (markets i))
    (slots : D ≤ 2^W) (alphabet : v.menu.alphabet ≤ 2^W) (nb : v.menu.copiesAt v.copyScale width < 2^W)
    (mass : v.menu.alphabet*v.menu.copiesAt v.copyScale width < 2^W) :
    let mem := Boot.booted markets size (JointHeader.words P.joint z (2^v.W) N k phase π (fun _=>0) rest)
    (H).Resident mem → ∀a, Original (f a) (g a) (StripChart.start B a) (G).first mem fixture := by
  intro mem «public» a
  exact v.stock_original P z width r banks src tab dst owners mem fixture «public»
    (StockBound.boot_half P.joint phase π (fun _=>0) rest fixture markets layout Nat.one_le_two_pow first heap fits before)
    slots alphabet nb mass a

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
