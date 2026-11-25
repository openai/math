import OAI.Hierarchy.ProbeDiscrepancyBoot
import OAI.Hierarchy.ProtocolRAMCalendarStripROMBudget

namespace OAI
/-! # Charging and placing both actual lookup tables above the complete scalar header -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped Fin.CommRing Classical
variable {z d k q depth : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))

def outerVector (F : Type*) [Field F] [SiteNaming (PayloadStrip.Site N k)] (s : Boards z d k q depth)
    (b : JointHeader.Board) (c : Mesh) (finish : ℝ) (price : PhasePrice) (radix precision : ℕ) :=
  DiscrepancyROM.payload F N k (priceTable s b c finish price).stop radix precision (DeadlineROM.prices c finish price)

def innerVector (F : Type*) [Field F] [SiteNaming (PayloadStrip.Site N k)] [SiteNaming (ChainStrip.Site depth k)]
    (s : Boards z d k q depth) (b : JointHeader.Board) (c : Mesh) (finish : ℝ) (price : PhasePrice)
    (outerRadix innerRadix outerPrecision innerPrecision : ℕ) :=
  DiscrepancyROM.purchase F depth k (outerVector F s b c finish price outerRadix outerPrecision).stop
    innerRadix innerPrecision (DeadlineROM.prices c finish price)

def vectorCharge (stages k depth phases outerRadix innerRadix : ℕ) :=
  phases*(2*(outerRadix^Fintype.card (PayloadStrip.Quotes stages k)+1))+
  phases*(2*(innerRadix^Fintype.card (ChainStrip.Axes depth k)+1))

theorem vector_layout (F : Type*) [Field F] [SiteNaming (PayloadStrip.Site N k)] [SiteNaming (ChainStrip.Site depth k)]
    (s : Boards z d k q depth) (b : JointHeader.Board) (c : Mesh) (finish : ℝ) (price : PhasePrice)
    (R S Q T : ℕ) :
    let old:=outerVector F s b c finish price R Q
    let new:=innerVector F s b c finish price R S Q T
    old.base=(priceTable s b c finish price).stop ∧ new.base=old.stop ∧
      new.stop≤(priceTable s b c finish price).stop+vectorCharge N k depth (DeadlineROM.count c) R S := by
  intro old new
  refine ⟨rfl,rfl,?_⟩
  have first:=old.charged_size
  have second:=new.charged_size
  change old.stop≤(priceTable s b c finish price).stop+_ at first
  change new.stop≤ old.stop+_ at second
  dsimp only [vectorCharge]
  calc
    new.stop ≤ old.stop+_ := second
    _ ≤ ((priceTable s b c finish price).stop+_)+_ := Nat.add_le_add_right first _
    _ = _ := Nat.add_assoc _ _ _

theorem vector_word_room (F : Type*) [Field F] [SiteNaming (PayloadStrip.Site N k)] [SiteNaming (ChainStrip.Site depth k)]
    (s : Boards z d k q depth) (b : JointHeader.Board) (c : Mesh) (finish : ℝ) (price : PhasePrice)
    (R S Q T core : ℕ) (width : b.cap*b.width+1≤2^z) (initial : b.initial≤ heapEnd z d copies+core*2^z)
    (enough : core+headerFactor s b c+vectorCharge N k depth (DeadlineROM.count c) R S+1≤2^z) :
    (innerVector F s b c finish price R S Q T).stop<2^wordBits z d copies := by
  have old:=header_bound s b c finish price width
  have new:=(vector_layout F s b c finish price R S Q T).2.2
  let V:=vectorCharge N k depth (DeadlineROM.count c) R S
  have fit:=append_room (d:=d) (copies:=copies) enough
  have positive:=Nat.two_pow_pos z
  have scale : V≤ V*2^z := by nlinarith
  apply lt_of_le_of_lt _ fit
  rw [Nat.add_mul,Nat.add_mul]
  change _≤(priceTable s b c finish price).stop+V at new
  dsimp only [V] at *
  omega

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
