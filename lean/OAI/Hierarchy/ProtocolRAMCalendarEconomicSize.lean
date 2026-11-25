import OAI.Hierarchy.ProtocolRAMCalendarEconomicHeader
import OAI.Hierarchy.ProtocolRAMCalendarStripTreeBudget

namespace OAI
/-! # Total space for the complete fixed public header and private chronological arena -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CatalogueRows
open scoped Classical
variable {z W k q depth : ℕ}
local notation "d" => 2^W
local notation "N" => Stages z (2^W)
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (s : Boards z (2^W) k q depth) (t : TreeCosts) (c : Mesh) (joint : JointHeader.Board)
  (catalogue : Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
  (finish : ℝ) (price : PhasePrice) (R S Q T : ℕ)

def economicFactor :=
  let phase:=DeadlineROM.prices c finish price
  let m:=menuPages F s t 0 R S phase
  headerFactor s joint c + 2*vectorCharge N k depth (DeadlineROM.count c) R S +
    (2*(m.leftAlphabet.radix+1)+2*(m.rightAlphabet.radix+1))+
    treePagesFactor c d k s.sampler.degree depth

theorem menu_charged (base : ℕ) :
    let m:=menuPages F s t base R S (DeadlineROM.prices c finish price)
    m.stop≤base+vectorCharge N k depth (DeadlineROM.count c) R S+
      (2*(m.leftAlphabet.radix+1)+2*(m.rightAlphabet.radix+1)) := by
  intro m
  have a:=m.left.charged_size
  have b:=m.right.charged_size
  have c₁:=m.leftAlphabet.charged_size
  have d₁:=m.rightAlphabet.charged_size
  change m.left.stop≤base+_ at a
  change m.right.stop≤ m.left.stop+_ at b
  change m.leftAlphabet.stop≤ m.right.stop+1*(2*(m.leftAlphabet.radix^1+1)) at c₁
  change m.stop≤ m.leftAlphabet.stop+1*(2*(m.rightAlphabet.radix^1+1)) at d₁
  simp only [pow_one,one_mul] at c₁ d₁
  change m.left.stop≤base+DeadlineROM.count c*(2*(R^Fintype.card (PayloadStrip.Quotes N k)+1)) at a
  change m.right.stop≤ m.left.stop+DeadlineROM.count c*(2*(S^Fintype.card (ChainStrip.Axes depth k)+1)) at b
  unfold vectorCharge
  omega

private theorem menu_alphabet_space (base : ℕ) :
    let p := menuPages F s t base R S (DeadlineROM.prices c finish price)
    let origin := menuPages F s t 0 R S (DeadlineROM.prices c finish price)
    2*(p.leftAlphabet.radix+1)+2*(p.rightAlphabet.radix+1) =
      2*(origin.leftAlphabet.radix+1)+2*(origin.rightAlphabet.radix+1) := by
  dsimp only [menuPages, MenuROM.alphabets]

private theorem sum_header_pages {base scalar vector menu tree L V A T stride : ℕ}
    (header : scalar ≤ base+L*stride) (vectors : vector ≤ scalar+V) (menus : menu ≤ vector+V+A)
    (trees : tree ≤ menu+T*stride) (positive : 0 < stride) : tree ≤ base+(L+2*V+A+T)*stride := by
  have scale := Nat.le_mul_of_pos_right (2*V+A) positive
  rw [show L+2*V+A+T=L+(2*V+A)+T by omega,Nat.add_mul,Nat.add_mul]
  omega

set_option cleanup.letToHave false in
set_option maxHeartbeats 500000 in
theorem economic_header_linear (width : joint.cap*joint.width+1≤2^z) :
    (economicHeader F s t c joint catalogue G finish price R S Q T).stop≤
      joint.initial+economicFactor F s t c joint finish price R S*2^z := by
  let v:=innerVector F s joint c finish price R S Q T
  let m:=menuPages F s t v.stop R S (DeadlineROM.prices c finish price)
  let origin:=menuPages F s t 0 R S (DeadlineROM.prices c finish price)
  let V:=vectorCharge N k depth (DeadlineROM.count c) R S
  let Z:=2*(origin.leftAlphabet.radix+1)+2*(origin.rightAlphabet.radix+1)
  let L:=headerFactor s joint c
  let Zt:=treePagesFactor c d k s.sampler.degree depth
  have lower:=header_bound s joint c finish price width
  have vectors:=(vector_layout F s joint c finish price R S Q T).2.2
  have lookup:=menu_charged F s t c finish price R S v.stop
  have trees:=treePages_bound s c catalogue G F m.stop
  change (boughtPage s c catalogue G F m.stop).stop≤joint.initial+(L+2*V+Z+Zt)*2^z
  change (priceTable s joint c finish price).stop≤joint.initial+L*2^z at lower
  change v.stop≤(priceTable s joint c finish price).stop+V at vectors
  change m.stop ≤ v.stop+V+(2*(m.leftAlphabet.radix+1)+2*(m.rightAlphabet.radix+1)) at lookup
  have space : 2*(m.leftAlphabet.radix+1)+2*(m.rightAlphabet.radix+1) = Z :=
    menu_alphabet_space F s t c finish price R S v.stop
  exact sum_header_pages lower vectors (lookup.trans_eq (congrArg (fun n=>v.stop+V+n) space)) trees
    (Nat.two_pow_pos z)

theorem economic_word_room (core : ℕ) (width : joint.cap*joint.width+1≤2^z)
    (initial : joint.initial≤heapEnd z d copies+core*2^z)
    (enough : core+economicFactor F s t c joint finish price R S+1≤2^z) :
    (economicHeader F s t c joint catalogue G finish price R S Q T).stop<2^wordBits z d copies := by
  apply (economic_header_linear F s t c joint catalogue G finish price R S Q T width).trans_lt
  apply lt_of_le_of_lt _ (append_room enough)
  rw [Nat.add_mul]
  omega

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
