import OAI.Hierarchy.ProtocolRAMAdviceLocal
import OAI.Hierarchy.ProtocolRAMCalendarChargePages
import OAI.Hierarchy.ProtocolRAMCalendarEconomicHeader

namespace OAI
/-! # The public economic tables have no cross-address dependencies on the private input -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {w z d N k phases steps X Y jobs : ℕ}

attribute [local irreducible] AdviceLocal

theorem PortROM.Table.words_local (t : PortROM.Table jobs) : AdviceLocal (t.words (w:=w)) := by
  unfold PortROM.Table.words
  apply AdviceLocal.run
  intro i
  unfold StockCommit.PortHeader.load RepairHistogram.pairAdvice
  exact (AdviceLocal.fill _ _ _).comp ((AdviceLocal.fill _ _ _).comp
    ((AdviceLocal.fill _ _ _).comp (AdviceLocal.fill _ _ _)))

theorem ScalarROM.Table.words_local (t : ScalarROM.Table phases) : AdviceLocal (t.words (w:=w)) := by
  unfold ScalarROM.Table.words
  apply AdviceLocal.run
  intro i
  exact AdviceLocal.fill _ _ _

theorem DiscrepancyROM.Table.words_local {D : ℕ} (t : DiscrepancyROM.Table phases D) :
    AdviceLocal (t.words (w:=w)) := AdviceLocal.fill _ _ _

theorem StripChart.EconomicHeader.vector_local (e : StripChart.EconomicHeader phases X Y steps) :
    AdviceLocal (e.vectorMemory (w:=w)) :=
  e.bought.words_local.comp (e.payload.words_local.comp (e.menus.rightAlphabet.words_local.comp
    (e.menus.leftAlphabet.words_local.comp (e.menus.right.words_local.comp (e.menus.left.words_local.comp
      (e.boughtTree.words_local.comp e.payloadTree.words_local))))))

theorem MenuROM.Charges.words_local (p : MenuROM.Charges) : AdviceLocal (p.words (w:=w)) :=
  p.purchase.words_local.comp p.payload.words_local

theorem GlobalTests.all_local (l : GlobalTests.Layout) (phase : Fin phases→PhasePrice) :
    AdviceLocal (GlobalTests.allPages l z N k phase (w:=w)) := by
  unfold GlobalTests.allPages
  apply AdviceLocal.run
  intro i
  exact AdviceLocal.fill _ _ _

theorem JointHeader.words_local (b : JointHeader.Board) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) : AdviceLocal (JointHeader.words b z d N k phase π stock) := by
  have permutation : AdviceLocal (Boot.permutationWords (d:=d) π) := by
    unfold AdviceLocal
    intro m n x h
    simp only [Boot.permutationWords,h]
  exact (GlobalTests.all_local _ phase).comp ((AdviceLocal.fill _ _ _).comp
    ((AdviceLocal.fill _ _ _).comp ((AdviceLocal.fill _ _ _).comp permutation)))

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
