import OAI.Hierarchy.DescentPackedCensusRAM
import OAI.Hierarchy.DescentPackedMinimumAny
import OAI.Hierarchy.DescentPackedPhase

namespace OAI
/-! # Fixed execution time of the five chooser phases on arbitrary packed words -/
namespace Hierarchy.DescentPackedColony.Phase
open DescentColonies DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {k D b M H G w : ℕ}

theorem any (L : Shelves k D) (space : Space L w H G b M) (m : Memory w) :
    ∃out,(program L w H G M).Exec m out (cost L w H G M) := by
  let trials:=AllSeeds.search w H G M k L.layers
  let test:=fun i=>AllSeeds.trial w H G M k (L.layers i)
  have evaluated (i) : (test i).exec:=fun mem=>(DescentPackedColony.physical (L.layers i) (space.trials.hardware i) mem).1
  have scored : trials.exec := NativeBatch.Code.exec_seqAll test evaluated (2^k-1) le_rfl
  obtain ⟨m₁,first⟩:=DescentPackedMinimum.any L.split space.split (trials.after m)
  have panel (i) : (L.panels i).Fits w L.split.work := (space.splitPanel i) ▸ space.split.source i
  have accessible (i) : (L.panels i).Fits w L.selected :=
    ⟨(panel i).1,(panel i).2.1,(panel i).2.2.trans space.zipAbove⟩
  let n:=H*chunks G M
  let m₂:=image L.selected n L.field m₁
  have picked : (scan w L.selected n L.field).Exec m₁ m₂ (4+n*(2*L.field.work+4)) :=
    @scan_exec w L.selected n L.field m₁
    (chosen_fits L.mu L.selected L.panels L.amount L.zip space.zipKey accessible space.countFit space.zipRoom) space.zipEnd
  obtain ⟨m₃,second⟩:=DescentPackedMinimum.any L.color space.color m₂
  let emit:=PackedWinnerRAM.program k w L.paintTable L.output H G M L.mu L.paint L.panels
  have emitted : emit.exec := PackedWinnerRAM.exec space.final
  refine ⟨emit.after m₃,?_⟩
  dsimp only [program,cost]
  rw [← chosen_work L.mu L.panels L.amount L.zip]
  exact Procedure.Exec.then
    (Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then (@scored m) (@first)) (@picked)) (@second))
    (@emitted m₃)

end
end Hierarchy.DescentPackedColony.Phase

namespace Hierarchy.DescentSixParty.PackedCensus
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
variable {a b w lo hi H G M : ℕ}
theorem any (first second : Banks) (f : Fits first a b M H G w lo) (g : Fits second a b M H G w hi) (m : Memory w) :
    ∃out,(histograms first second lo hi H G M w).Exec m out (clocks first second H G M) := by
  let rows := H * chunks G M
  let mid := image lo rows (lookup first) m
  let out := image hi rows (lookup second) mid
  have f₁ : (lookup first).Fits w lo := ⟨⟨f.dictionary,f.source,trivial⟩,f.mask,trivial⟩
  have f₂ : (lookup second).Fits w hi := ⟨⟨g.dictionary,g.source,trivial⟩,g.mask,trivial⟩
  exact ⟨out, @Procedure.Exec.then w (scan w lo rows (lookup first)) (scan w hi rows (lookup second))
    m mid out (4+rows*(2*(lookup first).work+4)) (4+rows*(2*(lookup second).work+4))
    (@scan_exec w lo rows (lookup first) m f₁ f.output)
    (@scan_exec w hi rows (lookup second) mid f₂ g.output)⟩
end Hierarchy.DescentSixParty.PackedCensus

end OAI
