import OAI.Hierarchy.DescentPackedCensusRAM
import OAI.Hierarchy.DescentPackedMinimumAnyFrame
import OAI.Hierarchy.DescentPackedPhase

namespace OAI
/-! # Fixed execution time of the five chooser phases on arbitrary packed words -/
namespace Hierarchy.DescentPackedColony.Phase
open DescentColonies DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {k D b M H G w : ℕ}

theorem any_framed (L : Shelves k D) (space : Space L w H G b M) (m : Memory w) :
    ∃out,(program L w H G M).Exec m out (cost L w H G M) ∧
      ∀z,z<L.first ∨ L.output+2^k*(H*chunks G M)≤z → out z=m z := by
  let trials:=AllSeeds.search w H G M k L.layers
  let test:=fun i=>AllSeeds.trial w H G M k (L.layers i)
  have evaluated (i) : (test i).exec:=fun mem=>(DescentPackedColony.physical (L.layers i) (space.trials.hardware i) mem).1
  have scored : trials.exec := NativeBatch.Code.exec_seqAll test evaluated (2^k-1) le_rfl
  obtain ⟨m₁,first,firstFrame⟩:=DescentPackedMinimum.any_framed L.split space.split (trials.after m)
  have panel (i) : (L.panels i).Fits w L.split.work := (space.splitPanel i) ▸ space.split.source i
  have accessible (i) : (L.panels i).Fits w L.selected :=
    ⟨(panel i).1,(panel i).2.1,(panel i).2.2.trans space.zipAbove⟩
  let n:=H*chunks G M
  let m₂:=image L.selected n L.field m₁
  have picked : (scan w L.selected n L.field).Exec m₁ m₂ (4+n*(2*L.field.work+4)) :=
    @scan_exec w L.selected n L.field m₁
    (chosen_fits L.mu L.selected L.panels L.amount L.zip space.zipKey accessible space.countFit space.zipRoom) space.zipEnd
  obtain ⟨m₃,second,secondFrame⟩:=DescentPackedMinimum.any_framed L.color space.color m₂
  let emit:=PackedWinnerRAM.program k w L.paintTable L.output H G M L.mu L.paint L.panels
  have emitted : emit.exec := PackedWinnerRAM.exec space.final
  refine ⟨emit.after m₃,?_,?_⟩
  · dsimp only [program,cost]
    rw [← chosen_work L.mu L.panels L.amount L.zip]
    exact Procedure.Exec.then
      (Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then (@scored m) (@first)) (@picked)) (@second))
      (@emitted m₃)

  · intro z outside
    have selectedEnd : L.selected+n ≤ L.color.work := space.afterZip
    have colorLedger := space.color.ledger.2.2
    have colorWork := space.color.workspace
    have oldWork := space.previous
    have zipped := space.zipAbove
    have splitEnd : L.split.result+(2^k-1)≤L.selected := by
      have h:=space.zipKey.2.2
      change L.split.result+(2^k-1-1)+1≤L.selected at h
      omega
    have colorEnd : L.color.result+2^(k+1)≤L.output := by
      have h:=space.final.paint
      change L.color.result+(2^(k+1)-1)<L.output at h
      omega
    have colorBeforeOutput : L.color.work ≤ L.output :=
      ((Nat.le_add_right _ _).trans colorWork).trans
        (((Nat.le_add_right _ _).trans colorLedger).trans ((Nat.le_add_right _ _).trans colorEnd))
    have selectedToOutput : L.selected+n ≤ L.output := selectedEnd.trans colorBeforeOutput
    have splitToOutput : L.split.result+(2^k-1) ≤ L.output :=
      splitEnd.trans ((Nat.le_add_right L.selected n).trans selectedToOutput)
    have splitBeforeOutput : L.split.work ≤ L.output :=
      zipped.trans (((Nat.le_add_right _ _).trans selectedEnd).trans colorBeforeOutput)
    rcases outside with hz|hz
    · have old : trials.after m z=m z := by
        apply NativeBatch.Code.frame_seq
        intro i old
        exact below (L.layers i) (space.trials.hardware i) old le_rfl z (hz.trans_le (space.trials.beginAt i))
      have lastRead : emit.after m₃ z=m₃ z :=
        PackedWinnerRAM.frame (lo:=L.paintTable) (out:=L.output) (seed:=L.mu) (paint:=L.paint)
          (source:=L.panels) (M:=M) (G:=G) (H:=H) m₃ z (hz.trans_le (oldWork.trans splitBeforeOutput))
      exact lastRead.trans ((secondFrame z (.inl (by omega))).trans
        ((ProtocolRAMGeneratedWrite.frame_image L.selected n L.field m₁ z (.inl (by omega))).trans
          ((firstFrame z (.inl (by omega))).trans old)))
    · have old:=AllSeeds.frame_above L.layers m
        (fun i d hd=>(space.trialsStop i d hd).trans
          (splitBeforeOutput.trans ((Nat.le_add_right L.output _).trans hz)))
      have lastRead : emit.after m₃ z=m₃ z :=
        PackedWinnerRAM.frame_above (lo:=L.paintTable) (out:=L.output) (seed:=L.mu) (paint:=L.paint)
          (source:=L.panels) (M:=M) (G:=G) (H:=H) m₃ z hz
      have outLe : L.output ≤ z := (Nat.le_add_right L.output _).trans hz
      exact lastRead.trans ((secondFrame z (.inr (colorEnd.trans outLe))).trans
        ((ProtocolRAMGeneratedWrite.frame_image L.selected n L.field m₁ z
          (.inr (selectedToOutput.trans outLe))).trans
          ((firstFrame z (.inr (splitToOutput.trans outLe))).trans old)))

end
end Hierarchy.DescentPackedColony.Phase

namespace Hierarchy.DescentSixParty.PackedCensus
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
variable {a b w lo hi H G M : ℕ}
theorem any_framed (first second : Banks) (f : Fits first a b M H G w lo) (g : Fits second a b M H G w hi) (m : Memory w) :
    ∃out,(histograms first second lo hi H G M w).Exec m out (clocks first second H G M) ∧
      ∀z,(z<lo ∨ lo+H*chunks G M≤z) → (z<hi ∨ hi+H*chunks G M≤z) → out z=m z := by
  let rows := H*chunks G M
  let mid := image lo rows (lookup first) m
  let out := image hi rows (lookup second) mid
  have f₁ : (lookup first).Fits w lo := ⟨⟨f.dictionary,f.source,trivial⟩,f.mask,trivial⟩
  have f₂ : (lookup second).Fits w hi := ⟨⟨g.dictionary,g.source,trivial⟩,g.mask,trivial⟩
  refine ⟨out,@Procedure.Exec.then w (scan w lo rows (lookup first)) (scan w hi rows (lookup second))
    m mid out (4+rows*(2*(lookup first).work+4)) (4+rows*(2*(lookup second).work+4))
    (@scan_exec w lo rows (lookup first) m f₁ f.output)
    (@scan_exec w hi rows (lookup second) mid f₂ g.output),?_⟩
  intro z low high
  exact (ProtocolRAMGeneratedWrite.frame_image hi rows (lookup second) mid z high).trans
    (ProtocolRAMGeneratedWrite.frame_image lo rows (lookup first) m z low)

end Hierarchy.DescentSixParty.PackedCensus

end OAI
