import OAI.Computability.MultitapeWeakETH.ShrinkMapEntry
import OAI.Computability.MultitapeWeakETH.ShrinkDemandInputs
import OAI.Computability.MultitapeWeakETH.ShrinkSupplyInputs
import OAI.Computability.MultitapeWeakETH.ResidentResults

/-! # Checking every resident map of a selected shrinking site on tape -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open CompressorRecords PairSimulation ShrinkBlockInputs MapResidentRows LocalHistory MotifConversion
open scoped Classical Fin.CommRing
noncomputable section

set_option allowUnsafeReducibility true in
attribute [local reducible] Compression.PackingData.shrinkTermLayout
set_option allowUnsafeReducibility true in
attribute [local irreducible] Compression.ShrinkEnergy.chosenLayout

variable {D k : Type} [Codec D] [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  (i : Fin S.steps) (read : D × Bits.Word → Bits.Word) (hr : Poly read)
  (number : (parameterData B.shrink).Entry → ℕ)

include hr

set_option maxHeartbeats 1400000 in
/-- One tape program evaluates any occurrence in the selected row, including the
map's failure case and its list of repeated template labels. -/
theorem occurrence_program :
    ∃ run : ShrinkHidden.Indexed (Buffers D) → Option (List Tally), Poly run ∧
      ∀ {g w : ℕ} (ctx : D) (z : SiteArguments B i g) (d : Level w) (j : z.Row),
      z.Ready d → (∀ p : Word w, read (ctx,wordBits p) = wordBits (d.memory p.val)) →
      run (z.query d ctx j) = (ShrinkRole.MapWitness.names B (z.input j)).map (List.map (tally ∘ number)) := by
  obtain ⟨getD,hd,vd⟩ := demand_programs B i read hr
  obtain ⟨getS,hs,vs⟩ := supply_programs B i read hr
  obtain ⟨run,cost,ev⟩ := entry_program B i (external read) (external_poly hr) getD getS hd hs number
  refine ⟨run,cost,?_⟩
  intro g w ctx z d j ready rd
  obtain ⟨outD,inD⟩ := vd ctx z d j ready rd
  obtain ⟨outS,inS⟩ := vs ctx z d j ready rd
  exact ev (z.buffers ctx w) z.state z.choice d.base d.positions d.blocks d.n d.cur (d.n*d.n) d.memory
    z.owner j (z.input j) rd ready.data rfl rfl rfl (z.space d ready).2.2.2.1 ready.factor
    (z.space d ready).2.2.2.2 outD inD outS inS

/-- The directory's fixed row capacity makes the complete site check a single
polynomial program, uniformly over sizes, placements, and private assignments. -/
theorem site_program :
    ∃ run : ShrinkHidden.Query (Buffers D) → Option (List Tally), Poly run ∧
      ∀ {g w : ℕ} (ctx : D) (z : SiteArguments B i g) (d : Level w), z.Ready d →
      (∀ p : Word w, read (ctx,wordBits p) = wordBits (d.memory p.val)) →
      run (ShrinkHidden.query (z.buffers ctx w) (d.head B) (d.n*d.n) (siteIndex z.state z.owner).val) =
        checked (z.results number) := by
  obtain ⟨run,cost,ev⟩ := occurrence_program B i read hr number
  refine ⟨fun q => checked (rowsAt (capacity (a i)) run q),(rowsAt_poly _ run cost).compose checked_poly,?_⟩
  intro g w ctx z d ready rd
  apply congrArg checked
  unfold rowsAt
  rw [← length_eq z.state (SelectedFinish.chosen B z.state z.choice) z.owner]
  exact congrArg List.ofFn (funext fun j => ev ctx z d j ready rd)

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
