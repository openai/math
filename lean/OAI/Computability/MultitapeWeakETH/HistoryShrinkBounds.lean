import OAI.Computability.MultitapeWeakETH.ShrinkSiteArguments
import OAI.Computability.MultitapeWeakETH.HistoryCapacity
import OAI.Computability.MultitapeWeakETH.ShrinkHiddenCapacity

/-! # Uniform operand bounds for shrinking occurrences in the sparse history -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open VPVNP Compression Compression.ShrinkMotif BurstRAM CompressorRecords PairSimulation LocalHistory
open DyadicBudget ShrinkBlockInputs TraversalRows TraversalRoles ShrinkMap ShrinkRole Filter
open scoped Classical Fin.CommRing
noncomputable section

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
  (f : B.Entry → R) (hf : B.IsSolution f)

attribute [local irreducible] source scale executeLevels

/-- A single threshold for the grid suffices for every shrinking stage, site,
selection, and chronological occurrence, including both adjacent packet arenas. -/
theorem history_shrink_bounds : ∀ᶠ s : ℕ in atTop,
    let X := source B s
    let n := scale B s
    let w := CursorBounds.wordBits 1 n
    ∀ (path : (B.execute f hf s (lanes_fit B s) X).Choices) (i : Fin S.steps) {g : ℕ}
      (z : SiteArguments B i g) (selector : List Bool),
      shrinkLevel B f hf i z.state z.choice selector ∈ executeLevels B f hf s (lanes_fit B s) X path →
      ∀ (cur : ℕ) (m : Memory w),
        CompiledResident.ShrinkPayload B (0 : Word w) X.positions s n cur i z.state z.choice m →
        z.Ready (⟨0,X.positions,s,n,cur,m⟩ : Level w) := by
  have cube : PolynomiallyBounded (fun n : ℕ => 2*n*n*n) :=
    (((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).mul PolynomiallyBounded.id).mul PolynomiallyBounded.id
  obtain ⟨N,room⟩ := eventually_atTop.mp (CursorRAM.eventual_word_room 1 le_rfl cube)
  filter_upwards [eventually_ge_atTop 1,eventually_ge_atTop (slotDegree S),
    eventually_ge_atTop (2*fieldFactor B.shrink),eventually_ge_atTop N] with s hs hd factor fit
  intro X n w path i g z selector member cur m stored
  let V := shrinkLevel B f hf i z.state z.choice selector
  obtain ⟨pos,wide⟩ := history_size hs path V member
  have next := (history_output_size hs path V member).2
  have size : s ≤ n := scale_ge B s
  have degree := V.oldDegree_le.trans (hd.trans size)
  have nextDegree := V.outputDegree_le.trans (hd.trans size)
  refine ⟨stored,pos.trans (source_positions B hs),degree,nextDegree,wide,next,?_,hs.trans size,room n (fit.trans size)⟩
  change fieldFactor B.shrink * (z.state.maxWireWidth+1) ≤ n*n
  change z.state.maxWireWidth ≤ n at wide
  calc
    _ ≤ fieldFactor B.shrink * (2*n) := Nat.mul_le_mul_left _ (by omega)
    _ = (2*fieldFactor B.shrink)*n := by ring
    _ ≤ n*n := Nat.mul_le_mul_right _ (factor.trans size)

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
