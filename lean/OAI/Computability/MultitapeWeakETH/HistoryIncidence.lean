import OAI.Computability.MultitapeWeakETH.HistoryLayout

/-! # Recovering the input incidence and size of every selected pass -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open VPVNP Compression CompressorRecords DescriptorSpace DyadicBudget BurstRAM PairSimulation LocalHistory
open private field_address from OAI.Computability.VPVNP.PairNodeChildPublishedDirectory
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels
open scoped Fin.CommRing
noncomputable section

variable {k R : Type} [Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
  {f : B.Entry → R} {hf : B.IsSolution f}

private theorem within_levels {a g b l P M : ℕ} {X : State a g} (E : StateExecution R b l X)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) (o : PassOrigins B f hf E) (z : E.Choices)
    (h : PrefixLevelScale.Within P M E) :
    ∀ v ∈ collectLevels B f hf E W r o z, v.input.positions ≤ P ∧ v.input.maxWireWidth ≤ M := by
  induction E with
  | done => simp [collectLevels]
  | more p next ih =>
    intro v member
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨h.1,h.2.1⟩
    · exact ih z.1 (W.2 z.1) (r.2 z.1) (o.2 z.1) z.2 (h.2.2 z.1) v tail

theorem history_size {s : ℕ} (hs : 1 ≤ s)
    (z : (B.execute f hf s (lanes_fit B s) (source B s)).Choices)
    (v : SelectedLevel B f hf) (member : v ∈ executeLevels B f hf s (lanes_fit B s) (source B s) z) :
    v.input.positions ≤ (source B s).positions ∧ v.input.maxWireWidth ≤ scale B s :=
  within_levels _ _ _ _ z (within B f hf hs) v member

variable {w : ℕ} {workspace : Word w} {positions blocks n i : ℕ} {v : SelectedLevel B f hf} {m : Memory w}
local notation "L" => BlockProgram.layout B workspace.val positions blocks
local notation "T" => packedIncidence L w i (v.input.positions*2^v.inputExponent)

attribute [local irreducible] BlockProgram.script BlockProgram.layout

/-- The stored degree, inverse-column and width-column pointers, together with correctness
of the data at those pointers, for the input state of this particular selected pass. -/
theorem history_incidence (h : CompiledResident.payload B f hf workspace positions blocks n i v m) :
    m (levelStart L i+16) = ((2^v.inputExponent : ℕ) : Word w) ∧
    m (levelStart L i+19) = (T).actualIn ∧ m (levelStart L i+20) = (T).width ∧ (T).ActualColumns v.input m := by
  have d := CompiledResident.child_directory h
  have fields := d.bank (m (levelStart L i+14)).val (Fin.cast_val_eq_self _).symm
  have deg := fields 2
  have inv := fields 5
  have wid := fields 6
  rw [field_address _ d.room 2] at deg
  rw [field_address _ d.room 5] at inv
  rw [field_address _ d.room 6] at wid
  refine ⟨deg,inv,wid,?_⟩
  obtain ⟨a,g,b,l,X,p,o,c,bits⟩ := v
  cases o with
  | shrink j eq X =>
    subst eq
    have num : DemandRAM.oldCount X = X.positions*2^(ShrinkBlockInputs.a j) := by
      rw [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv _),Fintype.card_fin]
    exact num ▸ ((CompiledResident.shrink_payload ..).mp h).sources.old.incidence
  | refresh X => exact ((CompiledResident.refresh_payload ..).mp h).sources.old.actual

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
