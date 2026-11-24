import OAI.Computability.VPVNP.MacaulayPairEntries
import OAI.Computability.VPVNP.RankQueryGramReadSpace

/-! # Dynamic inputs to the powered target row

The enclosing coordinate query stages the source monomial ordinal, the
marked variable, and the power scale. The other monomial address is the
column requested by the scalar reader. The auxiliary bank also retains
encoded constants zero and one.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.TargetRead

open RAMTape UniversalCountStack RadicalCertificate.MonomialIndex

/-- Additional powered-reader ports for the encoded zero and one scalars and a temporary stack. -/
inductive Extra where
  | constant (b : Bool) | tmp
  deriving DecidableEq, Fintype

/-- Private workspace combining the monomial pair scan, two scalar literals and a temporary
stack. -/
abbrev Work := PairCall.Port ⊕ Extra
set_option synthInstance.maxSize 2500 in
instance : DecidableEq Work := inferInstanceAs (DecidableEq (PairCall.Port ⊕ Extra))

/-- Matrix entry interface whose auxiliary stacks run the powered target scan. -/
abbrev Port := MacaulayRead.Port Work

/-- Workspace address holding the source monomial's ordinal in the pair scan. -/
def sourcePort : Work := .inl (.external (.ordinal false))
/-- Workspace address holding the one-based variable mark, with zero denoting an unmarked
target. -/
def markPort : Work := .inl (.external .mark)
/-- Workspace address holding the exponent scale used by the powered monomial test. -/
def scalePort : Work := .inl (.external .scale)
/-- Reader address of the equality flag produced by the powered monomial scan. -/
abbrev flagPort : Port := .aux (.inl (.external .flag))

/-- The full flag word belongs to the powered scan until the scalar copy
has completed. The caller's column is the only aliased pair-scan port. -/
def storage (w : ℕ) (d : PairCall.Inputs) (constants : Bool → List Bool) (flag : List Bool) : Stacks Work
  | .inl (.external (.ordinal true)) => []
  | .inl p => PairCall.publicBank w d (fun _ => []) [] flag p
  | .inr (.constant b) => constants b
  | .inr .tmp => []

/-- Initial powered-reader bank with the supplied scalar literals and an empty result flag. -/
def bank (w : ℕ) (d : PairCall.Inputs) (constants : Bool → List Bool) : Stacks Work :=
  storage w d constants []

/-- Updates the source ordinal, power scale and variable mark while preserving the column
ordinal and degree bounds. -/
def setDynamic (d : PairCall.Inputs) (source scale mark : ℕ) : PairCall.Inputs :=
  {d with ordinal := fun b => if b then d.ordinal true else source, scale := scale, mark := mark}

/-- The staging slots, in source ordinal, marked variable, and scale order. -/
def slot : Fin 3 ↪ Work :=
  ⟨![sourcePort, markPort, scalePort], by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

/-- The three fixed-width staging words, ordered as source ordinal, variable mark and exponent
scale. -/
def words (w source scale mark : ℕ) : Stacks (Fin 3) :=
  ![digits w source, digits w mark, digits w scale]

/-- Powered-reader template with the three dynamic argument stacks emptied for staging. -/
noncomputable def blankDynamic (w : ℕ) (d : PairCall.Inputs) (constants : Bool → List Bool) : Stacks Work :=
  installStacks slot (bank w d constants) (fun _ => [])

private theorem updated_outside (w : ℕ) (d : PairCall.Inputs) (constants : Bool → List Bool)
    (source scale mark : ℕ) (p : Work) (outside : ∀ i, slot i ≠ p) :
    bank w (setDynamic d source scale mark) constants p = bank w d constants p := by
  rcases p with (f | k | _) | e
  · cases f with
    | ordinal b => cases b <;> first | rfl | exact (outside 0 rfl).elim
    | mark => exact (outside 1 rfl).elim
    | scale => exact (outside 2 rfl).elim
    | _ => rfl
  · rfl
  · rfl
  · cases e <;> rfl

theorem stage_dynamic (w : ℕ) (d : PairCall.Inputs) (constants : Bool → List Bool) (source scale mark : ℕ) :
    installStacks slot (bank w d constants) (words w source scale mark) =
      bank w (setDynamic d source scale mark) constants := by
  apply installStacks_frame slot.injective (fun i => by fin_cases i <;> rfl)
    (updated_outside w d constants source scale mark)

theorem stage_blankDynamic (w : ℕ) (d : PairCall.Inputs) (constants : Bool → List Bool) (source scale mark : ℕ) :
    installStacks slot (blankDynamic w d constants) (words w source scale mark) =
      bank w (setDynamic d source scale mark) constants := by
  apply installStacks_frame slot.injective (fun i => by fin_cases i <;> rfl)
  intro p hp
  rw [updated_outside w d constants source scale mark p hp, blankDynamic, installStacks_outside _ _ hp]

end RankQuery.Stack.Coordinate.TargetRead

end VPVNP
end Computability
end OAI
