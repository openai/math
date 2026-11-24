import OAI.Computability.VPVNP.PairShrinkRoleScheduledSuffix
import OAI.Computability.VPVNP.PairShrinkRoleParsed

/-!
# Typed resident actions for the parsed raw field lists

The old children and hidden rows have unique typed encodings. A list of
resident actions may therefore be indexed by the physical readers' outputs.
On every completed parse the recovered values are exactly the supplied fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM Compression Compression.ShrinkMotif NetworkKernel CompressorRecords
open NodeArguments NodeArguments.ChildScan ShrinkHiddenSlots ShrinkHiddenGuess LocalHistory
open private ChildArguments.children_injective from OAI.Computability.VPVNP.PairShrinkRoleChildTyped

variable {α β : Type*}

open Classical in
/-- Decode a value in the image of a fixed injective encoding. The default only
serves to define a total indexing function outside that image. -/
noncomputable def recover (encode : α → β) (base : α) (y : β) : α :=
  if h : ∃ x, encode x = y then h.choose else base

theorem recover_encode (encode : α → β) (inj : Function.Injective encode) (base x : α) :
    recover encode base (encode x) = x := by
  have h : ∃ z, encode z = encode x := ⟨x, rfl⟩
  rw [recover, dite_eq_left h]
  exact inj h.choose_spec

variable {R : Type*} {a g : ℕ} (X : State a (packingLaneBits a g))
  {term : Term R X.network} (v : term.output.Site) (ord : Order (term.Preimage v))

/-- Recover the old placement from the child list in descriptor order. -/
noncomputable def oldFields (xs : List (Child X)) : Placed term.place X.network.Half v :=
  recover (children X v ord) (fun _ _ => (fun _ _ _ => false, fun _ _ _ => false)) xs

theorem oldFields_encoded (h : Placed term.place X.network.Half v) :
    oldFields X v ord (children X v ord h) = h :=
  recover_encode _ (ChildArguments.children_injective v ord) _ h

theorem children_oldFields (xs : List (Child X))
    (order : xs.map Child.site = List.ofFn fun j => (ord.entries j).val) :
    children X v ord (oldFields X v ord xs) = xs := by
  obtain ⟨h, rfl⟩ := exists_placed X v ord xs order
  rw [oldFields_encoded]

variable (layout : Bool) (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
  (site : (X.Base × BitWord (Shrink.J a)) × BitWord g)

local notation "rowsAt" => ShrinkHiddenSlots.rows X layout widths site
local notation "Hidden" => Placed (X.packingData.shrinkInternalOwner layout)
  (internalLabel widths layout) site

private theorem rows_injective : Function.Injective (rowsAt) := by
  intro h k eqn
  exact (rows_prefix_unique X layout widths site h k [] [] (eqn ▸ rfl)).1

/-- Recover the absorbed half-wire fields from their dense IDs and little-endian bits. -/
noncomputable def hiddenFields (seed : Hidden) (es : List Row) : Hidden :=
  recover (rowsAt) seed es

theorem hiddenFields_encoded (seed h : Hidden) :
    hiddenFields X layout widths site seed (rowsAt h) = h :=
  recover_encode _ (rows_injective X layout widths site) seed h

variable {w n : ℕ}

/-- A successful native hidden parse is always in the image of the typed encoding. -/
theorem rows_hiddenFields (arg : Args w) (m : Memory w) (seed : Hidden) (es : List Row)
    (node : Word w) (parsed : Parsed (n := n) (hiddenReader arg m (rowsAt seed)) node es) :
    rowsAt (hiddenFields X layout widths site seed es) = es := by
  obtain ⟨s, bits, out, tail, hit, rfl⟩ := parsed
  obtain ⟨h, eqn, _⟩ := (hiddenReader_typed X layout widths site arg m seed hit).exists
  rw [eqn, hiddenFields_encoded]

/-- Run the same resident calls when the physical interface provides raw lists. -/
noncomputable def typedActions (seed : Hidden)
    (bank : Placed term.place X.network.Half v → Hidden → List (ResidentMapLoop.Exact.Action w n))
    (xs : List (Child X)) (es : List Row) : List (ResidentMapLoop.Exact.Action w n) :=
  bank (oldFields X v ord xs) (hiddenFields X layout widths site seed es)

theorem typedActions_encoded (seed : Hidden)
    (bank : Placed term.place X.network.Half v → Hidden → List (ResidentMapLoop.Exact.Action w n))
    (old : Placed term.place X.network.Half v) (hidden : Hidden) :
    typedActions X v ord layout widths site seed bank (children X v ord old) (rowsAt hidden) =
      bank old hidden := by
  simp only [typedActions, oldFields_encoded, hiddenFields_encoded]

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
