import OAI.Computability.VPVNP.PairShrinkCallFields
import OAI.Computability.VPVNP.CompressorFormulaFootprint

/-!
# External cells used to form a shrinking map descriptor

The selected motif ordinal addresses two demand cells and ten term cells. At each
party the remaining descriptor entries compute private workspace pointers or use the
direct CD pointer for an incident endpoint. This proof checks the nested external
loads in those expressions before the descriptor is written.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkDescriptorReads

open BurstRAM CompressorRecords CompressorRecords.PhaseRecipe Compression ShrinkCallFields
open scoped Fin.CommRing

variable {w a g : ℕ}

private theorem add_val_le (base : Word w) (n : ℕ) :
    (base + (n : Word w)).val ≤ base.val + n := by
  change (base.val + n % 2 ^ w) % 2 ^ w ≤ base.val + n
  exact (Nat.mod_le ..).trans (Nat.add_le_add_left (Nat.mod_le ..) _)

variable {X : State a (packingLaneBits a g)} {m : X.packingData.Motif}
  {pub : Fin 5 → Word w} {state : Word w} {mem : Memory w}
  {I : ShrinkCallFields.Inputs} {s : Scratch} {term dense : Word w}
  {step : ℕ} {layout : Bool} {cd : Bool → ℕ}

local notation "idx" => Fin.val (ShrinkMotifOrder.stateNumber X m)
local notation "ev" => Expr.eval pub state mem

/-- Bounds on the actual level, demand pair and term row suffice for all descriptor
loads. The two CD endpoints can have independently computed addresses. -/
theorem fields (stored : Stored pub state mem X m I s term dense step layout cd) (H : ℕ)
    (levelRead : I.level.ReadsFrom (· < H) pub state mem)
    (levelRoom : (ev I.level).val + 59 < H)
    (ordinalRead : I.ordinal.ReadsFrom (· < H) pub state mem)
    (hiddenRead : I.hidden.ReadsFrom (· < H) pub state mem)
    (strideRead : I.stride.ReadsFrom (· < H) pub state mem)
    (motifsRead : I.motifs.ReadsFrom (· < H) pub state mem)
    (histRead : I.hist.ReadsFrom (· < H) pub state mem)
    (cdRead : ∀ dir, (I.cd dir).ReadsFrom (· < H) pub state mem)
    (termRoom : term.val + idx * step + 9 < H) (denseRoom : dense.val + 2 * idx + 1 < H) :
    I.descriptor.ReadsFrom (· < H) pub state mem ∧
      ∀ party arg, (I.fields party arg).ReadsFrom (· < H) pub state mem := by
  let safe := Expr.ReadsFrom (· < H) pub state mem
  have head (n : ℕ) (hn : n ≤ 59) : safe (I.loadHead n) := by
    refine ⟨⟨levelRead, trivial⟩, ?_⟩
    exact (add_val_le (ev I.level) n).trans_lt (by omega)
  have tr : safe I.term := ⟨head 36 (by decide), ordinalRead, head 37 (by decide)⟩
  let start := term.val + idx * step
  have tv : ev I.term = (start : Word w) := by
    change ev (I.loadHead 36) + ev I.ordinal * ev (I.loadHead 37) = _
    rw [stored.termBase, stored.ordinal, stored.termStride]
    simp only [start, Nat.cast_add, Nat.cast_mul, Fin.cast_val_eq_self]
  have bound : (ev I.term).val ≤ start := tv ▸ Nat.mod_le ..
  have copies : safe I.copies := by
    refine ⟨⟨tr, trivial⟩, ?_⟩
    exact (add_val_le (ev I.term) 1).trans_lt (by change start + 9 < H at termRoom; omega)
  have payload (e : Bool × Fin 4) : safe (I.payload e) := by
    let i := ShrinkSliceArrays.supplyRoles.symm e
    refine ⟨⟨⟨tr, trivial⟩, trivial⟩, ?_⟩
    have first : ((ev I.term) + 2).val ≤ (ev I.term).val + 2 := add_val_le _ 2
    have hi : i.val < 8 := i.isLt
    apply ((add_val_le ((ev I.term) + 2) i.val).trans (Nat.add_le_add_right first i.val)).trans_lt
    change start + 9 < H at termRoom
    omega
  have demand (e : Bool) : safe (I.demand e) := by
    refine ⟨⟨⟨head 47 (by decide), trivial, ordinalRead⟩, trivial⟩, ?_⟩
    change ((ev (I.loadHead 47) + 2 * ev I.ordinal) + (e.toNat : Word w)).val < H
    rw [stored.denseBase, stored.ordinal]
    have pair : dense + 2 * (idx : Word w) = ((dense.val + 2 * idx : ℕ) : Word w) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Fin.cast_val_eq_self]
    rw [pair, ← Nat.cast_add]
    apply (Nat.mod_le ..).trans_lt
    have he : e.toNat ≤ 1 := by cases e <;> decide
    omega
  have staging : safe I.staging := ⟨hiddenRead, ⟨trivial, motifsRead⟩, strideRead⟩
  have shared (t : Fin 4) : safe (I.shared t) :=
    ⟨hiddenRead, ⟨⟨ordinalRead, trivial⟩, trivial⟩, strideRead⟩
  have surviving (dir : Bool) (t : Fin 4) : safe (I.surviving dir t) :=
    ⟨staging, trivial, strideRead⟩
  have directory : safe I.directory := ⟨staging, trivial, strideRead⟩
  have descriptor : safe I.descriptor := ⟨directory, trivial⟩
  have source : safe I.source := ⟨descriptor, trivial⟩
  have select {x y : Expr} (hx : safe x) (hy : safe y) : safe (Inputs.select I.layout x y) :=
    ⟨hy, ⟨hx, hy⟩, head 38 (by decide)⟩
  refine ⟨descriptor, fun j arg => ?_⟩
  cases arg with
  | copies => exact copies
  | hist => exact histRead
  | source => exact source
  | target => exact ⟨source, copies⟩
  | directory => exact directory
  | demand e => exact demand e
  | payload e => exact payload e
  | base f =>
    change safe (I.base j f)
    rcases f with ⟨dir, e⟩ | ⟨dir, side, t⟩
    · rw [Inputs.base]
      split
      · cases e
        · exact staging
        · exact cdRead dir
      · trivial
    · rw [Inputs.base]
      split
      · cases side
        · exact select (shared t) (surviving dir t)
        · exact select (surviving dir t) (shared t)
      · trivial

end PairSimulation.ShrinkDescriptorReads

end VPVNP
end Computability
end OAI
