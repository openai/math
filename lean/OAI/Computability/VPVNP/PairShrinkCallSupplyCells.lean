import OAI.Computability.VPVNP.PairShrinkCallFields
import OAI.Computability.VPVNP.PairShrinkSurvivingOperands
import OAI.Computability.VPVNP.PairShrinkHiddenSlots
import OAI.Computability.VPVNP.LiveHeaderBits

/-!
# Supply bits of a shrinking map in the caller's private memory

An incident port is either an absorbed wire shared between its two resident
maps or a surviving wire assembled from the independently stored half-wire
of the current output vertex. Reading its own physical field yields the
payload bits followed by the selector bits of the selected matrix column.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallSupplyCells

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel MotifEntry ShrinkCallFields
open scoped Fin.CommRing
open private readSupplyEnd layoutCases_absorbed from OAI.Computability.VPVNP.ShrinkSupplyLocal

variable {a b g w pad : ℕ} (X : State a (packingLaneBits a g))
variable (layout : Bool) (subdiv : Fin 4 → ℕ)
variable (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
variable {next : Equiv.Perm (X.Base × BitWord (packingTagBits (2 ^ a)))}
variable (I : X.packingData.ShrinkIndex layout subdiv next (2 ^ b) pad) (hpos : ∀ t, 0 < subdiv t)
variable (m : X.packingData.Motif) (j : Fin 6)
local notation "W" => fun m t ↦ widths m (layout, t)
local notation "Idx" => Fin.val (CompressorRecords.ShrinkMotifOrder.stateNumber X m)

variable (s : Scratch)
variable (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel widths layout)
  (X.packingData.shrinkPartySite layout m j))
variable (z : (X.shrinkOutputState layout subdiv (fun m t ↦ widths m (layout, t)) I).network.Half
  (X.packingData.shrinkPartySite layout m j))

/-- The assembled private field agrees pointwise with the reverse copies from
the new vertex. Each right-hand side uses its own actual source or target half. -/
def Retained (before after : Word w → Word w) : Prop :=
  ∀ dir t (party : j = ShrinkSurvivingOperands.party layout t dir),
    let site := (congrArg (X.packingData.shrinkPartySite layout m) party).trans
      (ShrinkSurvivingOperands.party_site X layout m t dir)
    let halves : (X.shrinkOutputState layout subdiv (fun m t ↦ widths m (layout, t)) I).network.Half
        (ShrinkSurvivingOperands.site X layout m t dir) :=
      ⟨fun e he ↦ z.1 e (site.trans he), fun e he ↦ z.2 e (site.trans he)⟩
    let dst := s.surviving dir t
    ∀ i : Fin (widths m (layout, t)), after ((dst + i.val : ℕ) : Word w) =
      ShrinkSurvivingOperands.nativeFill X layout subdiv (W) I m t dir halves dst before
        ((dst + i.val : ℕ) : Word w)

/-- The once-guessed field at its absolute ID survives every assembly copy. -/
def Absorbed (after : Word w → Word w) : Prop :=
  ∀ t (owned : X.packingData.shrinkPartySite layout m j =
        X.packingData.shrinkInternalOwner layout (m, t))
    (i : Fin (widths m (!layout, t))),
    after ((s.shared Idx t + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w (RAMSerialization.wordBits _ (h (m, t) owned) i)

private theorem input_bit {n : ℕ} (x : Fin (2 ^ n)) (i : Fin n) :
    inputBits x i = RAMSerialization.wordBits n x i := LiveHeader.testBit_wordBits _ _

variable (before after : Word w → Word w)
variable (hidden : Absorbed X layout widths m j s h after)
variable (retained : Retained X layout subdiv widths I m j s z before after)
variable (room : ∀ dir t, s.surviving dir t + widths m (layout, t) ≤ 2 ^ w)

include retained room in
private theorem retained_cell (t : Fin 4) (dir : Bool)
    (party : j = ShrinkSurvivingOperands.party layout t dir) (i : Fin (widths m (layout, t))) :
    after ((s.surviving dir t + i.val : ℕ) : Word w) = PrivateFields.bitValue w
      (inputBits (ShrinkSurvivingOperands.mapColumn X layout subdiv I hpos m t widths dir
        (party ▸ h) (party ▸ z)) i) := by
  subst j
  rw [input_bit]
  exact (retained dir t rfl i).trans
    (ShrinkSurvivingOperands.nativeFill_mapColumn X layout subdiv I hpos m t widths dir h z
      (s.surviving dir t) before (room dir t) i)

/-- Select one actual source or target coordinate from the six-party matrix column. -/
noncomputable def word (dir : Bool) (e : Bool × Fin 4) (p : j = supplyParty dir e) :
    Fin (2 ^ widths m e) :=
  match dir with
  | false => (X.packingData.shrinkLocalSupplyArg layout subdiv widths I hpos m j h z).1 e p
  | true => (X.packingData.shrinkLocalSupplyArg layout subdiv widths I hpos m j h z).2 e p

include hidden retained room in
theorem read (cd : Bool → ℕ) (dir : Bool) (e : Bool × Fin 4) (party : j = supplyParty dir e)
    (i : Fin (widths m e)) :
    after ((s.fieldBase Idx j layout cd (.inr (dir, e)) + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w
        (inputBits (word X layout subdiv widths I hpos m j h z dir e party) i) := by
  rcases e with ⟨l,t⟩
  by_cases active : l = layout
  · subst l
    rw [Scratch.fieldBase, ite_eq_left party, ite_eq_left rfl]
    have hp : j = ShrinkSurvivingOperands.party layout t dir := by cases dir <;> exact party
    have hh := retained_cell X layout subdiv widths I hpos m j s h z before after retained room
      t dir hp i
    subst j
    cases dir <;> exact hh
  · have he : l = !layout := Bool.eq_not_of_ne active
    subst l
    rw [Scratch.fieldBase, ite_eq_left party, ite_eq_right active]
    subst j
    rw [input_bit]
    cases dir <;> simp only [word, supplyParty,
      shrinkLocalSupplyArg, readSupplyEnd, layoutCases_absorbed] <;> apply hidden


end PairSimulation.ShrinkCallSupplyCells

end VPVNP
end Computability
end OAI
