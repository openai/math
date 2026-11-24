import OAI.Computability.VPVNP.CompressorSelectedPayloadHistory
import OAI.Computability.VPVNP.CompressorSelectedDirectoryEmission
import OAI.Computability.VPVNP.CompressorShrinkSuccessorIndex

/-!
# Reading selected role-specific payloads and successor pitches

The actual scheduled pass determines the type of its selected term.
A shrinking stage always has a successor pass, whose metadata publisher
writes the pitch needed to decode the new-state party operands.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SelectedPayloadHistory

open BurstRAM Compression DescriptorSpace PairSimulation.LocalHistory
open scoped Fin.CommRing

variable {w : ℕ} {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)

/-- Type of predicates relating a selected shrinking term, its tape, and memory at a specified
history level. -/
abbrev Shrinking :=
  ∀ (_level : ℕ) (i : Fin S.steps) {g n : ℕ} (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n),
    (B.shrinkPassAt f hf i h X).step.Choice → List Bool → Memory w → Prop

/-- Type of predicates relating a selected dyadic refresh term, its tape, and memory at a
specified history level. -/
abbrev Refreshing :=
  ∀ (_level : ℕ) {g : ℕ} (X : State S.portExponent (S.portExponent+g)),
    Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 B.refresh → List Bool → Memory w → Prop

variable {B f hf}

private def atOrigin (shrink : Shrinking (w := w) B f hf) (refresh : Refreshing (w := w) B)
    (j : ℕ) {a g b n : ℕ} {X : State a g} {p : StatePass R X b n} :
    PassOrigin B f hf p → p.step.Choice → List Bool → Memory w → Prop
  | .shrink i h Y => shrink j i h Y
  | .refresh Y => refresh j Y

/-- Dispatch the payload predicate on the pass's typed origin. The
constructor exposes the native choice and input state to the producer. -/
def byOrigin (shrink : Shrinking (w := w) B f hf) (refresh : Refreshing (w := w) B) :
    Data (w := w) B f hf :=
  fun j v => atOrigin shrink refresh j v.origin v.term v.selector

theorem byOrigin_shrink (shrink : Shrinking (w := w) B f hf) (refresh : Refreshing (w := w) B)
    (j : ℕ) (i : Fin S.steps) {g n : ℕ} (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) (c : (B.shrinkPassAt f hf i h X).step.Choice)
    (bits : List Bool) (m : Memory w) :
    byOrigin shrink refresh j ⟨_,_,_,_,X,_,.shrink i h X,c,bits⟩ m ↔ shrink j i h X c bits m := Iff.rfl

theorem byOrigin_refresh (shrink : Shrinking (w := w) B f hf) (refresh : Refreshing (w := w) B)
    (j : ℕ) {g : ℕ} (X : State S.portExponent (S.portExponent+g))
    (c : Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (bits : List Bool) (m : Memory w) :
    byOrigin shrink refresh j ⟨_,_,_,_,X,_,.refresh X,c,bits⟩ m ↔ refresh j X c bits m := Iff.rfl

variable {L : Layout} {data : Data (w := w) B f hf} {past : List (SelectedLevel B f hf)} {m : Memory w}

/-- Read any field of an older selected level from its actual published
source record, even if the same level value occurs at multiple ordinals. -/
theorem Past.read_field (h : Past B f hf L data past m) (i : Fin past.length) {field : ℕ}
    {value : Word w} (small : field < levelWords L)
    (published : ∀ source, data i.val past[i] source → source (levelStart L i.val+field) = value) :
    m (levelStart L i.val+field) = value := by
  obtain ⟨source,p,same⟩ := h i
  have span (j : ℕ) : levelStart L (j+1) = levelStart L j+levelWords L := by
    simp only [levelStart,Nat.succ_mul,Nat.add_assoc]
  exact (same _ (Or.inl ⟨Nat.le_add_right ..,by rw [span]; omega⟩)).symm.trans (published source p)

variable {n : ℕ} {T : ℕ} {hT : T*S.laneBits ≤ n} {X : State (S.degreeExponent 0) n}
variable {z : (B.execute f hf T hT X).Choices}
local notation "vs" => executeLevels B f hf T hT X z

/-- The shrink's output-state pitch is read from the next actual pass's
native metadata packet, including across the final shrink of each block. -/
theorem shrink_successor_stride (h : Past B f hf L data vs m) (i : Fin (vs).length)
    (shrink : vs[i].origin.ordinal < S.steps) (wide : 15 < levelWords L)
    (published : ∀ j : Fin (vs).length, ∀ source, data j.val vs[j] source →
      source (levelStart L j.val+15) = ((B.recordLimit+2 : ℕ) : Word w)) :
    m (levelStart L (i.val+1)+15) = ((B.recordLimit+2 : ℕ) : Word w) := by
  let next : Fin (vs).length := ⟨i.val+1,executeLevels_shrink_succ_lt B f hf T hT X z i shrink⟩
  exact h.read_field next wide (published next)

end CompressorRecords.SelectedPayloadHistory

end VPVNP
end Computability
end OAI
