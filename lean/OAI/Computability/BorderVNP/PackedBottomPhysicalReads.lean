import OAI.Computability.BorderVNP.PackedBottomReportAcceptance
import OAI.Computability.BorderVNP.PackedGridWitnessAlive

/-! # Recovering the true conditioned fine-site inputs from a passing bottom box

The original fine-wire guesses occupy the first interval of each copy. The
remaining fine bits are the subwords selected by the concrete channel packing
and grouped external slot map. A verifier's named rule then reads exactly its
conditioned original table row, without interpreting a source name as a local
RAM address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes Inherited Diagonal.CellEntries
open scoped Classical

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ne np qe qa : ℕ} (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "ord" => sourceOrder G channelID groupID v
local notation "fineIndex" => publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v

/-- Physical one-copy public channel word at the site's canonical incidence positions. -/
noncomputable def channelRead (input : Fin (incoming G v) → Bool)
    (q : {q : Q // src q = v ∨ dst q = v}) (k : Fin H) := input (ord (.inl ⟨q,k⟩))

/-- The live original port reads its actual lane in the site's grouped exterior word. -/
noncomputable def argumentRead (input : Fin (incoming G v) → Bool)
    (p : {p : P // cell (N.attach p) = v}) (_ : Fin 1) :=
  input (ord (.inr ⟨⟨(lane p.val).1,(aligned p.val).trans p.property⟩,(lane p.val).2⟩))

local notation "a₀" => channelRead (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v
local notation "x₀" => argumentRead (src := src) (dst := dst) (H := H) N cell position width owner lane aligned channelID groupID v

/-- The fine supplied vector on the physical grouped input is exactly the
canonical decoder of the subwords needed by the fine cell. -/
theorem supplied_decoder (input : Fin (incoming G v) → Bool) :
    (fun k => input (fineIndex k)) =
      (suppliedWords N cell v edgeID portID).symm
        (publicWords cell position pack v (a₀ input) (x₀ input)) := by
  apply (suppliedWords N cell v edgeID portID).injective
  rw [Equiv.apply_symm_apply]
  funext u k
  change input (fineIndex (suppliedOrdinal N cell v edgeID portID u k)) = _
  rw [publicIndex_supplied]
  cases u <;> rfl

/-- Exact fine prefix of the old physical word array, after recovering the
free internal wire vector and the forced external subwords. -/
theorem prefix_physical (input : Fin (incoming G v) → Bool) (hidden : ∀ u, N.InsideAssignment cell u)
    (bank : ℕ → Bool) (off : ℕ)
    (guess : ∀ k : Fin (guessedSize N cell v), bank (off+k.val) = ((guessedWords N cell v edgeID).symm (hidden v)) k)
    (supply : ∀ k : Fin (suppliedSize N cell v), bank (off+(guessedSize N cell v+k.val)) = input (fineIndex k)) :
    ∀ k : Fin (GridBoxes.stride N cell v), bank (off+k.val) =
      physicalBits cell position hidden pack edgeID portID v (a₀ input) (x₀ input) k := by
  intro k
  obtain ⟨j,rfl⟩ := (finSumFinEquiv (m := guessedSize N cell v) (n := suppliedSize N cell v)).surjective k
  cases j with
  | inl j =>
    simp only [physicalBits,copyBits,Equiv.symm_apply_apply,Sum.elim_inl]
    exact guess j
  | inr j =>
    simp only [physicalBits,copyBits,Equiv.symm_apply_apply,Sum.elim_inr]
    exact (supply j).trans (congrFun (supplied_decoder N cell position pack width owner lane aligned edgeID portID
      channelID groupID v input) j)

/-- Reading a named report from a source-major sidecar does not require any report
label to be a local RAM pointer. At each passing copy its original fine guard is
the genuine cell read for the extracted private wire assignment. -/
theorem named_guard_read (rules : ∀ u, Rule N u) (use : Port → Bool) (u : {u : N.Site // cell u = v})
    (input : Fin (incoming G v) → Bool) (hidden : ∀ c, N.InsideAssignment cell c)
    (bank : ℕ → Bool) (off : ℕ)
    (hread : ∀ k : Fin (GridBoxes.stride N cell v), bank (off+k.val) =
      physicalBits cell position hidden pack edgeID portID v (a₀ input) (x₀ input) k) :
    (rules u.val).passes (fun l => bank (off+(GridBoxes.lane N cell v edgeID portID u l).val)) use =
      cellRead cell position hidden pack (guard rules use) v u (a₀ input) (x₀ input) :=
  accepts_cellRead cell position hidden pack edgeID portID
    (fun u => .truth (fun r => (rules u).passes r use)) v u (a₀ input) (x₀ input) bank off 0 hread

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
