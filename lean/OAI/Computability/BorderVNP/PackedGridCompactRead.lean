import OAI.Computability.BorderVNP.PackedGridWitnessAlive
import OAI.Computability.BorderVNP.PackedBottomWeightedValue

/-! # Native repeated bottom-bank addresses read the actual conditioned seed factors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse CellAddresses Diagonal.CellEntries Inherited BottomGridBank
open scoped Classical
variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
    (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
    (pack : (N.cellNetwork cell position).ChannelPacking src dst H) (hidden : ∀ i, N.InsideAssignment cell i)
    (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
    (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
    {ne np qe qa : ℕ} (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (c : C)
local notation "G" => grouped (H := H) (src := src) (dst := dst) N cell position width owner

omit [Fintype Q] in
/-- The guarded one-copy test in the native compact fine bank checks precisely
the Boolean base factors on the chosen hidden and exposed grid words. -/
theorem finePass_cellRead (rules : ∀ v, Rule N v) (a x) :
    finePass N cell edgeID portID c (fun v => rules v.val)
      ((guessedWords N cell c edgeID).symm (hidden c))
      ((suppliedWords N cell c edgeID portID).symm (publicWords cell position pack c a x)) ↔
      ∀ v, cellRead cell position hidden pack (baseTable rules) c v a x = true := by
  let bits := physicalBits cell position hidden pack edgeID portID c a x
  let bank (j : ℕ) := if h : j < stride N cell c then bits ⟨j,h⟩ else false
  have hb (i : Fin (stride N cell c)) : bank (0+i.val) = bits i := by simp [bank,i.isLt]
  apply forall_congr'
  intro v
  let baseRules (v : N.Site) : Rule N v := .truth (rules v).base
  have hr := accepts_cellRead cell position hidden pack edgeID portID baseRules c v a x bank 0 0 hb
  change (rules v.val).base (fun l => bits (GridBoxes.lane N cell c edgeID portID v l)) = true ↔ _
  change (rules v.val).base (fun l => bank (0+(GridBoxes.lane N cell c edgeID portID v l).val)) =
    cellRead cell position hidden pack (baseTable rules) c v a x at hr
  simp only [hb] at hr
  exact (congrArg (· = true) hr).to_iff

/-- The grouped word's true argument lane is read at each exposed fine input. -/
abbrev argumentWords (x : ∀ p : {p : A // owner p = c}, Fin (width p.val) → Bool)
    (p : {p : P // cell (N.attach p) = c}) (_ : Fin 1) : Bool :=
  x ⟨(lane p.val).1,(aligned p.val).trans p.property⟩ (lane p.val).2

/-- On an actual one-copy grouped input, the fine address lookup is exactly
the inverse of the compact supplied-word encoding. -/
theorem supplied_pull (a : Incident G c → Fin H → Bool) (x : ∀ p : Attached G c, Fin (width p.val) → Bool) :
    (fun k => inputWords G channelID groupID c a x
      (publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID c k)) =
    (suppliedWords N cell c edgeID portID).symm
      (publicWords cell position pack c a (argumentWords N cell width owner lane aligned c x)) := by
  apply (suppliedWords N cell c edgeID portID).injective
  rw [Equiv.apply_symm_apply]
  funext u k
  change inputWords G channelID groupID c a x
    (publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID c
      (suppliedOrdinal N cell c edgeID portID u k)) = _
  rw [publicIndex_supplied]
  cases u with
  | inl e => exact inputWords_wire G channelID groupID c a x _ _
  | inr p => exact inputWords_port G channelID groupID c a x _ _

open private slice_words from OAI.Computability.BorderVNP.FiniteBottomGridModel

/-- Each copy of the real wide grouped input reads the true compact boundary
vector of its own seed-grid term. -/
theorem copy_supplied_pull (copies : ℕ) (i : Fin copies)
    (a : Incident (BottomRepeat.wide G copies) c → Fin (copies*H) → Bool)
    (x : ∀ p : Attached (BottomRepeat.wide G copies) c, Fin (copies*width p.val) → Bool) :
    scalarFine N cell position pack width owner lane aligned edgeID portID channelID groupID c copies
      (inputWords (BottomRepeat.wide G copies) channelID groupID c a x) i =
    (suppliedWords N cell c edgeID portID).symm (publicWords cell position pack c
      (fun e k => a e (finProdFinEquiv (i,k))) (argumentWords N cell width owner lane aligned c
        (fun p k => x p (finProdFinEquiv (i,k))))) := by
  unfold scalarFine
  rw [slice_words]
  exact supplied_pull N cell position pack width owner lane aligned edgeID portID channelID groupID c _ _

omit [Fintype P] in
/-- The public grouped padding check sees the original unused directed cable
lanes of the copy and tests each at its true address. -/
theorem copy_publicPad (copies : ℕ) (i : Fin copies)
    (a : Incident (BottomRepeat.wide G copies) c → Fin (copies*H) → Bool)
    (x : ∀ p : Attached (BottomRepeat.wide G copies) c, Fin (copies*width p.val) → Bool) :
    publicPad N cell position pack width owner channelID groupID c
      (scalarSlice (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID c copies
        (inputWords (BottomRepeat.wide G copies) channelID groupID c a x) i) ↔
      padOK pack c (fun e k => a e (finProdFinEquiv (i,k))) (argumentWords N cell width owner lane aligned c
        (fun p k => x p (finProdFinEquiv (i,k)))) := by
  rw [slice_words]
  simp only [publicPad,padOK,inputWords_wire]

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI
