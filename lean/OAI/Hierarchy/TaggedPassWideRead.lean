import OAI.Hierarchy.TaggedPassRead

namespace OAI
/-! # Regrouping the retained row stream into contiguous wide words -/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork RadixStage SortedBlock
open scoped Classical
noncomputable section

variable {α : Type*}


namespace PassShape

variable (s : PassShape) {w : ℕ} (dummy : Fin w → Bool)

/-- Viewing the same retained slots as packs changes neither their data nor
any order-sensitive reading of those data. -/
theorem wide_sweep (v : s.LocalData w → Bool) (observe : (Fin w → Bool) → List α) (quiet : observe dummy=[])
    (fits : s.perBlock ≤ 2^s.localBits) (volume : s.nextRows ≤ 2^s.globalHeight*s.pack) :
    sweep (2^s.globalHeight) (fun r => sweep s.pack (fun i => observe (s.wideLane (staticRead (s.wideInput dummy) v) r i))) =
      sweep s.blocks (fun b => sweep s.perBlock (fun i => observe (s.blockWord v b (i.castLE fits)))) := by
  let read (k : Fin s.nextRows) := let i := s.retainedIndex k fits; observe (s.blockWord v i.1 i.2)
  let pad (k : Fin (2^s.globalHeight*s.pack)) := if h : k.val < s.nextRows then read ⟨k.val,h⟩ else []
  have word (r i) : observe (s.wideLane (staticRead (s.wideInput dummy) v) r i) = pad (finProdFinEquiv (r,i)) := by
    rw [wide_word s dummy v fits]
    have ix : (finProdFinEquiv (r,i)).val = r.val*s.pack+i.val := by simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
    simp only [pad,ix]; split <;> simp_all [read]
  simp_rw [word,←sweep_rect]
  rw [sweep_extend volume read pad (fun i => dite_eq_left i.isLt) (fun i h => dite_eq_right h.not_gt)]
  let blockRead (i : Fin (s.blocks*s.perBlock)) := read i
  calc
    _ = sweep s.blocks (fun b => sweep s.perBlock (fun i => blockRead (finProdFinEquiv (b,i)))) :=
      sweep_rect (m := s.blocks) (n := s.perBlock) blockRead
    _ = _ := by
      have atSlot (b : Fin s.blocks) (i : Fin s.perBlock) : blockRead (finProdFinEquiv (b,i)) =
          observe (s.blockWord v b (i.castLE fits)) := congrArg observe (s.retained_word fits v b i)
      simp only [atSlot]

end PassShape
end
end Hierarchy.Tagged.Radix

end OAI
