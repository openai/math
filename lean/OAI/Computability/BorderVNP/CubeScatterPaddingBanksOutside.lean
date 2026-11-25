import OAI.Computability.BorderVNP.CubeScatterPaddingBanksFold

/-! # Survival of the literal frame and metadata outside both scatter banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding.Banks

open Scatter Physical Physical.Owned TeamRows RoutingISA VPVNP.BurstRAM Tally

variable {n d blocks b h K s w : ℕ} (A : Data n d blocks b h K s)

/-- A metadata address outside the complete singleton allocation and every packet bank. -/
def Data.Outside (a : ℕ) : Prop :=
  (a < A.singleBase ∨ A.singleBase+d^(n+1)*d^(n+1)*(blocks*(h*b)) ≤ a) ∧
    ∀ p : Packet n d blocks, a < A.packetAddr p ∨ A.packetAddr p+bankWidth n b h K s ≤ a

/-- The actual stores of a strict or diagonal row preserve any original metadata word
outside both reservations. This covers the group owners, width and packet tables. -/
theorem Data.row_outside (g f : Fin d) (sel cross : ℕ) (m : Memory w) (a : ℕ) (away : A.Outside a) :
    A.rowMem g f sel cross m a = m a := by
  have single (u v : Fin d) (sc cc : ℕ) (input : Memory w) :
      ((A.single u v sc cc).before input (singlePairTrials n d)).2 a = input a :=
    (A.single u v sc cc).final_outside _ _ _ away.1
  have strict (pair : Symbols d) (high : Bool) : A.strictMem pair high sel cross m a = m a := by
    let D := A.packet pair high sel cross
    have packet := D.before_invariant m (fun z => z a = m a) rfl (fun p _ state hold =>
      (D.visit_outside p state a (away.2 p)).trans hold) (packetTrials n d blocks) le_rfl
    exact (single _ _ _ _ _).trans ((single _ _ _ _ _).trans packet)
  unfold Data.rowMem
  split
  · apply strict
  split
  · apply strict
  · apply single

/-- In the chronological team fold, each preserved metadata word equals its input value,
including on every skipped row and before the first owned row. -/
theorem Data.fold_outside {l : TeamRowPrepare.Layout} (A : Data n l.d blocks b h K s)
    (owner : Fin l.d → ℕ) (step : Fin l.d → Fin l.d → ViewState w → ViewState w) (start : ViewState w)
    (sel cross : Fin l.d → Fin l.d → ℕ) (a : ℕ) (away : A.Outside a) (keep : ∀ q : Fin (l.d*l.d), let p := pairAt l.d q
      let z := fold l owner step start q.val
      owner p.1 = l.teamID → (step p.1 p.2 z).mem a = A.rowMem p.1 p.2 (sel p.1 p.2) (cross p.1 p.2) z.mem a) (k : ℕ) (hk : k ≤ l.d*l.d) :
    (fold l owner step start k).mem a = start.mem a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have old := ih (by omega)
    rw [fold_succ _ _ _ _ k hk]
    by_cases active : owner (pairAt l.d ⟨k,hk⟩).1 = l.teamID
    · rw [ite_eq_left active]; exact (keep ⟨k,hk⟩ active).trans ((A.row_outside _ _ _ _ _ _ away).trans old)
    · simpa only [ite_eq_right active] using old

end Cube.Padding.Banks

end BorderVNP
end Computability
end OAI
