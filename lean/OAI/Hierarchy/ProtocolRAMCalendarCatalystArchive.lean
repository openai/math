import OAI.Hierarchy.ProtocolRAMCatalystArchiveRank
import OAI.Hierarchy.ProbeCoreReserve
import OAI.Hierarchy.ProtocolRAMReserveUse
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # The chronological reserve archive funds the physical catalyst pairs -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar ProbeStage ProbeStage.CoreBoard Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical

variable {count payload w : ℕ} (c : Mesh) (issued : Attempt→Entry count payload)

def site (j : Fin (recordCount c issued)) : Fin count :=
  let v := (rank c issued).symm j
  (atTime c issued v.1).owner v.2

def debit (j : Fin (recordCount c issued)) : ℕ :=
  let v := (rank c issued).symm j
  (atTime c issued v.1).bits v.2

/-- Summing actual per-event arrays in chronological order bounds each key
by one payload width per calendared event, including feeds with no debit rows. -/
theorem funded (i : Fin count) :
    (∑ j,if site c issued j=i then debit c issued j else 0)≤fuel c*payload :=
  ReserveUse.funded_padded (fun t=>Fin (atTime c issued t).rows)
    (fun t=>(atTime c issued t).owner) (fun t=>(atTime c issued t).bits)
    (rank c issued) (event_count c).le (fun t=>(atTime c issued t).fits)
    (fun t=>(atTime c issued t).separate) i

/-- The used/reserved pair is read from the actual output after both native
seeding passes and the complete weighted scatter. -/
theorem remaining (a : ReserveUse.Archive) (b : RouteSettlement.Banks) (m : Memory w)
    (mounted : ReserveUse.Mounted a b (fuel c*payload) (site c issued) (debit c issued) m)
    (usedSize : count≤b.used.size) (reservedSize : count≤b.reserved.size)
    (wide : fuel c*payload<2^w) (i : Fin count) :
    let final := ReserveUse.output a b (fuel c*payload) (site c issued) (debit c issued) m
    RouteSettlement.actual b.used final i.val≤RouteSettlement.actual b.reserved final i.val := by
  obtain ⟨used,reserved⟩ := ReserveUse.reported a b (fuel c*payload) (site c issued)
    (debit c issued) m mounted i usedSize reservedSize (funded c issued i) wide
  dsimp only
  rw [used,reserved]
  exact funded c issued i

/-- The funding on each geometric column and axis is exactly the cardinality
of the initially installed catalyst bits labelled by that column and axis. -/
theorem initial_reserve {h d k : ℕ}
    (history : Attempt→Entry (Fintype.card (Columns h d)*k) payload)
    (p : Columns h d × Fin k) :
    (∑ j,if site c history j=pairKeys (Columns h d) k p then debit c history j else 0)≤
      Fintype.card {v : ReserveBits h d k (fuel c*payload) //
        reserveLocation h d k (fuel c*payload) v=p} := by
  rw [reserve_fiber]
  exact funded c history _

/-- Every intermediate state fits in the same initially installed per-pair
aperture, even if a later attempt revisits that column. -/
theorem prefix_funded (before : ℕ) (i : Fin count) :
    (∑ j : Fin (recordCount c issued),
      if ((rank c issued).symm j).1.val<before ∧ site c issued j=i then debit c issued j else 0)
      ≤ fuel c*payload := by
  apply le_trans _ (funded c issued i)
  apply Finset.sum_le_sum
  intro j _
  by_cases passed : ((rank c issued).symm j).1.val<before <;>
    simp [passed]

/-- Total advance provision on the original exposed column/axis layout.
The calendar, degree and radix constants precede the permutation height. -/
theorem provision {h d : ℕ} (k payload : ℕ) (radix : 1≤d) :
    Fintype.card (ReserveBits h d k (fuel c*payload))≤
      ((2+2*(18*(d-1)+1)*4^(rounds d+1))*k*fuel c)*(2^h*payload) := by
  have height : Stages h d=18*(d-1)+1 := by
    change (template (ProbeStage.radix h d) (radix_pos h d) (rounds d) Unit (2^h)).shapes.length = _
    rw [template_length]
    unfold rounds
    omega
  simpa only [height] using (reserve_total_bound (h:=h) (k:=k) radix (le_refl (fuel c*payload)))

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
