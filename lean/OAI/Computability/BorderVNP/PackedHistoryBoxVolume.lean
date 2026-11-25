import OAI.Computability.BorderVNP.PackedHistoryPaidBoxShape
import OAI.Computability.BorderVNP.PackedPaidBoxWordLimit
import OAI.Computability.BorderVNP.PackedFinalReportSpare

/-! # Public volume of the actual selected terminal box directory

Known paid tables use a number of words bounded by the fixed paid identity.
An opaque original description occupies one descriptor and no public factor
words. Consequently the full static table is linear in padded site rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited FrozenTape CellSparse PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open CellPacketGeometry CellPacketGeometry.SiteWords CellPacketGeometry.History
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
    {start T : ℕ} (dir : Directory.Layout) (count : dir.entries=(fan S)^T*dir.sites) (number : e.Entry → ℕ)
    (pos : 0<(SelectedSchedule.boundaryShape S start T).sites)

local notation "sites" => (SelectedSchedule.boundaryShape S start T)
local notation "boxes" => scheduledBoxes dir count number pos

/-- A padded original/public site carries at most one box descriptor. -/
theorem scheduledBoxes_count : (∑ i, (boxes i).length) ≤ (sites).sites := by
  have bound (i : Fin (sites).sites) : (boxes i).length ≤ 1 := by
    rcases scheduledBoxes_cases dir count number pos i with h | ⟨_,_,h⟩ | ⟨_,h⟩ <;> simp [h]
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,mul_one] using
    Finset.sum_le_sum (s:=Finset.univ) (fun i _ => bound i)

/-- The emitted public table words are bounded without charging any byte of
the separately received original factor descriptions. -/
theorem scheduledBoxes_words : (∑ i, (boxWords (boxes i)).length) ≤ BoxRoster.paidWordLimit e*(sites).sites := by
  have bound (i : Fin (sites).sites) : (boxWords (boxes i)).length ≤ BoxRoster.paidWordLimit e := by
    rcases scheduledBoxes_cases dir count number pos i with h | ⟨a,v,h⟩ | ⟨j,h⟩
    · rw [h]; exact Nat.zero_le _
    · rw [h]; exact BoxRoster.paidBoxWords_le e number a v
    · rw [h]; exact Nat.zero_le _
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] using
    Finset.sum_le_sum (s:=Finset.univ) (fun i _ => bound i)

variable {C g digits : ℕ} {R B U V : Type} (old : Schema R B) (last : Schema U V)

/-- Complete sparse source charge for the true frozen and final record tapes,
the opaque-pointer column and the signed report layout, including the spare. -/
theorem scheduledBoxes_sourceVolume :
    sourceVolume old last boxes (FinalReports.Spare.reports (C:=C) (g:=g) (digits:=digits) (E:=Fin dir.entries)) ≤
      (3+BoxRoster.paidWordLimit e)*(1+(sites).sites+C*(1+g*(1+digits))+
        old.rows.length+tagWords old+last.rows.length+tagWords last+dir.entries) := by
  rw [FinalReports.Spare.sourceVolume_eq,Fintype.card_fin]
  let mass := 1+(sites).sites+C*(1+g*(1+digits))+old.rows.length+tagWords old+last.rows.length+tagWords last+dir.entries
  have descriptors := scheduledBoxes_count dir count number pos
  have words := scheduledBoxes_words dir count number pos
  have layout : C*(1+g*(1+digits)) = C+C*g+C*g*digits := by ring
  have smaller : (sites).sites ≤ mass := by dsimp [mass]; omega
  have large := Nat.mul_le_mul_left (BoxRoster.paidWordLimit e) smaller
  change _ ≤ (3+BoxRoster.paidWordLimit e)*mass
  rw [Nat.add_mul]
  dsimp only [mass] at large ⊢
  omega

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
