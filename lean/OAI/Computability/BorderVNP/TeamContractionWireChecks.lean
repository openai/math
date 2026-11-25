import OAI.Computability.BorderVNP.TeamContractionWires
import OAI.Computability.BorderVNP.TeamTapeInputRouteProcessor

/-! # Unique physical interior bits for a fixed chronological path and register handoffs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.Wires

open VPVNP BurstRAM RAMTape RAMSerialization
open TeamTapeSorting TeamTapeInputRoute.Verify
open scoped Classical
attribute [local instance] TeamTapeSorting.portDecidableEq

variable {r k w e W : ℕ}

/-- Checking the primary and all present padding blocks on their real owners is exactly
checking every virtual block once. -/
theorem allOwners_iff (hr : 0 < r) (hw : 2 ≤ W) (hc : 2^(Nat.clog 2 r)*2^e < 2^W)
    (a : Fields (Nat.clog 2 r) e W) (x : ℕ → Option (WordRecord W)) :
    (∀ j : Fin r, ownerValid hw hc a x (primary j) (secondary j)) ↔
      ∀ v, valid hw hc a x v := by
  constructor
  · intro checks v
    let j := TeamSorting.owner hr v
    rcases (owned_iff hr j v).mp rfl with h | h
    · rw [h]; exact (checks j).1
    · exact (checks j).2 v h
  · intro checks j; exact ⟨checks _,fun v _ => checks v⟩

/-- Fixed-length canonical shared register assignment, retaining every bit of each
internal successor frame. -/
def frameAssignment (frames : Fin (r-1) → TeamTapeHandoff.Frame w k) (j : Fin (r-1))
    (i : Fin (frameWidth k w)) : Bool := (frames j).bits[i.val]'((frames j).bits_length.symm ▸ i.isLt)

/-- Every real successor frame is read in its original bit order, with no unused bits. -/
theorem frameAssignment_bits (frames : Fin (r-1) → TeamTapeHandoff.Frame w k) (j : Fin (r-1)) :
    List.ofFn (frameAssignment frames j) = (frames j).bits := by
  apply List.ext_getElem
  · simp [frameWidth,TeamTapeHandoff.Frame.bits_length]
  · intro i hi hj; rw [List.getElem_ofFn]; rfl

/-- The unique successor-frame assignment and the accepted physical sorting fields
together determine exactly one full assignment on the paper's interior wire indices.
Conversely the local memory checks force the old words, including old words on writes. -/
theorem unique_interior_iff (hr : 0 < r) (hw : 2 ≤ W) (hc : 2^(Nat.clog 2 r)*2^e < 2^W)
    (frames : Fin (r-1) → TeamTapeHandoff.Frame w k) (rows : Fin r → List (TeamRecords.Record (Word W)))
    (hf : ∀ j, ∀ z ∈ rows j, ProbeFits z) (hfit : ∀ j, 2*(rows j).length ≤ 4*2^e)
    {actions : List (TeamRecords.Access (Word W))} {records : List (TeamRecords.Record (Word W))}
    (hmatches : TeamRecords.Matches actions records) (timed : TeamRecords.Timed actions)
    (perm : records.Perm (List.ofFn rows).flatten) :
    let x := rowInput e (padRows fun j => packRow (rows j) (hf j))
    (∃! links : Edge r k w e W → Bool,
      (∀ j, List.ofFn ((edgeEquiv links).1 j) = (frames j).bits) ∧
      ∀ j, ownerValid hw hc (edgeEquiv links).2 x (primary j) (secondary j)) ↔
      records = TeamRecords.transcript (fun _ => 0) actions := by
  intro x
  let T := siteBudget (Nat.clog 2 r) e W
  let Good (a : Fields (Nat.clog 2 r) e W) := ∀ v, program.body.count (fun _ _ => 0) T (siteInput hw a v x) = 1
  have hs : (∃! a, Good a) ↔ records = TeamRecords.transcript (fun _ => 0) actions :=
    existsUnique_rowBits hw hc rows hf hfit hmatches timed perm T le_rfl
  have hg (a : Fields (Nat.clog 2 r) e W) : Good a ↔ ∀ j, ownerValid hw hc a x (primary j) (secondary j) := by
    rw [allOwners_iff hr]
    apply forall_congr'
    intro v
    have eq := (program_spec hw hc a v x T le_rfl).1 (fun _ _ => 0)
    rw [eq]
    change (@ite ℕ (valid hw hc a x v) (Classical.propDecidable _) 1 0 = 1) ↔ _
    simp
  let F := frameAssignment frames
  have hframe (links : Edge r k w e W → Bool) :
      (∀ j, List.ofFn ((edgeEquiv links).1 j) = (frames j).bits) ↔ (edgeEquiv links).1 = F := by
    constructor
    · intro h; funext j
      exact List.ofFn_injective ((h j).trans (frameAssignment_bits frames j).symm)
    · intro h j; rw [h]; exact frameAssignment_bits frames j
  rw [← hs]
  constructor
  · rintro ⟨links,hl,unique⟩
    refine ⟨(edgeEquiv links).2,(hg _).mpr hl.2,?_⟩
    intro a ha
    let other := edgeEquiv.symm (F,a)
    have eq : edgeEquiv other = (F,a) := edgeEquiv.apply_symm_apply _
    have hother := unique other ⟨(hframe other).mpr (congrArg Prod.fst eq),
      (hg _).mp (by rwa [eq])⟩
    exact (congrArg Prod.snd eq).symm.trans (congrArg (fun z => (edgeEquiv z).2) hother)
  · rintro ⟨a,ha,unique⟩
    let links := edgeEquiv.symm (F,a)
    have eq : edgeEquiv links = (F,a) := edgeEquiv.apply_symm_apply _
    refine ⟨links,⟨(hframe links).mpr (congrArg Prod.fst eq),(hg _).mp (by rwa [eq])⟩,?_⟩
    intro other ho
    apply edgeEquiv.injective
    rw [eq]
    exact Prod.ext ((hframe other).mp ho.1) (unique _ ((hg _).mpr ho.2))

end TeamContraction.Wires

end BorderVNP
end Computability
end OAI
