import OAI.Computability.BorderVNP.TeamSiteConsistencyMemory
import OAI.Computability.BorderVNP.TeamSiteConsistencyLinks
import OAI.Computability.BorderVNP.TeamSiteConsistencyBounds

/-! # Individual raw assignments of the team interior

All physical successor, sort-send and boundary bits of a locally replayed block trace
are tested on their real owners. The individual assignment passes exactly when it is
the native one and the trace uses true RAM memory at every guessed word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency

open VPVNP RAMTape RAMSerialization TeamRAM TeamContraction.Wires TeamTapeSorting TeamTapeInputRoute.Verify
open BurstRAM (Word Memory)
variable {w r k e : ℕ}

/-- The actual globally addressed physical sorting array of the emitted processor rows. -/
def array (e : ℕ) (input : Fin r → List Bool) (blocks : Fin r → List (Event w)) :=
  rowInput e (padRows (realRows input blocks))

private theorem occupied_perm (input : Fin r → List Bool) (blocks : Fin r → List (Event w))
    (hi : ∀ j, 2*(TeamTapeInputEmit.rowStart input j + (input j).length) ≤ 2^(w+1))
    (hf : ∀ j, ∀ z ∈ rowFields input blocks j, ProbeFits z)
    (size : ∀ j, (realRows input blocks j).length ≤ 4*2^e) :
    ((chronology input blocks).flatMap TeamRecords.pair).Perm
      (occupied ((2+e)+Nat.clog 2 r) (array e input blocks)) := by
  have cap (v) : (padRows (realRows input blocks) v).length ≤ 4*2^e := by
    by_cases h : v.val < r
    · simpa [padRows,h] using size ⟨v.val,h⟩
    · simp [padRows,h]
  have decode (j) : (realRows input blocks j).map WordRecord.record =
      (rowFields input blocks j).flatMap TeamRecords.pair := by
    rw [realRows_eq_packRow _ _ j (hi j) (hf j),packRow_decode]
  rw [array,occupied_rowInput _ cap,flatten_padRows,List.map_flatten]
  have flat : ((List.ofFn (rowFields input blocks)).flatten.flatMap TeamRecords.pair) =
      ((List.ofFn (realRows input blocks)).map (List.map WordRecord.record)).flatten := by
    simp only [List.flatMap_def,List.map_flatten,List.map_ofFn,Function.comp_def,decode,List.flatten_flatten]
  rw [←flat]
  exact (chronology_perm input blocks).flatMap fun _ _ => .refl _

/-- The predicate tested at all real owners for the physically shared edges of one
team, including the possible second virtual block. -/
def OwnerChecks (hw : 2 ≤ w+1) (hc : 2^(Nat.clog 2 r)*2^e < 2^(w+1))
    (input : Fin r → List Bool) (blocks : Fin r → List (Event w))
    (frames : Fin (r-1) → TeamTapeHandoff.Frame w k) (links : Edge r k w e (w+1) → Bool) : Prop :=
  (∀ j, List.ofFn ((edgeEquiv links).1 j) = (frames j).bits) ∧
    ∀ j, ownerValid hw hc (edgeEquiv links).2 (array e input blocks) (primary j) (secondary j)

/-- For an arbitrary assignment, the real owner checks determine *every* interior
bit and recover precisely the true native computation. The bounds are on the original
word clock and the actual inputs and emitted buffers. -/
theorem ownerChecks_iff_execute {S : Type*} (hr : 0 < r) (hw : 2 ≤ w+1)
    (hc : 2^(Nat.clog 2 r)*2^e < 2^(w+1)) (input : Fin r → List Bool) (blocks : Fin r → List (Event w))
    (frames : Fin (r-1) → TeamTapeHandoff.Frame w k) (links : Edge r k w e (w+1) → Bool)
    {P : S → Instr w S} {s : S} (loc : Local P s (List.ofFn blocks).flatten)
    (time : 1+RAMBuckets.cost (fun z => z.action.extra) (List.ofFn blocks).flatten ≤ 2^w)
    (header : (List.ofFn input).flatten.length ≤ 2^w)
    (size : ∀ j, (realRows input blocks j).length ≤ 4*2^e) :
    OwnerChecks hw hc input blocks frames links ↔
      links = canonicalLinks hw frames (array e input blocks) ∧
      execute P s (inputMemory w input) ((List.ofFn blocks).flatten.map Event.choices) = some (List.ofFn blocks).flatten := by
  have positive : 0 < w := by omega
  obtain ⟨hm,ht⟩ := chronology_spec positive input blocks loc
  have perm := occupied_perm input blocks (row_input_size input header)
    (rowFields_fit input blocks loc time header) size
  rw [OwnerChecks,valid_links_iff hr hw hc frames _ hm ht perm links,
    chronology_eq_transcript_iff positive input blocks loc,execute_iff]
  tauto

end TeamSiteConsistency

end BorderVNP
end Computability
end OAI
