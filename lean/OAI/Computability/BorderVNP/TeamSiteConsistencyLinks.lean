import OAI.Computability.BorderVNP.TeamContractionWireChecks

/-! # Individual accepted assignments of physical sorter and handoff links

For a fixed path and its emitted records, even a single successful interior assignment
forces the native old-word transcript and the canonical register and sorting messages.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency

open VPVNP BurstRAM RAMTape RAMLayout RAMMemory RAMSerialization RAMSort RAMBoundary
open TeamContraction.Wires TeamTapeSorting TeamTapeInputRoute.Verify
open scoped Classical

variable {r k w e W : ℕ}

/-- The actual canonical transmitted bits for a fixed array of emitted words and the
computed register frames at the internal real-site boundaries. -/
def canonicalLinks (hw : 2 ≤ W) (frames : Fin (r-1) → TeamTapeHandoff.Frame w k)
    (x : ℕ → Option (WordRecord W)) : Edge r k w e W → Bool :=
  edgeEquiv.symm (frameAssignment frames,
    encodeFields hw (actualMemoryMessages (2+e) (Nat.clog 2 r) (wire x)) (actualFits x))

/-- For each individual raw interior assignment, acceptance at every real owner forces
the native memory history and every canonical register and sorting bit. Conversely
those canonical bits pass all local checks whenever the guesses are the native history. -/
theorem valid_links_iff (hr : 0 < r) (hw : 2 ≤ W) (hc : 2^(Nat.clog 2 r)*2^e < 2^W)
    (frames : Fin (r-1) → TeamTapeHandoff.Frame w k) (x : ℕ → Option (WordRecord W))
    {es : List (TeamRecords.Access (Word W))} {rs : List (TeamRecords.Record (Word W))}
    (he : TeamRecords.Matches es rs) (ht : TeamRecords.Timed es)
    (hp : (rs.flatMap TeamRecords.pair).Perm (occupied ((2+e)+Nat.clog 2 r) x))
    (links : Edge r k w e W → Bool) :
    ((∀ j, List.ofFn ((edgeEquiv links).1 j) = (frames j).bits) ∧
      ∀ j, ownerValid hw hc (edgeEquiv links).2 x (primary j) (secondary j)) ↔
      links = canonicalLinks hw frames x ∧ rs = TeamRecords.transcript (fun _ => 0) es := by
  let m := actualMemoryMessages (2+e) (Nat.clog 2 r) (wire x)
  have hf : m.FitsWord := actualFits x
  rw [allOwners_iff hr]
  simp only [valid,forall_and]
  rw [pairedMemory_iff_transcript x _ he ht hp]
  constructor
  · rintro ⟨f,fmt,mem,history⟩
    refine ⟨edgeEquiv.injective ?_,history⟩
    rw [canonicalLinks,Equiv.apply_symm_apply]
    apply Prod.ext
    · funext j; exact List.ofFn_injective ((f j).trans (frameAssignment_bits frames j).symm)
    · exact fields_eq_encode hw hc _ m hf fmt mem
  · rintro ⟨rfl,hist⟩
    simp only [canonicalLinks,Equiv.apply_symm_apply]
    exact ⟨frameAssignment_bits frames,format_encode hw hc m hf,memory_encode hw hc m hf,hist⟩

end TeamSiteConsistency

end BorderVNP
end Computability
end OAI
