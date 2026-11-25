import OAI.Computability.BorderVNP.ParseBatchLookupSort
import OAI.Computability.BorderVNP.ParseBatchVerifierAdjacent

/-! # Shared Boolean circuit for simultaneous reads

The sort reads address bits followed by a table/read tag and a suffix. The
adjacent check reads these same physical wires after sorting. The optional
payload positions in the suffix may omit the request number and other tie breakers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchLookup

open VPVNP.VerifierNetwork BorderVNP.ParseBatchSort

/-- Physical positions of the high field of a packed word. -/
def highPin (w : ℕ) : {a : ℕ} → Fin a → Fin (w+a)
  | 0, i => i.elim0
  | _+1, i => Fin.cases 0 (fun j => (highPin w j).succ) i

/-- Physical positions of the low field after skipping the high field. -/
def lowPin {w : ℕ} : (a : ℕ) → Fin w → Fin (w+a)
  | 0, j => j
  | a+1, j => (lowPin a j).succ

private theorem repack {w a : ℕ} (z : Fin (w+a) → Bool) :
    prepend (z ∘ highPin w) (z ∘ lowPin a) = z := by
  induction a with
  | zero => rfl
  | succ a ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [prepend, highPin]
    · change (Fin.cons (α := fun _ => Bool) _ (prepend (fun j => z ((highPin w j).succ))
        (fun j => z ((lowPin a j).succ)))) j.succ = _
      rw [Fin.cons_succ]
      exact congrFun (ih (z ∘ Fin.succ)) j

/-- Decode a designated subset of the low-field pins after the address and tag. -/
def selectedPayload {p w : ℕ} (a : ℕ) (pick : Fin p → Fin w) (z : Fin ((w+1)+a) → Bool) :
    Fin p → Bool := fun j => z (lowPin a (pick j).succ)

/-- Reading the physical slice pins recovers the decoder used to prove lookup correctness. -/
theorem row_from_pins {a p w : ℕ} (pick : Fin p → Fin w) (z : Fin ((w+1)+a) → Bool) :
    fromWord w (selectedPayload a pick) z =
      ⟨value (z ∘ highPin (w+1)), z (lowPin a 0), selectedPayload a pick z⟩ := by
  let tag := z (lowPin a 0)
  let address := z ∘ highPin (w+1)
  let tail := fun j : Fin w => z (lowPin a j.succ)
  have hz : bits address tag tail = z := by
    have ht : Fin.cons tag tail = z ∘ lowPin a := by
      funext i; exact Fin.cases rfl (fun _ => rfl) i
    rw [bits, ht]
    exact repack z
  simpa only [hz] using fromWord_bits (selectedPayload a pick) address tag tail

variable {σ : Type*} [Fintype σ] {b a w p : ℕ}

/-- Sort and check all rows, selecting payload pins inside the low field. -/
noncomputable def lookupFrame (f : Frame σ (Pins b ((w+1)+a))) (pick : Fin p → Fin w) :
    Frame σ Unit :=
  adjacentFrame (phases b le_rfl f) (fun i j => (i, highPin (w+1) j))
    (fun i => (i, lowPin a 0)) (fun i j => (i, lowPin a (pick j).succ))

/-- The actual sorted circuit accepts exactly the prescribed table reads, in their original
positions. The only inputs are the table data and requests, including proposed values. -/
theorem lookupFrame_eval (f : Frame σ (Pins b ((w+1)+a))) (pick : Fin p → Fin w)
    (x : σ → Bool) (table : ℕ → Option (Fin p → Bool))
    (ht : TableSpec table (fun i => fromWord w (selectedPayload a pick) (fun j => f.eval x (i,j)))) :
    (lookupFrame f pick).eval x () = true ↔ ∀ i,
      table (value (fun j => f.eval x (i,highPin (w+1) j))) =
        some (fun j => f.eval x (i,lowPin a (pick j).succ)) := by
  rw [lookupFrame, adjacentFrame_eval]
  have hrows : pinRows (fun i j => (i, highPin (w+1) j)) (fun i => (i, lowPin a 0))
      (fun i j => (i, lowPin a (pick j).succ)) ((phases b le_rfl f).eval x) =
      fun i => fromWord w (selectedPayload a pick) (fun j => (phases b le_rfl f).eval x (i,j)) := by
    funext i
    rw [row_from_pins]
    rfl
  rw [hrows, checks_after_sort_iff f x w (selectedPayload a pick) table ht]
  simp only [row_from_pins, Function.comp_def]
  rfl

/-- Explicit gate cost of the complete sort, physical slice comparisons, and final conjunction. -/
theorem lookupFrame_size (f : Frame σ (Pins b ((w+1)+a))) (pick : Fin p → Fin w) :
    (lookupFrame f pick).size ≤ f.size + b^2 * (2^b*(24*((w+1)+a)+1)) +
      2^b*(10*(a+p)+11)+2 := by
  apply (adjacentFrame_size _ _ _ _).trans
  have h := phases_size b le_rfl f
  omega

end ParseBatchLookup

end BorderVNP
end Computability
end OAI
