import OAI.Computability.NearSquareRoot.ScheduleProgram
import OAI.Computability.NearSquareRoot.ScheduleGeneratorCode

/-!
# Effective serialization of interpreter transition tables

A computable state count and computable entries on valid rows suffice to emit
the entire interpreter ROM. The list of read tuples and the numbering of tags
are fixed across the family.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator

open IntegerMultiplication Universal

private theorem computable_range_flatMap (width : ℕ → ℕ) (rows : ℕ → ℕ → List ℕ)
    (hw : Computable width) (hr : Computable₂ rows) :
    Computable fun i => (List.range (width i)).flatMap (rows i) := by
  have h := Computable.nat_rec (σ := List ℕ) hw (Computable.const [])
    (Computable.list_append.comp (Computable.snd.comp Computable.snd)
      (hr.comp Computable.fst (Computable.fst.comp Computable.snd))).to₂
  apply h.of_eq
  intro i
  induction width i with
  | zero => rfl
  | succ n ih => simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih]

private theorem computable_fixed_flatMap {R : Type} (rs : List R)
    (f : R → ℕ → ℕ → List ℕ) (hf : ∀ r ∈ rs, Computable₂ (f r)) :
    Computable₂ fun i q => rs.flatMap (fun r => f r i q) := by
  induction rs with
  | nil => exact Computable.const []
  | cons r rest ih =>
    exact Computable.list_append.comp (hf r (by simp))
      (ih fun s hs => hf s (by simp [hs]))

/-- Serialize a family of finite rules whose numeric transition entries are uniformly
computable in the family index and row address, for each fixed read tuple. -/
theorem computable_program {A I : Type} {M : ℕ} (rs : List (I → A))
    (states : ℕ → ℕ) (machine : ∀ i, TM.Rule A (Fin (states i)) I)
    (enum : Tag A I ≃ Fin (M + 1))
    (next branch : (I → A) → ℕ → ℕ → ℕ) (hstates : Computable states)
    (hnext : ∀ r ∈ rs, Computable₂ (next r)) (hbranch : ∀ r ∈ rs, Computable₂ (branch r))
    (next_eq : ∀ r ∈ rs, ∀ i (q : Fin (states i)), next r i q.val = target (machine i q r))
    (branch_eq : ∀ r ∈ rs, ∀ i (q : Fin (states i)), branch r i q.val =
      (enum (.branch r (commands (machine i q r)))).val) :
    Computable fun i => (program (machine i) rs).map (fun a => (enum a).val) := by
  let digit (a : Tag A I) := (enum a).val
  let entry (r : I → A) (i q : ℕ) := branch r i q :: List.replicate (next r i q) (digit .tick)
  let row (i q : ℕ) := digit .row :: rs.flatMap (fun r => entry r i q)
  have hticks : Computable fun n : ℕ => List.replicate n (digit .tick) := by
    simpa using (Primrec.list_map Primrec.list_range
      ((Primrec.const (digit .tick)).to₂ : Primrec₂ fun (_ _ : ℕ) => digit .tick)).to_comp
  have he (r) (hr : r ∈ rs) : Computable₂ (entry r) :=
    Computable.list_cons.comp (hbranch r hr) (hticks.comp (hnext r hr))
  have hrow : Computable₂ row :=
    Computable.list_cons.comp (Computable.const _) (computable_fixed_flatMap rs entry he)
  have hcode := Computable.list_cons.comp (Computable.const (digit .origin))
    (Computable.list_append.comp (computable_range_flatMap states row hstates hrow)
      (Computable.const [digit .endCode]))
  apply hcode.of_eq
  intro i
  have indices : (List.finRange (states i)).map Fin.val = List.range (states i) := by
    apply List.ext_getElem <;> simp
  simp only [program, List.map_cons, List.map_append, List.map_nil, List.map_flatMap]
  rw [← indices, List.flatMap_map]
  congr 2
  apply List.flatMap_congr
  intro q _
  simp only [row, rowCode, List.map_cons, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro r hr
  simp [entry, entryCode, branch_eq r hr, next_eq r hr, digit]

end Generator

end NearSquareRoot
end Computability
end OAI
