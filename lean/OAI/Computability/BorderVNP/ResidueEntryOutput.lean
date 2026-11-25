import OAI.Computability.BorderVNP.ResidueEntryInput
import OAI.Computability.BorderVNP.ResidueEntryFieldGridGuard

/-! # Output wiring of the variable residue-entry verifier

A common input tape carries the queried column, a multiplicative grid tuple and
the final threshold word. The output circuit reads the column's linear form
from its advised basis table, rejects noncanonical and zero grid coordinates,
and tests the threshold against the resulting prime-field representative.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryOutput

open ExactQuantumFactoring BooleanNetwork BitArithmetic
open ResidueEntryField ResidueEntryFieldGrid ResidueEntryInput ResidueFourier ResidueBox
open scoped Classical

variable {σ J K : Type*} [Fintype σ] [Fintype J] {idx D m d w b p : ℕ}
local notation "Tape" => Input σ idx D J m d w b

/-- A grid tuple is accepted only if all limb vectors encode nonzero field elements. -/
noncomputable def valid (p : ℕ) : BooleanNetwork (Fintype.card Tape) 1 :=
  gridGuard p fun i => route (gridWire ((Fintype.equivFin (Option σ)).symm i))

/-- Every grid coordinate, including the Laurent parameter, is checked. -/
theorem valid_eval (hp : p < 2^w) (query : Query σ idx D J m → Bool)
    (grid : Option σ → Fin (d*w) → Bool) (y : Fin b → Bool) :
    (valid p).eval (number (Sum.elim query (encodeGuess grid y))) 0 = true ↔
      ∀ i, validLimbs p (limbWords d w (grid i)) := by
  rw [valid,gridGuard_eval hp]
  simp only [route_eval]
  have read (i : Option σ) : Sum.elim query (encodeGuess grid y) ∘ gridWire i = grid i := rfl
  simp only [read]
  constructor
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h (Fintype.equivFin _ i)
  · intro h i
    exact h _

/-- The grid guard checks a polynomial number of binary limbs. -/
theorem valid_count (p : ℕ) :
    (valid (σ := σ) (idx := idx) (D := D) (J := J) (m := m) (d := d) (w := w) (b := b) p).net.count ≤
      Fintype.card (Option σ)*((d*(49*w+9)+d*(49*w+12)+3)+1)+1 := by
  exact (gridGuard_count (p := p) _ 0 (fun _ => le_rfl)).trans_eq (by simp)

/-- Final threshold word as supplied by the private guess. -/
noncomputable def yNet : BooleanNetwork (Fintype.card Tape) b := route thresholdWire

/-- Reading the threshold costs zero gates. -/
theorem yNet_count : (yNet (σ := σ) (idx := idx) (D := D) (J := J) (m := m)
    (d := d) (w := w) (b := b)).net.count = 0 := rfl

/-- The threshold reads all bits in their incoming little-endian order. -/
theorem yNet_eval (query : Query σ idx D J m → Bool)
    (grid : Option σ → Fin (d*w) → Bool) (y : Fin b → Bool) :
    yNet.eval (number (Sum.elim query (encodeGuess grid y))) = y := by
  rw [yNet,route_eval]
  rfl

variable [Field K] [Fact p.Prime] [Algebra (ZMod p) K]

/-- Feed the raw column address followed by the terminal register to the
advised table of prime-field coordinate functionals. -/
noncomputable def project (width : ℕ) (B : Module.Basis (Fin d) (ZMod p) K)
    (π : Fin D → K →ₗ[ZMod p] ZMod p) : BooleanNetwork (Fintype.card (Input σ idx D J m d width b)+d*width) width :=
  let T := Input σ idx D J m d width b
  let column := select fun j => ((Fintype.equivFin T) (addressWire true j)).castAdd (d*width)
  let register := select (Fin.natAdd (Fintype.card T))
  (column.pair register).comp (ResidueEntryBasis.projectionLookup _ width B π)

/-- The linear functional selected from the tape is exactly the queried column's
functional on the represented field register. -/
theorem project_eval (hp : p < 2^w) (B : Module.Basis (Fin d) (ZMod p) K)
    (π : Fin D → K →ₗ[ZMod p] ZMod p) (H : ℕ) (e μ k : Exponent σ)
    (row col : Fin D) (δ : J → ℕ) (grid : Option σ → Fin (d*w) → Bool)
    (y : Fin b → Bool) (z : Fin (d*w) → Bool) (a : K) (hz : Represents B z a) :
    value ((project (idx := idx) (m := m) w B π).eval (Fin.append
      (number (Sum.elim (encodeQuery idx H m e μ k row col δ) (encodeGuess grid y))) z)) =
        (π col a).val := by
  let tape : Tape → Bool := Sum.elim (encodeQuery idx H m e μ k row col δ) (encodeGuess grid y)
  let f := Fin.append (number tape) z
  have left : f ∘ (fun j => ((Fintype.equivFin Tape) (addressWire true j)).castAdd (d*w)) =
      addressWord col := by
    funext j
    simp only [f,Function.comp_apply,Fin.append_left,number,Equiv.symm_apply_apply]
    rfl
  have right : f ∘ Fin.natAdd (Fintype.card Tape) = z := funext (fun _ => Fin.append_right ..)
  change value ((project w B π).eval f) = _
  rw [project,eval_comp,eval_pair,eval_select,eval_select,left,right]
  exact ResidueEntryBasis.projectionLookup_at (Nat.le_pow_clog Nat.one_lt_two _) hp B π
    _ col (addressWord_value col) z a hz

/-- The routing before the projection table adds no gates. -/
theorem project_count (B : Module.Basis (Fin d) (ZMod p) K)
    (π : Fin D → K →ₗ[ZMod p] ZMod p) :
    (project (σ := σ) (idx := idx) (J := J) (m := m) (b := b) w B π).net.count ≤
      ResidueEntryBasis.lookupBudget D w (Nat.clog 2 D) (w+d*(w+limbCost w+limbCost w)) := by
  simpa only [project,count_comp,count_pair,count_select,zero_add] using
    ResidueEntryBasis.projectionLookup_count (r := Nat.clog 2 D) (w := w) B π

end ResidueEntryOutput

end BorderVNP
end Computability
end OAI
