import OAI.Computability.BorderVNP.FiniteOutputProduct
import OAI.Computability.BorderVNP.CellSparseSemantics

/-! # Field powers from checked cell multiplicities

The weighted field validator reads the little-endian binary count at each
table position. A control state remembers the current base and squares it at
the next bit. The program scans each reported bit once and has no guesses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldPowers

open VPVNP.RAMTape

/-- Natural value of little-endian count bits. -/
def digits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2*digits bs

/-- Reading designated addresses from the assignment bank supplies exactly the
integer that the sparse cell checker compares with the actual multiplicity. -/
theorem digits_map (bank : ℕ → Bool) (indices : List ℕ) :
    digits (indices.map bank) = CellSparse.word bank indices := by
  induction indices with
  | nil => rfl
  | cons j js ih => cases h : bank j <;> simp [digits, CellSparse.word, h, ih]

/-- Descending table-position loop, bit reader, and weighted transition. -/
inductive State (k f : ℕ) where
  | visit (left : Fin (k+1))
  | read (idx : Fin k) (base : Fin f)
  | useBit (idx : Fin k) (base : Fin f) (bit : Bool)
  deriving DecidableEq, Fintype

variable {F : Type*} [Field F] [Fintype F] {k : ℕ}

/-- A fixed field position has one input stack carrying the bits of its reported count. -/
noncomputable def program (v : Fin k → F) : StackCode (Fin k) (State k (Fintype.card F))
  | .visit l => if h : l.val = 0 then .halt true else
      let i : Fin k := ⟨l.val-1, by have := l.isLt; omega⟩
      .goto (.read i (Fintype.equivFin F (v i)))
  | .read i base => .pop i (fun z => z.elim (.visit i.castSucc) (.useBit i base))
  | .useBit i base _ => .goto (.read i (Fintype.equivFin F ((Fintype.equivFin F).symm base ^ 2)))

/-- Only a set count bit contributes the current power of the field scalar. -/
noncomputable def factor : State k (Fintype.card F) → F
  | .useBit _ base true => (Fintype.equivFin F).symm base
  | _ => 1

private theorem read_loop (v : Fin k → F) (i : Fin k) (bits : List Bool) (fuel : ℕ)
    (base : F) (s : Stacks (Fin k)) (hs : s i = bits) :
    FieldStack.productPaths (program v) factor (fun _ => 1) (2*bits.length+1+fuel)
      (.read i (Fintype.equivFin F base)) s =
    base ^ digits bits * FieldStack.productPaths (program v) factor (fun _ => 1) fuel
      (.visit i.castSucc) (Function.update s i []) := by
  induction bits generalizing base s with
  | nil =>
    rw [show 2*List.length ([] : List Bool)+1+fuel = fuel+1 by simp; omega]
    simp [FieldStack.productPaths, program, factor, hs, digits]
  | cons b bs ih =>
    rw [show 2*(b::bs).length+1+fuel = (2*bs.length+1+fuel)+1+1 by simp; omega]
    simp only [FieldStack.productPaths, program, factor, hs, List.head?_cons, List.tail_cons,
      Option.elim_some, Equiv.symm_apply_apply, one_mul]
    rw [ih (base^2) (Function.update s i bs) (Function.update_self ..)]
    simp only [Function.update_idem, digits, pow_add, pow_mul, mul_assoc]
    cases b <;> simp

private theorem visit_step (v : Fin k → F) (i : Fin k) (s : Stacks (Fin k)) (fuel : ℕ) :
    FieldStack.productPaths (program v) factor (fun _ => 1) (2*(s i).length+2+fuel) (.visit i.succ) s =
    v i ^ digits (s i) * FieldStack.productPaths (program v) factor (fun _ => 1) fuel
      (.visit i.castSucc) (Function.update s i []) := by
  rw [show 2*(s i).length+2+fuel = (2*(s i).length+1+fuel)+1 by omega]
  simpa [FieldStack.productPaths, program, factor] using read_loop v i (s i) fuel (v i) s rfl

/-- With `j` remaining positions, the deterministic program takes two transitions per
bit and two per visited position, then one terminal instruction. -/
theorem visit_value (v : Fin k → F) (j : ℕ) (hj : j ≤ k) (s : Stacks (Fin k)) :
    let read : Fin j → Fin k := Fin.castLE hj
    FieldStack.productPaths (program v) factor (fun _ => 1)
      (1 + ∑ i : Fin j, (2*(s (read i)).length+2)) (.visit ⟨j,by omega⟩) s =
    ∏ i : Fin j, v (read i) ^ digits (s (read i)) := by
  induction j generalizing s with
  | zero => simp [FieldStack.productPaths, program, factor]
  | succ j ih =>
    dsimp only
    let p : Fin k := ⟨j,by omega⟩
    let hle : j ≤ k := by omega
    let r : Fin j → Fin k := Fin.castLE hle
    have cast₁ (i : Fin j) : Fin.castLE hj i.castSucc = r i := rfl
    have cast₂ : Fin.castLE hj (Fin.last j) = p := rfl
    have neq (i : Fin j) : r i ≠ p := by intro he; have hv := congrArg Fin.val he; exact i.isLt.ne hv
    rw [Fin.sum_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [cast₁, cast₂]
    have he : (⟨j+1,by omega⟩ : Fin (k+1)) = p.succ := rfl
    rw [he, show 1 + ((∑ i : Fin j, (2*(s (r i)).length+2)) + (2*(s p).length+2)) =
      (2*(s p).length+2) + (1 + ∑ i : Fin j, (2*(s (r i)).length+2)) by omega, visit_step]
    have h := ih hle (Function.update s p [])
    change FieldStack.productPaths (program v) factor (fun _ => 1)
      (1 + ∑ i : Fin j, (2*((Function.update s p []) (r i)).length+2)) (.visit p.castSucc)
      (Function.update s p []) = ∏ i : Fin j, v (r i) ^ digits (Function.update s p [] (r i)) at h
    simp only [Function.update_of_ne (neq _)] at h
    rw [h,mul_comm]

/-- The full finite control computes the exact product of powers of all reported entries. -/
theorem evaluate (v : Fin k → F) (s : Stacks (Fin k)) :
    FieldStack.productPaths (program v) factor (fun _ => 1)
      (1 + ∑ i, (2*(s i).length+2)) (.visit (Fin.last k)) s =
      ∏ i, v i ^ digits (s i) := visit_value v k le_rfl s

end FieldPowers

end BorderVNP
end Computability
end OAI
