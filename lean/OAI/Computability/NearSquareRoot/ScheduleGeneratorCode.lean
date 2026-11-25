import Mathlib.Computability.TuringMachine.Config
import Mathlib.Computability.Primrec.List

/-!
# Effective generation of a finite ROM word

A computable family of finite words has one index-to-word program in the
list instruction language compiled by Mathlib's Turing-machine construction.
The emitted list contains the symbols of the word in order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator

open Turing.ToPartrec

private theorem scalar_code (f : ℕ → ℕ) (hf : Computable f) :
    ∃ c : Code, ∀ i, c.eval [i] = Part.some [f i] := by
  obtain ⟨c, hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf)
  exact ⟨c, fun i => hc (List.Vector.cons i List.Vector.nil)⟩

private theorem scalar_code₂ (f : ℕ → ℕ → ℕ) (hf : Computable₂ f) :
    ∃ c : Code, ∀ i j, c.eval [i,j] = Part.some [f i j] := by
  obtain ⟨c,hc⟩ := Code.exists_code
    ((Nat.Partrec'.part_iff₂ (f := fun i j => Part.some (f i j))).mpr hf)
  exact ⟨c, fun i j => hc (List.Vector.cons i (List.Vector.cons j List.Vector.nil))⟩

private def listStep (element : Code) : Code :=
  let second : Code := .comp .head .tail
  let firstTwo : Code := .cons .head second
  let suffix : Code := .comp .tail .tail
  let prepend : Code := .cons (.comp element firstTwo) suffix
  let next : Code := .cons .head (.cons second prepend)
  .case (.comp .zero' .tail) (.cons (.comp .succ .zero) next)

private theorem listStep_zero (element : Code) (i : ℕ) (suffix : List ℕ) :
    (listStep element).eval (0 :: i :: suffix) = Part.some (0 :: suffix) := by
  simp [listStep]

set_option backward.isDefEq.respectTransparency false in
private theorem listStep_succ (f : ℕ → ℕ → ℕ) (element : Code)
    (he : ∀ j i, element.eval [j,i] = Part.some [f j i])
    (j i : ℕ) (suffix : List ℕ) :
    (listStep element).eval ((j+1) :: i :: suffix) =
      Part.some (1 :: j :: i :: f j i :: suffix) := by
  simp [listStep,he,Bind.bind,Part.bind_some,Part.pure_eq_some]

private theorem fill_suffix (f : ℕ → List ℕ) (element : Code)
    (he : ∀ j i, element.eval [j,i] = Part.some [(f i).getD j 0])
    (i j : ℕ) (hj : j ≤ (f i).length) :
    (Code.fix (listStep element)).eval (j :: i :: (f i).drop j) = Part.some (f i) := by
  rw [Part.eq_some_iff,Code.fix_eval]
  induction j with
  | zero =>
    apply PFun.mem_fix_iff.mpr (Or.inl ?_)
    rw [listStep_zero]
    simp
  | succ j ih =>
    have hj' : j < (f i).length := hj
    refine PFun.mem_fix_iff.mpr (Or.inr ⟨j :: i :: (f i).drop j, ?_, ih hj'.le⟩)
    rw [listStep_succ _ _ he]
    simp only [Part.map_some,List.headI_cons,one_ne_zero,ite_false,List.tail_cons,
      Part.mem_some_iff,Sum.inr.injEq,List.cons.injEq,true_and]
    rw [List.drop_eq_getElem_cons hj']
    simp [List.getD,hj']

set_option backward.isDefEq.respectTransparency false in
/-- The single compiled program emits the full generated record stream for any index. -/
theorem exists_list_code (f : ℕ → List ℕ) (hf : Computable f) :
    ∃ c : Code, ∀ i, c.eval [i] = Part.some (f i) := by
  obtain ⟨len, hlen⟩ := scalar_code _ (Computable.list_length.comp hf)
  have indexed : Computable₂ (fun j i => (f i).getD j 0) :=
    ((Primrec.list_getD 0).to_comp.comp (hf.comp Computable.snd) Computable.fst).to₂
  obtain ⟨elt, helt⟩ := scalar_code₂ _ indexed
  refine ⟨.comp (.fix (listStep elt)) (.cons len .id), fun i => ?_⟩
  have h := fill_suffix f elt helt i (f i).length le_rfl
  simpa [hlen,Bind.bind,Part.bind_some,Part.pure_eq_some] using h

/-- A total finite-certificate search gives one computable selector. The cost
of finding the first passing certificate can depend arbitrarily on the index. -/
theorem first_certificate (test : ℕ → ℕ → Bool) (ht : Computable₂ test)
    (exists_valid : ∀ i, ∃ k, test i k = true) :
    ∃ select : ℕ → ℕ, Computable select ∧
      ∀ i, test i (select i) = true ∧ ∀ k < select i, test i k = false := by
  let search (i : ℕ) := Nat.rfind (fun k => Part.some (test i k))
  have dom (i : ℕ) : (search i).Dom := by
    obtain ⟨k,hk⟩ := exists_valid i
    obtain ⟨v,hv,_⟩ := Nat.rfind_min' hk
    exact hv.1
  let select (i : ℕ) := (search i).get (dom i)
  have ans (i : ℕ) : select i ∈ search i := Part.get_mem _
  have proc : Partrec search := Partrec.rfind (p := fun i k => Part.some (test i k)) ht
  refine ⟨select, proc.of_eq (fun i => Part.eq_some_iff.mpr (ans i)), fun i => ?_⟩
  exact ⟨(Part.mem_some_iff.mp (Nat.rfind_spec (ans i))).symm,
    fun k hk => (Part.mem_some_iff.mp (Nat.rfind_min (ans i) hk)).symm⟩

/-- Search, check, and emit the complete word for the first passing candidate. -/
theorem exists_searched_code (test : ℕ → ℕ → Bool) (ht : Computable₂ test)
    (hex : ∀ i, ∃ k, test i k = true) (emit : ℕ → ℕ → List ℕ) (he : Computable₂ emit) :
    ∃ c : Code, ∀ i, ∃ k, test i k = true ∧
      (∀ j < k, test i j = false) ∧ c.eval [i] = Part.some (emit i k) := by
  obtain ⟨select,hs,hsel⟩ := first_certificate test ht hex
  obtain ⟨c,hc⟩ := exists_list_code _ (he.comp Computable.id hs)
  exact ⟨c,fun i => ⟨select i,(hsel i).1,(hsel i).2,hc i⟩⟩

/-- A positive terminator allows the instruction language to distinguish the end of
the unary input from another zero marker. -/
def unaryInput (i : ℕ) : List ℕ := List.replicate i 0 ++ [1]

private def countStep : Code :=
  let continueCount : Code := .cons (.comp .succ .zero) (.cons .succ (.comp .tail .tail))
  let finishCount : Code := .comp (.cons .zero .head) .tail
  .comp (.case continueCount finishCount) (.cons .tail .id)

private theorem countStep_stop (acc : ℕ) :
    countStep.eval [acc,1] = Part.some [0,acc] := by
  simp [countStep]

private theorem countStep_more (acc : ℕ) (rest : List ℕ) :
    countStep.eval (acc :: 0 :: rest) = Part.some (1 :: (acc+1) :: rest) := by
  simp [countStep]

private theorem count_unary (i acc : ℕ) :
    (Code.fix countStep).eval (acc :: unaryInput i) = Part.some [acc + i] := by
  rw [Part.eq_some_iff,Code.fix_eval]
  induction i generalizing acc with
  | zero =>
    apply PFun.mem_fix_iff.mpr (Or.inl ?_)
    rw [show acc :: unaryInput 0 = [acc,1] from rfl,countStep_stop]
    simp
  | succ j ih =>
    refine PFun.mem_fix_iff.mpr (Or.inr ⟨(acc+1) :: unaryInput j, ?_, ?_⟩)
    · rw [show unaryInput (j+1) = 0 :: unaryInput j by simp [unaryInput,List.replicate_succ],
        countStep_more]
      simp
    · simpa only [show acc + 1 + j = acc + (j+1) by omega] using ih (acc+1)

set_option backward.isDefEq.respectTransparency false in
/-- One list program reads the scheduler's unary index, converts it to the scalar
index, and emits its whole generated ROM word. -/
theorem exists_unary_list_code (f : ℕ → List ℕ) (hf : Computable f) :
    ∃ c : Code, ∀ i, c.eval (unaryInput i) = Part.some (f i) := by
  obtain ⟨gen,hgen⟩ := exists_list_code f hf
  refine ⟨.comp gen (.comp (.fix countStep) .zero'), fun i => ?_⟩
  simp only [Code.comp_eval,Code.zero'_eval,Part.pure_eq_some,Part.bind_eq_bind,
    Part.bind_some,count_unary,Nat.zero_add,hgen]

end Generator

end NearSquareRoot
end Computability
end OAI
