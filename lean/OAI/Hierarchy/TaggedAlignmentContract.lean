import OAI.Hierarchy.TaggedAlign

namespace OAI
/-! # Contracting an aligned block with its padding

The chosen destination addresses and the output payload array are summed
indices of a tagged switch. The adjacent real-address checks and increasing
dummy addresses select exactly one term in that contraction.
-/

namespace Hierarchy.Tagged.Align

open scoped BigOperators Classical
noncomputable section

abbrev Input (r m : ℕ) := Fin r ⊕ Fin (m-r)

def Fits {r m : ℕ} (e : Fin r ↪ Fin m) (guess : Input r m → Fin m) : Prop :=
  (∀ i, guess (.inl i) = e i) ∧ StrictMono (fun j => guess (.inr j))

theorem bijective_fits_iff {r m : ℕ} (e : Fin r ↪ Fin m) (g : Input r m → Fin m) :
    Function.Bijective g ∧ Fits e g ↔ g = complete e := by
  constructor
  · rintro ⟨bij, real, ordered⟩
    have eq := complete_unique e (Equiv.ofBijective g bij) real ordered
    exact congrArg DFunLike.coe eq
  · rintro rfl
    exact ⟨(complete e).bijective, complete_real e, complete_dummy e⟩

theorem alignment_contract {F X : Type*} [CommSemiring F] [Fintype X] {r m : ℕ}
    (e : Fin r ↪ Fin m) (input : Input r m → X) (rest : (Fin m → X) → F) :
    (∑ g : Input r m → Fin m, ∑ output : Fin m → X,
      (if Function.Bijective g ∧ (∀ i, output (g i) = input i) then (1:F) else 0) *
      (if Fits e g then 1 else 0) * rest output) =
    rest (input ∘ (complete e).symm) := by
  classical
  let f := complete e
  have test (g : Input r m → Fin m) (out : Fin m → X) :
      (if Function.Bijective g ∧ (∀ i, out (g i) = input i) then (1:F) else 0) *
      (if Fits e g then 1 else 0) * rest out =
      if g = f ∧ out = input ∘ f.symm then rest out else 0 := by
    by_cases gEq : g = f
    · subst g
      have fits : Fits e f := ((bijective_fits_iff e f).mpr rfl).2
      have payload : (∀ i, out (f i) = input i) ↔ out = input ∘ f.symm := by
        constructor
        · intro h
          funext i
          simpa using h (f.symm i)
        · rintro rfl i
          simp
      by_cases yes : out = input ∘ f.symm
      · have left : Function.Bijective f ∧ ∀ i,out (f i)=input i := ⟨f.bijective,payload.mpr yes⟩
        have right : (f : Input r m → Fin m)=f ∧ out=input ∘ f.symm := ⟨rfl,yes⟩
        rw [ite_eq_left left,ite_eq_left fits,ite_eq_left right,one_mul,one_mul]
      · have left : ¬ (Function.Bijective f ∧ ∀ i,out (f i)=input i) := fun h => yes (payload.mp h.2)
        have right : ¬((f : Input r m → Fin m)=f ∧ out=input ∘ f.symm) := fun h=>yes h.2
        rw [ite_eq_right left,ite_eq_right right,zero_mul,zero_mul]
    · have right : ¬ (g=f ∧ out=input ∘ f.symm) := fun h => gEq h.1
      rw [ite_eq_right right]
      by_cases bij : Function.Bijective g
      · have notFit : ¬ Fits e g := fun hf => gEq ((bijective_fits_iff e g).mp ⟨bij,hf⟩)
        rw [ite_eq_right notFit,mul_zero,zero_mul]
      · have left : ¬ (Function.Bijective g ∧ ∀ i,out (g i)=input i) := fun h => bij h.1
        rw [ite_eq_right left,zero_mul,zero_mul]
  simp_rw [test]
  calc
    _ = ∑ g : Input r m → Fin m, if g = f then rest (input ∘ f.symm) else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      by_cases yes : g = f <;> simp [yes]
    _ = _ := by simp [f]

/-- The prescribed real tags can be checked with only the first tag and each
pair of neighboring real rows. -/
theorem adjacent_real_iff {n d p m : ℕ} (key : Fin (n+1) → Fin d) (e : Fin (n+1) ↪ Fin m)
    (expected : ∀ i, (e i).val = dest p key i) (guess : Fin (n+1) → Fin m) :
    (∀ i, guess i = e i) ↔ (guess 0).val = 0 ∧ ∀ i : Fin n,
      (guess i.succ).val = advance p (guess i.castSucc).val (decide (key i.castSucc ≠ key i.succ)) := by
  constructor
  · intro h
    exact ⟨(congrArg Fin.val (h 0)).trans (expected 0),fun i => by simp only [h,expected,dest_step]⟩
  · rintro ⟨zero, step⟩ i
    apply Fin.ext
    exact (congrFun (dest_unique p key (fun j => (guess j).val) zero step) i).trans (expected i).symm

end
end Hierarchy.Tagged.Align

end OAI
