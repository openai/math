import OAI.Computability.IntegerMultiplication.Fourier.Phase

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
variable (n : ℕ) [NeZero n]

abbrev Spot (n : ℕ) := Fin n
abbrev Arr (n : ℕ) (X : Type*) := Fin n → X

/-- Use integer formulas for index shifts. -/
def rep {n : ℕ} (x : Spot n) : ℤ := x.val

def wrap (i : ℤ) : Spot n :=
  ⟨(i%(n:ℤ)).toNat, by
    have h₁ : 0 ≤ i%(n:ℤ) := Int.emod_nonneg _ (by exact_mod_cast NeZero.ne n)
    have h₂ : i%(n:ℤ)<(n:ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
    omega⟩

@[simp] theorem rep_wrap (i : ℤ) : rep (wrap n i)=i%(n:ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne n))

omit [NeZero n] in
@[simp] theorem rep_nonneg (x : Spot n) : 0 ≤ rep x := (Int.natCast_nonneg _)

omit [NeZero n] in
theorem rep_lt (x : Spot n) : rep x<n := by unfold rep; exact_mod_cast x.isLt

@[simp]
theorem wrap_rep (x : Spot n) : wrap n (rep x)=x := by
  have : rep (wrap n (rep x)) = rep x := by rw [rep_wrap, Int.emod_eq_of_lt (rep_nonneg ..) (rep_lt n x)]
  change (↑_ : ℤ)=↑_ at this
  exact Fin.ext (Int.natCast_inj.mp this)

theorem wrap_eq (i j : ℤ) : wrap n i = wrap n j ↔ i ≡ j [ZMOD (n:ℤ)] :=
  ⟨fun h => by simpa [Int.ModEq] using congrArg rep h, fun h => by
    have e : rep (wrap n i)=rep (wrap n j) := by simpa [Int.ModEq] using h
    exact Fin.ext (Int.natCast_inj.mp e)⟩

@[simp] theorem wrap_phase (i : ℤ) : phase n (rep (wrap n i))=phase n i := by
  rw [rep_wrap, phase_inj]
  apply Int.modEq_iff_dvd.mp
  -- i ≡ i % n
  simp [Int.ModEq]

theorem phase_congr {i j : ℤ} (h : wrap n i=wrap n j) : phase n i=phase n j := by
  rw [phase_inj]
  exact Int.modEq_iff_dvd.mp ((wrap_eq n j i).mp h.symm)

theorem wrap_replace (i : ℤ) : wrap n (i%(n:ℤ))=wrap n i := by simp [wrap_eq,Int.ModEq]

theorem wrap_add (x : Spot n) (i j : ℤ) :
    wrap n (rep (wrap n (rep x+i))+j)=wrap n (rep x+(i+j)) := by
  rw [wrap_eq,rep_wrap]
  have e : (rep x+i)%(n : ℤ) ≡ rep x+i [ZMOD (n : ℤ)] := by simp [Int.ModEq]
  simpa [add_assoc] using e.add_right j

theorem wrap_mul (i j : ℤ) :
    wrap n (rep (wrap n i)*j) = wrap n (i*j) := by
  rw [wrap_eq, rep_wrap]
  have e : i%(n : ℤ) ≡ i [ZMOD (n:ℤ)] := by simp [Int.ModEq]
  exact e.mul_right j

def rotation (i : ℤ) : Equiv.Perm (Spot n) :=
  { toFun := fun x => wrap n (rep x+i)
    invFun := fun x => wrap n (rep x+-i)
    left_inv := fun x => by beta_reduce; rw [wrap_add]; simp
    right_inv := fun x => by beta_reduce; rw [wrap_add]; simp }

theorem sum_rotate {X : Type*} [AddCommMonoid X] (f : Fin n → X) (i : ℤ) :
    (∑ x : Spot n, f (wrap n (rep x+i)))=∑ x : Spot n, f x :=
  Equiv.sum_comp (rotation n i) f

end Fourier

end IntegerMultiplication
end Computability
end OAI
