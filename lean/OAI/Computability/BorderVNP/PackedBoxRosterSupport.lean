import OAI.Computability.BorderVNP.PackedSubdivisionBoxRoster
import OAI.Computability.BorderVNP.DiagonalOriginalRowTree

/-! # Which rows of the fixed physical roster depend on the original factors

Only a copy of a true original site can change when an original factor
array changes. The copy is at its actual cumulative physical offset. This
allows the public one-copy table directory to be built with empty original
bodies and the opaque entries filled separately at the true original rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.BoxRoster

open Crossing Shortening Shortening.Adaptive Shortening.StaticRows Shortening.PublicCapacity CellSparse
open Diagonal.ExternalSew.RowTrace
open scoped Classical

/-- Distinct results of the extended subdivision array come from a changed
original entry at exactly the same numeric address. -/
theorem subdivided_difference {s : Shape} {α : Type*} (extra : ℕ) (a b : Fin s.sites → List α)
    (i : Fin (s.subdivide extra).sites) (h : subdivided extra a i ≠ subdivided extra b i) :
    ∃ v, i.val = v.val ∧ a v ≠ b v := by
  by_cases hi : i.val < s.sites
  · exact ⟨⟨i.val,hi⟩,rfl,by simpa [subdivided,hi] using h⟩
  · simp [subdivided,hi] at h

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (number : e.Entry → ℕ)
variable {k rounds : ℕ} {V : ℕ → ℕ} (seeds : Fin rounds → ℕ)
    (rect : ∀ j : Fin rounds, V (j.val+1) = siteCapacity e (k*V j.val) (seeds j))
    (a b : Fin (V 0) → List (List Factor))

/-- Distinct bodies in the two complete inner rosters identify a genuine
changed input slot and its actual public row-major bundle address. -/
theorem steps_difference (j : ℕ) (hj : j ≤ rounds) (r : Fin (V j))
    (h : steps e number seeds rect a j r ≠ steps e number seeds rect b j r) :
    ∃ (u : Fin (k^j)) (v : Fin (V 0)),
      r.val = flatOffset (fun l (z : Fin k) => z.val*V l) j u + v.val ∧ a v ≠ b v := by
  induction j with
  | zero => exact ⟨0,r,by simp [flatOffset],h⟩
  | succ j ih =>
    have lt : j < rounds := Nat.lt_of_succ_le hj
    let idx : Fin rounds := ⟨j,lt⟩
    let cast := finCongr (rect idx)
    obtain ⟨r',rr⟩ := cast.symm.surjective r
    obtain ⟨z,rfl⟩ := finSumFinEquiv.surjective r'
    subst r
    rcases z with z | z
    · obtain ⟨⟨child,row⟩,rfl⟩ := finProdFinEquiv.surjective z
      have diff : steps e number seeds rect a j row ≠ steps e number seeds rect b j row := by
        simpa only [steps,dite_eq_left lt,cast,finCongr_symm,finCongr_apply,Fin.cast_cast,Fin.cast_refl,id_eq,sewn,parallel,Equiv.symm_apply_apply]
          using h
      obtain ⟨u,v,hr,hv⟩ := ih (Nat.le_of_succ_le hj) row diff
      refine ⟨copyIndex k j (child,u),v,?_,hv⟩
      rw [flatOffset_succ]
      change row.val+V j*child.val = child.val*V j + flatOffset _ j u + v.val
      rw [hr,Nat.mul_comm (V j) child.val]
      omega
    · have same : steps e number seeds rect a (j+1) (cast.symm (finSumFinEquiv (.inr z))) =
          steps e number seeds rect b (j+1) (cast.symm (finSumFinEquiv (.inr z))) := by
        simp only [steps,dite_eq_left lt,cast,finCongr_symm,finCongr_apply,Fin.cast_cast,Fin.cast_refl,id_eq,sewn,Equiv.symm_apply_apply]
      exact (h same).elim

end Packing.Inherited.BoxRoster

end BorderVNP
end Computability
end OAI
