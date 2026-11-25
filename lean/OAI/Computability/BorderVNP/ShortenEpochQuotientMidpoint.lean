import OAI.Computability.BorderVNP.CoverLorentzProduct
import OAI.Computability.BorderVNP.ShortenEpochSegments

/-! # Midpoints of actual quotient wires -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Epoch

variable {I : Type*} [Fintype I]

/-- Every product-surface endpoint pair admits a genuine distance midpoint,
including zero-length feeders and pairs separated by a nontrivial deck move. -/
theorem exists_surface_midpoint {d : ℕ} (x y : SurfaceHost I d) :
    ∃ u : SurfaceHost I d, dist u x = dist x y / 2 ∧ dist u y = dist x y / 2 := by
  by_cases h : x = y
  · subst y; exact ⟨x,by simp,by simp⟩
  obtain ⟨a,ha,_⟩ := productProjection_closest_lift (productChart (0 : PiLp 2 (fun _ : I => ℂ))) x
  obtain ⟨b,hb,hd⟩ := productProjection_closest_lift a y
  rw [ha] at hd
  have hab : a ≠ b := fun he => h (ha.symm.trans ((congrArg _ he).trans hb))
  obtain ⟨c,v,hv,hl,hr⟩ := exists_product_midpoint_line a b hab
  let z := shiftTo c (productLine v 0)
  have hz (t : ℝ) : dist z (shiftTo c (productLine v t)) = |t| := by
    rw [shiftTo_isometry c |>.dist_eq,dist_productLine,zero_sub,abs_neg,hv,mul_one]
  have da : dist (productProjection d z) x ≤ dist x y / 2 := by
    calc
      _ = dist (productProjection d z) (productProjection d a) := by rw [ha]
      _ ≤ dist z a := productProjection_dist_le d z a
      _ = dist x y / 2 := by rw [← hl,hz,abs_neg,abs_of_nonneg (by positivity),hd]
  have db : dist (productProjection d z) y ≤ dist x y / 2 := by
    calc
      _ = dist (productProjection d z) (productProjection d b) := by rw [hb]
      _ ≤ dist z b := productProjection_dist_le d z b
      _ = dist x y / 2 := by rw [← hr,hz,abs_of_nonneg (by positivity),hd]
  have tri := dist_triangle x (productProjection d z) y
  rw [dist_comm x (productProjection d z)] at tri
  exact ⟨productProjection d z,by linarith only [da,db,tri],by linarith only [da,db,tri]⟩

/-- A fixed midpoint for each quotient endpoint pair. -/
noncomputable def surfaceMidpoint {d : ℕ} (x y : SurfaceHost I d) :=
  (exists_surface_midpoint x y).choose

/-- Both incident half-lengths of the chosen midpoint. -/
theorem surfaceMidpoint_dist {d : ℕ} (x y : SurfaceHost I d) :
    dist (surfaceMidpoint x y) x = dist x y / 2 ∧ dist (surfaceMidpoint x y) y = dist x y / 2 :=
  (exists_surface_midpoint x y).choose_spec

end Cover

end BorderVNP
end Computability
end OAI
