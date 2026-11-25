import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! Polynomial growth bounds for the local scalar instruction counts of a public program. -/
namespace Hierarchy.DescentScalarGrowth
def Polynomial (f : ℕ→ℕ) := ∃C d : ℕ,∀x,f x ≤ C*(x+1)^d

theorem poly_const (n : ℕ) : Polynomial (fun _=>n) := ⟨n,0,by simp⟩
theorem poly_var : Polynomial (fun x=>x) := ⟨1,1,by simp⟩
theorem poly_add {f g : ℕ→ℕ} (left : Polynomial f) (right : Polynomial g) :
    Polynomial (fun x=>f x+g x) := by
  obtain ⟨A,p,hp⟩:=left
  obtain ⟨B,q,hq⟩:=right
  refine ⟨A+B,p+q,fun x=>?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add ((hp x).trans (Nat.mul_le_mul_left A (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right ..))))
    ((hq x).trans (Nat.mul_le_mul_left B (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left ..))))
theorem poly_mul {f g : ℕ→ℕ} (left : Polynomial f) (right : Polynomial g) :
    Polynomial (fun x=>f x*g x) := by
  obtain ⟨A,p,hp⟩:=left
  obtain ⟨B,q,hq⟩:=right
  refine ⟨A*B,p+q,fun x=>(Nat.mul_le_mul (hp x) (hq x)).trans_eq ?_⟩
  rw [pow_add]
  ring


theorem poly_of_le {f g : ℕ→ℕ} (upper : Polynomial g) (bound : ∀x,f x ≤ g x) : Polynomial f := by
  obtain ⟨C,d,small⟩:=upper
  exact ⟨C,d,fun x=>(bound x).trans (small x)⟩

end Hierarchy.DescentScalarGrowth

end OAI
