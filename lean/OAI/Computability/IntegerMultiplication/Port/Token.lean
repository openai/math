import Mathlib

/-! Interpreting finitely many rational constants in Z/q^e.
A ticket uses any denominator unit at the given modulus. -/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Port
variable {R : Type} [CommRing R]

def Token (t : ℚ) (v : R) :=
  ∃ d u : ℤ, IsUnit (d:R) ∧ (d:R)*v=(u:R) ∧ (d:ℚ)*t=u
namespace Token
variable {t s : ℚ} {v w : R}
theorem unique (h : Token t v) (e : Token t w) : v=w := by
  obtain ⟨a,b,x,f,g⟩ := h; obtain ⟨c,d,y,i,j⟩ := e
  have hh : a*d=c*b := by
    have : (a:ℚ)*d=(c:ℚ)*b := by rw [← g, ← j,mul_left_comm]
    exact_mod_cast this
  apply (IsUnit.mul_right_inj (x.mul y)).mp
  calc
   _ = (c:R)*((a:R)*v) := by ring
   _ = (a:R)*((c:R)*w) := by rw [i,show (a:R)*v=b from f,← Int.cast_mul,← hh]; simp
   _ = _ := by ring

theorem whole (a : ℤ) : Token (↑a) (↑a:R) :=
  ⟨1,a,by simp⟩
protected theorem nat (a : ℕ) : Token (a:ℚ) (a:R) := by exact_mod_cast (whole (R:=R) (a:ℤ))
protected theorem unit : Token 1 (1:R) := by simpa using (whole (R:=R) 1)
protected theorem zero : Token 0 (0:R) := by simpa using (whole (R:=R) 0)
protected theorem add (h : Token t v) (e : Token s w) : Token (t+s) (v+w) := by
  obtain ⟨a,b,x,f,g⟩ := h; obtain ⟨c,d,y,i,j⟩ := e
  refine ⟨a*c,c*b+a*d, by rw [Int.cast_mul]; exact x.mul y,?_,?_⟩
  · calc
     _ = (c:R)*((a:R)*v)+(a:R)*((c:R)*w) := by push_cast; ring
     _ = _ := by rw [f,i]; push_cast; rfl
  calc
   _ = (c:ℚ)*((a:ℚ)*t)+(a:ℚ)*((c:ℚ)*s) := by push_cast; ring
   _ = _ := by rw [g,j]; push_cast; rfl
protected theorem mul (h : Token t v) (e : Token s w) : Token (t*s) (v*w) := by
  obtain ⟨a,b,x,f,g⟩ := h; obtain ⟨c,d,y,i,j⟩ := e
  refine ⟨a*c,b*d, by rw [Int.cast_mul]; exact x.mul y,?_,?_⟩
  · calc
     _ = ((a:R)*v)*((c:R)*w) := by push_cast; ring
     _ = _ := by rw [f,i]; push_cast; rfl
  calc
   _ = ((a:ℚ)*t)*((c:ℚ)*s) := by push_cast; ring
   _ = _ := by rw [g,j]; push_cast; rfl
protected theorem neg (h : Token t v) : Token (-t) (-v) := by
  obtain ⟨a,b,x,f,g⟩ := h
  exact ⟨a,-b,x,by simp [f],by simp [g]⟩
protected theorem sub (h : Token t v) (e : Token s w) : Token (t-s) (v-w) := by
  simpa [sub_eq_add_neg] using h.add e.neg

theorem inv (h : Token t v) (u : Rˣ) (hv : ↑u=v) (ht : t≠0) : Token (t⁻¹) ((↑u⁻¹:R)) := by
  subst v
  obtain ⟨a,b,x,f,g⟩ := h
  refine ⟨b,a,f ▸ x.mul u.isUnit,?_,?_⟩
  · rw [← f,mul_assoc,Units.mul_inv, mul_one]
  rw [← g,mul_assoc,mul_inv_cancel₀ ht,mul_one]

end Token
end Port

end IntegerMultiplication
end Computability
end OAI
