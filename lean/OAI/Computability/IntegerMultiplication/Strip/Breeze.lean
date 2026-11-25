import OAI.Computability.IntegerMultiplication.Spindle.Mint

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code
variable {I : Type} {r : Regime I} {n l : I→ℕ} {f g : I→ℝ} {p q v u : I→Tree}

abbrev runrate (f : I → ℝ) (r : Regime I) (n l : I→ℕ) (k : ℕ) :=
  fun i => mass r n l k i*f i

theorem rate_higher (i : I) (z : 1≤f i) {a b : ℕ} (v : a≤b) :
    runrate f r n l a i ≤ runrate f r n l b i := by unfold runrate; gcongr; exact mass_le v _

/-- Factor over fat record mass. -/
def Breeze (f : I→ℝ) (r : Regime I) (n l : I → ℕ) (p q : I→Tree) :=
  (∀ i,1≤f i) ∧ ∃ k,Carries (runrate f r n l k) p q

namespace Breeze
theorem launch (h : Rip r n l p q) (x : ∀ i,1≤f i) :
    Breeze f r n l p q := by
  obtain ⟨k,f⟩ := h
  exact ⟨x,k,f.larger (fun i => le_mul_of_one_le_right (show 0 ≤ mass _ _ _ _ _ by have := f.budget i; linarith) (x i))⟩
theorem next (h : Breeze f r n l p q) (x : Breeze f r n l q v) :
    Breeze f r n l p v := by
  obtain ⟨z,a,u⟩ := h; obtain ⟨_,b,t⟩ := x
  exact ⟨z,a+b,(u.larger (fun i => rate_higher i (z _) (by omega : a≤a+b))).chain
    (t.larger (fun i => rate_higher i (z _) (by omega : b≤a+b)))⟩
theorem pair (h : Breeze f r n l p q) (x : Breeze f r n l p v) :
    Breeze f r n l p (together q v) := by
  obtain ⟨z,a,u⟩ := h; obtain ⟨_,b,t⟩ := x
  exact ⟨z,a+b,(u.larger (fun i => rate_higher i (z _) (by omega : a≤a+b))).twice
    (t.larger (fun i => rate_higher i (z _) (by omega : b≤a+b)))⟩
theorem prepend (h : Breeze f r n l p q) (v : I→Tree) (x : Alive r n l v) :
    Breeze f r n l (together p v) (together q v) := by
  obtain ⟨z,a,u⟩ := h; obtain ⟨_,b,t⟩ := Breeze.launch x z
  exact ⟨z,a+b,(u.larger (fun i => rate_higher i (z _) (by omega : a≤a+b))).first
    (t.larger (fun i => rate_higher i (z _) (by omega : b≤a+b))).out⟩
theorem raise (h : Breeze f r n l p q) (x : ∀ i,f i≤g i) :
    Breeze g r n l p q := by
  obtain ⟨z,a,u⟩ := h; refine ⟨fun i => (z i).trans (x i),a,u.larger fun i => ?_⟩
  unfold runrate; exact mul_le_mul_of_nonneg_left (x i) (by unfold mass; positivity)
theorem along_cast {A : Type} (h : Breeze f r n l p q) (a : A→I) :
    Breeze (f ∘ a) (r.pull a) (n ∘ a) (l ∘ a) (p ∘ a) (q ∘ a) := by
  obtain ⟨z,k,h⟩ := h; exact ⟨fun _ => z _,k,h.slide _⟩
end Breeze
end Strip

end IntegerMultiplication
end Computability
end OAI
