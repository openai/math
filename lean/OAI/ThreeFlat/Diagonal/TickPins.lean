import OAI.ThreeFlat.Diagonal.PhysicalBlock
import OAI.ThreeFlat.BitNetwork

namespace OAI
/-! # Tick-template pins for a physical block fixing

One common network is used by all teams and all ticks. The team index,
transition, public bits and shared advice enter through the pin function.
The old and new chunk values and the old and new auxiliary words are
read uniquely from a consistent block fixing.
-/

namespace ThreeFlat.Diagonal

variable {F A S : Type*} [Field F] {p q n : ℕ}

/-- The initial word for the first tick, or the preceding tick's output. -/
def beforeWord {A : Type*} : (n : ℕ) → A → (Fin n → A) → Fin n → A
  | 0, _, _ => fun i => i.elim0
  | n+1, a, v => Fin.cons a (beforeWord n (v 0) (fun j => v j.succ))

/-- Every tick sees precisely its predecessor's output. -/
theorem auxProduct_eq_prod (n : ℕ) (K : Fin n → Matrix A A F) (a : A) (v : Fin n → A) :
    auxProduct n K a v = ∏ i, K i (beforeWord n a v i) (v i) := by
  induction n generalizing a with
  | zero => simp [auxProduct]
  | succ n ih =>
    rw [auxProduct, Fin.prod_univ_succ, ih]
    simp only [beforeWord, Fin.cons_zero, Fin.cons_succ]

/-- A single team template, simultaneously instantiated on all transitions
and teams of the block. -/
noncomputable def teamTick (N : BitNetwork F p)
    (pin : Fin n → Fin q → S → S → A → A → Fin p → Bool) (i : Fin n) (x y : S) : Matrix A A F :=
  fun u v => ∏ j, N.eval (pin i j x y u v)

/-- Build exactly the `q * n` pin vectors consumed by the catalytic collapse. -/
def fixingPins (pin : Fin n → Fin q → S → S → A → A → Fin p → Bool)
    (f : BlockFixing n S A) (i : Fin n) (j : Fin q) : Fin p → Bool :=
  pin i j (f.1 i) (f.2.1 i) (beforeWord n f.2.2.1 f.2.2.2 i) (f.2.2.2 i)

/-- The scalar being replaced is the collapse scalar on the actual pins of
this fixing, including every team instance. -/
theorem fixingWeight_eq_template_product (N : BitNetwork F p)
    (pin : Fin n → Fin q → S → S → A → A → Fin p → Bool) (f : BlockFixing n S A) :
    fixingWeight (teamTick N pin) f = ∏ i, ∏ j, N.eval (fixingPins pin f i j) := by
  exact auxProduct_eq_prod n _ _ _

end ThreeFlat.Diagonal

end OAI
