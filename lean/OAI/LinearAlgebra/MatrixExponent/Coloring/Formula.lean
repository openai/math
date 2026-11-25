import OAI.LinearAlgebra.MatrixExponent.Coloring.Edges
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort

noncomputable section

/-! # Indexing the three stages of a product permutation -/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

structure Chart (h : ℕ) where
  base : B h → B h
  location : B h → B h
  mask : B h → Bool
  support : Finset (B h)
  degree : ℕ

namespace Chart

variable {h : ℕ} (p : Chart h)

def label (y : B h → B h) := colours p.support p.degree p.base (p.base ∘ y) p.mask

def route (b c : B h → B h) (i : B h) : B h :=
  if p.mask i then p.location (b i + c i) else i

def left (y : B h → B h) := p.route p.base (p.label y)
def right (y : B h → B h) := p.route (p.base ∘ y) (p.label y)

def run (inv : (B h → B h) → (B h → B h)) (y : B h → B h) :=
  (y ∘ inv (p.right y), p.right y ∘ inv (p.left y), p.left y)

end Chart
end OAI.LinearAlgebra.MatrixExponent.Coloring
end

/-!
# Checking relations on a finite alphabet in parallel

Reject malformed encodings. The relation can be an arbitrary finite
table. Only the address inputs have unbounded width.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring

open scoped Classical
variable {V : Type*} {t q : ℕ} (e : V ↪ B q) (R : V → (B t → V) → Prop)

def encode (V : Type*) [Fintype V] : V ↪ B (Fintype.card V) :=
  (Fintype.equivFin V).toEmbedding.trans (Fin.castLEEmb Nat.lt_two_pow_self.le)

def test (x : B q × (B t → B q)) : Bool :=
  decide (∃ y z, e y = x.1 ∧ e ∘ z = x.2 ∧ R y z)

def check (h : ℕ) (x : (B h → B q) × (B t → B h → B h)) (i : B h) : Bool :=
  test e R (x.1 i, fun j => x.1 (x.2 j i))

theorem check_iff (h : ℕ) (x : B h → B q) (g : B t → B h → B h) :
    (∀ i, check e R h (x, g) i = true) ↔
      ∃! y : B h → V, e ∘ y = x ∧ ∀ i, R (y i) (fun j => y (g j i)) := by
  simp only [check, test, decide_eq_true_eq]
  constructor
  · intro H
    choose y z hy hz he using H
    refine ⟨y, ⟨funext hy, fun i => ?_⟩, fun w hw => funext fun i => ?_⟩
    · have hh : z i = fun j => y (g j i) :=
        funext fun j => e.injective ((congrFun (hz i) j).trans (hy _).symm)
      rw [← hh]
      exact he i
    · exact e.injective ((congrFun hw.1 i).trans (hy i).symm)
  · rintro ⟨y, ⟨rfl, hy⟩, _⟩ i
    exact ⟨y i, fun j => y (g j i), rfl, rfl, hy i⟩

theorem cheap_check (F : Type) [Field F] :
    ∃ k₀, ∀ h k : ℕ, h ≤ k → k₀ ≤ k →
      Cheap F h k (.pair (.vec h (.addr q)) (.vec t (Perm h))) (.vec h .bit)
        (check e R h) 17 := by
  let A := Format.addr q
  let Y := Format.pair A (.vec t A)
  let k₀ := 2 * Y.width + Format.bit.width + Install.localCost Y.width * Format.bit.width
  refine ⟨max k₀ (max A.width (2 ^ t)), fun h k hh hk => ?_⟩
  obtain ⟨hl, ht⟩ := max_le_iff.mp hk
  obtain ⟨ha, ht⟩ := max_le_iff.mp ht
  let X := Format.pair (.vec h A) (.vec t (Perm h))
  have g := Cheap.neighbors F A h k t hh ha ht
  have hx : X.width ≤ 2 ^ h * (100 + k) ^ 12 := by
    obtain ⟨m, _, hm⟩ := g
    exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hm)
  have hf : Cheap F 0 k Y .bit (test e R) 1 := Cheap.fixed F _ hl
  have hv := Cheap.map (A := Y) (D := .bit) (h := h) (fun _ => test e R) (fun _ => hf)
  have ans := (((Cheap.id F hx).fst.pair g).zip).comp hv
  simp only [Function.comp_def, id_eq] at ans
  exact ans

end OAI.LinearAlgebra.MatrixExponent.Coloring
end
