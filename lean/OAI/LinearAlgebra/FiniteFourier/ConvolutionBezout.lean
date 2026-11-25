import OAI.LinearAlgebra.FiniteFourier.OpenConvolution
import OAI.LinearAlgebra.FiniteFourier.CircuitRingCombine

/-! # Integer Bézout assembly of the three open reductions

A linear combination of open reductions keeps all their shorter convolutions
as separate gates. The prime lists give an odd first denominator and a
power of two as the greatest common divisor of the two other denominators.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators

private def selectCircuit {R J T : Type*} [Semiring R] (f : T → J) : Circuit R J T 0 :=
  ⟨.nil, fun i => .scaled 1 (.inl (f i))⟩

private theorem selectCircuit_eval {R J T : Type*} [Semiring R] (f : T → J) (x : J → R) :
    (selectCircuit f).eval x = fun i => x (f i) := by
  funext i
  simp [selectCircuit, Circuit.eval, Readout.eval]

namespace OpenConvolution

variable {R : Type*} [CommRing R] {n : ℕ}
    {B₁ B₂ : Type*} {ℓ₁ : B₁ → ℕ} {ℓ₂ : B₂ → ℕ}

/-- Combine two lists while leaving all child convolutions open. The extra
cost is at most one binary addition with prescribed scalars per output. -/
theorem combine (p : OpenConvolution R n B₁ ℓ₁) (q : OpenConvolution R n B₂ ℓ₂)
    (a b : R) :
    ∃ r : OpenConvolution R n (B₁ ⊕ B₂) (Sum.elim ℓ₁ ℓ₂),
      r.linearCost ≤ p.linearCost + q.linearCost + (2*n-1) ∧
      ∀ x y k, r.eval x y k = a*p.eval x y k + b*q.eval x y k := by
  obtain ⟨s, hs, L, hL⟩ := circuit_fanout p.input q.input
  let ℓ := Sum.elim ℓ₁ ℓ₂
  let LR : Circuit R (Fin n) (Σ u, Fin (ℓ u)) s := ⟨L.program, fun ⟨u, i⟩ =>
    match u with
    | .inl j => L.output (.inl ⟨j,i⟩)
    | .inr j => L.output (.inr ⟨j,i⟩)⟩
  have hL₁ x j i : LR.eval x ⟨Sum.inl j, i⟩ = p.input.eval x ⟨j, i⟩ :=
    congrFun (hL x) (.inl ⟨j, i⟩)
  have hL₂ x j i : LR.eval x ⟨Sum.inr j, i⟩ = q.input.eval x ⟨j, i⟩ :=
    congrFun (hL x) (.inr ⟨j, i⟩)
  let J := Σ u, Fin (2*ℓ u-1)
  let f (v : Σ j, Fin (2*ℓ₁ j-1)) : J := ⟨.inl v.1, v.2⟩
  let g (v : Σ j, Fin (2*ℓ₂ j-1)) : J := ⟨.inr v.1, v.2⟩
  obtain ⟨u, hu, U, hU⟩ := circuit_comp (selectCircuit f) p.output
  obtain ⟨v, hv, V, hV⟩ := circuit_comp (selectCircuit g) q.output
  obtain ⟨t, ht, H, hH⟩ := circuit_sumPair J (Fin (2*n-1)) a b U V
  let r : OpenConvolution R n (B₁ ⊕ B₂) ℓ := ⟨s, t, LR, H⟩
  refine ⟨r, ?_, fun x y k => ?_⟩
  · simp only [Fintype.card_fin] at ht
    dsimp [r, linearCost]
    omega
  · have hf : (fun j => r.children x y (f j)) = p.children x y := by
      funext ⟨j,i⟩
      change openConv R (ℓ₁ j) (fun t => LR.eval x ⟨Sum.inl j,t⟩) _ _ = _
      exact congrArg₂ (fun u v => openConv R (ℓ₁ j) u v i)
        (funext fun t => hL₁ x j t) (funext fun t => hL₁ y j t)
    have hg : (fun j => r.children x y (g j)) = q.children x y := by
      funext ⟨j,i⟩
      change openConv R (ℓ₂ j) (fun t => LR.eval x ⟨Sum.inr j,t⟩) _ _ = _
      exact congrArg₂ (fun u v => openConv R (ℓ₂ j) u v i)
        (funext fun t => hL₂ x j t) (funext fun t => hL₂ y j t)
    change H.eval (r.children x y) k = _
    rw [hH, hU, hV, selectCircuit_eval, selectCircuit_eval, hf, hg]
    rfl

end OpenConvolution

/-- The three denominator conditions imply an integer Bézout identity. -/
theorem threeDenominatorBezout {d₀ d₁ d₂ k : ℕ} (h₀ : Odd d₀) (hg : d₁.gcd d₂ = 2^k) :
    ∃ a b c : ℤ, a*d₀+b*d₁+c*d₂ = 1 := by
  let g := d₁.gcd d₂
  have hcop : Nat.Coprime d₀ g := by
    rw [show g = 2^k from hg]
    exact h₀.coprime_two_right.pow_right k
  have h₁ := Nat.gcd_eq_gcd_ab d₀ g
  have h₂ := Nat.gcd_eq_gcd_ab d₁ d₂
  rw [hcop.gcd_eq_one] at h₁
  refine ⟨d₀.gcdA g, d₀.gcdB g * d₁.gcdA d₂, d₀.gcdB g * d₁.gcdB d₂, ?_⟩
  change (g : ℤ) = _ at h₂
  rw [h₂] at h₁
  push_cast at h₁
  linear_combination -h₁

namespace OpenConvolution

/-- The open-descent Bézout step of Theorem 9.3. The child lengths on the
combined list are exactly those of the three input lists. -/
theorem threeListBezout {n : ℕ} {B₀ B₁ B₂ : Type*}
    {ℓ₀ : B₀ → ℕ} {ℓ₁ : B₁ → ℕ} {ℓ₂ : B₂ → ℕ}
    (p₀ : OpenConvolution ℤ n B₀ ℓ₀) (p₁ : OpenConvolution ℤ n B₁ ℓ₁)
    (p₂ : OpenConvolution ℤ n B₂ ℓ₂) {D₀ D₁ D₂ k : ℕ}
    (h₀ : p₀.RealizesMultiple D₀) (h₁ : p₁.RealizesMultiple D₁) (h₂ : p₂.RealizesMultiple D₂)
    (hodd : Odd D₀) (hgcd : D₁.gcd D₂ = 2^k) :
    ∃ p : OpenConvolution ℤ n (B₀ ⊕ (B₁ ⊕ B₂)) (Sum.elim ℓ₀ (Sum.elim ℓ₁ ℓ₂)),
      p.RealizesMultiple 1 ∧
      p.linearCost ≤ p₀.linearCost + p₁.linearCost + p₂.linearCost + 2*(2*n-1) := by
  obtain ⟨a, b, c, hbec⟩ := threeDenominatorBezout hodd hgcd
  obtain ⟨p₁₂, h₁₂, he₁₂⟩ := p₁.combine p₂ b c
  obtain ⟨p, hp, he⟩ := p₀.combine p₁₂ a 1
  refine ⟨p, fun x y i => ?_, by omega⟩
  rw [he, he₁₂, h₀, h₁, h₂, one_mul, one_mul]
  linear_combination (openConv ℤ n x y i) * hbec

end OpenConvolution

end FiniteFourier
end LinearAlgebra
end OAI
