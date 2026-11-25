import OAI.LinearAlgebra.SpectralBooks.SpectralPlacementPrices.ShortenPrice

/-! # The four-terminal tensor and its two opposite cuts -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

namespace ShiftedCrossing

open SiteTensor

local instance (priority := 4000) {α : Type*} : DecidableEq α := Classical.decEq α

abbrev Site := Fin 2 ⊕ Fin 2

/-- Each wire carries its own dimension at both ends. -/
def Leg (dX dY : ℕ) : Site → Type := Sum.elim (fun _ ↦ Fin dX) (fun _ ↦ Fin dY)

instance (dX dY : ℕ) : ∀ i, Fintype (Leg dX dY i)
  | .inl _ => inferInstanceAs (Fintype (Fin dX))
  | .inr _ => inferInstanceAs (Fintype (Fin dY))

variable {K : Type*} [Field K] {dX dY r : ℕ}

def target (K : Type*) [Field K] (dX dY : ℕ) : Raw Site K :=
  ⟨Leg dX dY, inferInstance, fun a =>
    if a (.inl 0) = a (.inl 1) ∧ a (.inr 0) = a (.inr 1) then 1 else 0⟩

/-- On the minus cut the second pair of terminals is exchanged. -/
def partner : Bool → Fin 2 → Fin 2
  | false => id
  | true => Fin.rev

@[simp] theorem partner_partner (b : Bool) (i : Fin 2) : partner b (partner b i) = i := by
  cases b <;> simp [partner]

def cut (b : Bool) : Site → Fin 2 := Sum.elim id (partner b)

def term (b : Bool) (W : Fin 2 → Fin dX → Fin dY → Fin r → K) : Raw Site K :=
  ⟨Leg dX dY, inferInstance, fun a =>
    ∑ k, ∏ j, W j (a (.inl j)) (a (.inr (partner b j))) k⟩

/-- At the two centers, the matrices of the stated factorization are precisely the
two local maps from the diagonal on the shared index. -/
theorem term_group_restricts (b : Bool) (W : Fin 2 → Fin dX → Fin dY → Fin r → K) :
    ((term b W).group (cut b)).Restricts (Raw.diagonal (Fin 2) K (Fin r)) := by
  let M (j : Fin 2) (z : ((term b W).group (cut b)).Leg j) (k : Fin r) :=
    W j (z ⟨.inl j, rfl⟩) (z ⟨.inr (partner b j), partner_partner b j⟩) k
  refine ⟨M, fun x => ?_⟩
  change _ = ∑ a : Fin 2 → Fin r, (∑ k, if a = fun _ => k then (1 : K) else 0) *
    ∏ j, M j (x j) (a j)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  dsimp only [Raw.group, term]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.prod_congr rfl
  intro j _
  dsimp only [M]
  cases b <;> fin_cases j <;> rfl

/-- Ordinary sum decomposition into two factorizations on their respective cuts. -/
structure Factorization (K : Type*) [Field K] (dX dY rp rm : ℕ) where
  plus : Fin 2 → Fin dX → Fin dY → Fin rp → K
  minus : Fin 2 → Fin dX → Fin dY → Fin rm → K
  identity : ∀ x : ∀ i, Leg dX dY i, (target K dX dY).coeff x =
    (term false plus).coeff x + (term true minus).coeff x

theorem target_ne_zero (hx : 0 < dX) (hy : 0 < dY) : (target K dX dY).coeff ≠ 0 := by
  let a : ∀ j, Leg dX dY j
    | .inl _ => ⟨0,hx⟩
    | .inr _ => ⟨0,hy⟩
  intro h
  have hh := congrFun h a
  change (if _ then (1 : K) else 0) = 0 at hh
  rw [ite_eq_left ⟨rfl, rfl⟩] at hh
  exact one_ne_zero hh

/-- The integral matrix identity yields exactly the two fixed-format tensors over each field. -/
def Factorization.ofInt {rp rm : ℕ}
    (Lp Rp : Fin dX → Fin dY → Fin rp → ℤ) (Lm Rm : Fin dX → Fin dY → Fin rm → ℤ)
    (h : ∀ i j a b, (if i = j ∧ a = b then (1 : ℤ) else 0) =
      (∑ k, Lp i a k * Rp j b k) + ∑ k, Lm i b k * Rm j a k) :
    Factorization K dX dY rp rm where
  plus j i a k := (![Lp,Rp] j i a k : ℤ)
  minus j i a k := (![Lm,Rm] j i a k : ℤ)
  identity := by
    intro x
    let i : Fin dX := x (.inl 0)
    let j : Fin dX := x (.inl 1)
    let a : Fin dY := x (.inr 0)
    let b : Fin dY := x (.inr 1)
    have p := h i j a b
    change (if i = j ∧ a = b then (1 : K) else 0) =
      (∑ k, ∏ s, ((![Lp,Rp] s (x (.inl s)) (x (.inr (partner false s))) k : ℤ) : K)) +
        ∑ k, ∏ s, ((![Lm,Rm] s (x (.inl s)) (x (.inr (partner true s))) k : ℤ) : K)
    simp only [Fin.prod_univ_two]
    change (if i = j ∧ a = b then (1 : K) else 0) =
      (∑ k, (Lp i a k : K) * (Rp j b k : K)) + ∑ k, (Lm i b k : K) * (Rm j a k : K)
    split_ifs at p ⊢ with he
    · simpa using congrArg (Int.castRingHom K) p
    · simpa using congrArg (Int.castRingHom K) p

end ShiftedCrossing

end

end SpectralBooks
end LinearAlgebra
end OAI
