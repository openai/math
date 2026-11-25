import OAI.ThreeFlat.Routing.TypedWiring
import Mathlib.Tactic

namespace OAI
/-! # Composing tagged radix stages with their oracle pins exposed -/

noncomputable section
namespace Hierarchy.Tagged.RadixStage

open ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} {I M O H J : Type} [Fintype I] [Fintype M] [Fintype O]
  [Fintype H] [Fintype J]

abbrev Pins (I O H : Type) := (I ⊕ O) ⊕ H
abbrev Network (F : Type*) (I O H : Type) [Fintype I] [Fintype O] [Fintype H] :=
  BitNetwork F (Fintype.card (Pins I O H))

def row [CommSemiring F] (N : Network F I O H) (x : I→Bool) (y : O→Bool) (h : H→Bool) : F :=
  TypedWiring.value N (Sum.elim (Sum.elim x y) h)

def contract [CommSemiring F] (N : Network F I O H) (φ : (H→Bool)→F)
    (x : I→Bool) (y : O→Bool) : F := ∑ h, row N x y h * φ h

def pairWeight [Mul F] (φ : (H→Bool)→F) (ψ : (J→Bool)→F) (z : H⊕J→Bool) : F :=
  φ (z ∘ Sum.inl) * ψ (z ∘ Sum.inr)

private def side (I M O H J : Type) : Bool → Type
  | false => Pins I M H
  | true => Pins M O J

private instance sidesFinite (b : Bool) : Fintype (side I M O H J b) := by
  cases b
  · exact inferInstanceAs (Fintype (Pins I M H))
  · exact inferInstanceAs (Fintype (Pins M O J))

private def component (N : Network F I M H) (P : Network F M O J) :
    (b : Bool) → BitNetwork F (Fintype.card (side I M O H J b))
  | false => N
  | true => P

private def connect (I M O H J : Type) : (b : Bool) → side I M O H J b → Pins I O (H⊕J) ⊕ M
  | false, .inl (.inl i) => .inl (.inl (.inl i))
  | false, .inl (.inr m) => .inr m
  | false, .inr h => .inl (.inr (.inl h))
  | true, .inl (.inl m) => .inr m
  | true, .inl (.inr o) => .inl (.inl (.inr o))
  | true, .inr j => .inl (.inr (.inr j))

/-- Hide exactly the intermediate word array. Every oracle pin remains open. -/
def seq (N : Network F I M H) (P : Network F M O J) : Network F I O (H⊕J) :=
  TypedWiring.glue (component N P) (connect I M O H J)

theorem seq_row [CommSemiring F] (N : Network F I M H) (P : Network F M O J)
    (x : I→Bool) (z : O→Bool) (a : H→Bool) (b : J→Bool) :
    row (seq N P) x z (Sum.elim a b) = ∑ y, row N x y a * row P y z b := by
  unfold row seq
  rw [TypedWiring.glue_value]
  apply Finset.sum_congr rfl
  intro y _
  rw [Fintype.prod_bool]
  have left : (fun k : side I M O H J false =>
      Sum.elim (Sum.elim (Sum.elim x z) (Sum.elim a b)) y (connect I M O H J false k)) =
        Sum.elim (Sum.elim x y) a := by
    funext i
    rcases i with (i | i) | i <;> rfl
  have right : (fun k : side I M O H J true =>
      Sum.elim (Sum.elim (Sum.elim x z) (Sum.elim a b)) y (connect I M O H J true k)) =
        Sum.elim (Sum.elim y z) b := by
    funext i
    rcases i with (i | i) | i <;> rfl
  rw [left,right]
  simp only [component,mul_comm]; rfl

theorem seq_contract [CommSemiring F] (N : Network F I M H) (P : Network F M O J)
    (φ : (H→Bool)→F) (ψ : (J→Bool)→F) (x : I→Bool) (z : O→Bool) :
    contract (seq N P) (pairWeight φ ψ) x z =
      ∑ y, contract N φ x y * contract P ψ y z := by
  have split : contract (seq N P) (pairWeight φ ψ) x z =
      ∑ a,∑ b,row (seq N P) x z (Sum.elim a b)*(φ a*ψ b) := by
    unfold contract
    rw [← Fintype.sum_prod_type (f := fun ab : (H→Bool)×(J→Bool) =>
      row (seq N P) x z (Sum.elim ab.1 ab.2)*(φ ab.1*ψ ab.2))]
    trans ∑ h : H ⊕ J → Bool, row (seq N P) x z h * pairWeight φ ψ h
    · apply Finset.sum_congr (congrArg (@Finset.univ (H ⊕ J → Bool)) (Subsingleton.elim _ _))
      intro i _
      rfl
    · apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow H J Bool)
      intro h
      have eta : Sum.elim (h ∘ Sum.inl) (h ∘ Sum.inr) = h := by
        funext j
        cases j <;> rfl
      change _ = row (seq N P) x z (Sum.elim (h ∘ Sum.inl) (h ∘ Sum.inr)) * _
      rw [eta]
      rfl
  rw [split]
  unfold contract
  simp_rw [seq_row,Finset.sum_mul,Finset.mul_sum]
  calc
    (∑ a,∑ b,∑ y,row N x y a*row P y z b*(φ a*ψ b)) =
        ∑ a,∑ y,∑ b,row N x y a*row P y z b*(φ a*ψ b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

def Computes [CommSemiring F] (N : Network F I O H) (φ : (H→Bool)→F)
    (f : (I→Bool)→(O→Bool)) : Prop :=
  ∀ x y, contract N φ x y = if y=f x then 1 else 0

def ComputesOn [CommSemiring F] (N : Network F I O H) (φ : (H→Bool)→F)
    (G : (I→Bool)→Prop) (f : (I→Bool)→(O→Bool)) : Prop :=
  ∀ x,G x → ∀ y, contract N φ x y = if y=f x then 1 else 0

theorem ComputesOn.seq [CommSemiring F] {N : Network F I M H} {P : Network F M O J}
    {φ : (H→Bool)→F} {ψ : (J→Bool)→F} {G : (I→Bool)→Prop} {K : (M→Bool)→Prop}
    {f : (I→Bool)→(M→Bool)} {g : (M→Bool)→(O→Bool)}
    (hf : ComputesOn N φ G f) (hg : ComputesOn P ψ K g) (keep : ∀ x,G x→K (f x)) :
    ComputesOn (seq N P) (pairWeight φ ψ) G (g ∘ f) := by
  intro x hx y
  rw [seq_contract]
  simpa [hf x hx,ite_mul,Function.comp_def] using (hg (f x) (keep x hx) y)

theorem Computes.seq [CommSemiring F] {N : Network F I M H} {P : Network F M O J}
    {φ : (H→Bool)→F} {ψ : (J→Bool)→F} {f : (I→Bool)→(M→Bool)} {g : (M→Bool)→(O→Bool)}
    (hf : Computes N φ f) (hg : Computes P ψ g) :
    Computes (seq N P) (pairWeight φ ψ) (g ∘ f) := by
  intro x y
  rw [seq_contract]
  simpa [hf x,ite_mul,Function.comp_def] using (hg (f x) y)

@[simp] theorem seq_cells (N : Network F I M H) (P : Network F M O J) :
    (seq N P).cells = N.cells+P.cells := by
  simp [seq,component,add_comm]

@[simp] theorem seq_internal (N : Network F I M H) (P : Network F M O J) :
    (seq N P).internal = Fintype.card M + N.internal+P.internal := by
  simp [seq,component,add_comm,add_left_comm]

section Chain
variable (state holes : ℕ → Type) [∀ i,Fintype (state i)] [∀ i,Fintype (holes i)]

/-- All physical holes in passes numbered zero through n. -/
def Bank : ℕ → Type
  | 0 => holes 0
  | n+1 => Bank n ⊕ holes (n+1)

instance bankFinite : (n : ℕ) → Fintype (Bank holes n)
  | 0 => inferInstanceAs (Fintype (holes 0))
  | n+1 => by
    letI : Fintype (Bank holes n) := bankFinite n
    exact inferInstanceAs (Fintype (Bank holes n ⊕ holes (n+1)))

variable (N : (i : ℕ) → Network F (state i) (state (i+1)) (holes i))

def chain : (n : ℕ) → Network F (state 0) (state (n+1)) (Bank holes n)
  | 0 => N 0
  | n+1 => seq (chain n) (N (n+1))

def weights [Mul F] (φ : (i : ℕ) → (holes i → Bool) → F) :
    (n : ℕ) → (Bank holes n → Bool) → F
  | 0 => φ 0
  | n+1 => pairWeight (weights φ n) (φ (n+1))

def advance (run : (i : ℕ) → (state i → Bool) → (state (i+1) → Bool)) :
    (n : ℕ) → (state 0 → Bool) → (state (n+1) → Bool)
  | 0 => run 0
  | n+1 => run (n+1) ∘ advance run n

theorem chain_computesOn [CommSemiring F] (φ : (i : ℕ) → (holes i→Bool)→F)
    (run : (i : ℕ) → (state i → Bool) → (state (i+1) → Bool))
    (good : (i : ℕ) → (state i→Bool) → Prop) (n : ℕ)
    (ok : ∀ i, i≤n → ComputesOn (N i) (φ i) (good i) (run i))
    (keep : ∀ i, i≤n → ∀ x,good i x → good (i+1) (run i x)) :
    ComputesOn (chain state holes N n) (weights holes φ n) (good 0) (advance state run n) ∧
      ∀ x,good 0 x → good (n+1) (advance state run n x) := by
  induction n with
  | zero => exact ⟨ok 0 le_rfl,keep 0 le_rfl⟩
  | succ n ih =>
    obtain ⟨prior,well⟩ := ih (fun i hi => ok i (Nat.le_succ_of_le hi))
      (fun i hi => keep i (Nat.le_succ_of_le hi))
    exact ⟨prior.seq (ok (n+1) le_rfl) well,fun x hx => keep (n+1) le_rfl _ (well x hx)⟩

theorem chain_computes [CommSemiring F] (φ : (i : ℕ) → (holes i→Bool)→F)
    (run : (i : ℕ) → (state i → Bool) → (state (i+1) → Bool))
    (n : ℕ) (ok : ∀ i, i≤n → Computes (N i) (φ i) (run i)) :
    Computes (chain state holes N n) (weights holes φ n) (advance state run n) := by
  induction n with
  | zero => exact ok 0 le_rfl
  | succ n ih => exact (ih (fun i hi => ok i (Nat.le_succ_of_le hi))).seq (ok (n+1) le_rfl)

theorem chain_cells (n : ℕ) :
    (chain state holes N n).cells = ∑ i ∈ Finset.range (n+1),(N i).cells := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    change (seq (chain state holes N n) (N (n+1))).cells = _
    rw [seq_cells,ih]
    exact (Finset.sum_range_succ (fun i => (N i).cells) (n+1)).symm

theorem chain_internal (n : ℕ) :
    (chain state holes N n).internal = (∑ i ∈ Finset.range (n+1),(N i).internal) +
      ∑ i ∈ Finset.range n,Fintype.card (state (i+1)) := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    change (seq (chain state holes N n) (N (n+1))).internal = _
    rw [seq_internal,ih,Finset.sum_range_succ (fun i => (N i).internal) (n+1),
      Finset.sum_range_succ (fun i => Fintype.card (state (i+1))) n]
    omega

end Chain

end Hierarchy.Tagged.RadixStage

end
end OAI
