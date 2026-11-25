import OAI.Computability.BorderVNP.CrossingNetwork
import OAI.Computability.BorderVNP.CrossingSelectorProfile

/-!
# The fixed profile network

A selector cable runs from the origin to every terminal. Each terminal
sends the selected external blocks to the banks on zero-length cables.
The remaining cables are copies of the term cables, scaled by the term's
histogram entry. Sites, edge endpoints and positions are independent of
the word length and histogram.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Profile

variable {A D j : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}

/-- Split a concatenation of equally long bit strings into its consecutive blocks. -/
def blocks {b n : ℕ} : (Fin (n * b) → Bool) ≃ (Fin n → Fin b → Bool) where
  toFun x i q := x (finProdFinEquiv (i, q))
  invFun y k := y (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv x := by funext k; exact congrArg x (finProdFinEquiv.apply_symm_apply k)
  right_inv y := by funext i q; simp

/-- Unpack a whole word of binary selectors into `j` fixed-width codes. -/
def spokeBlocks {b n : ℕ} : (Fin (n * b) → Bool) ≃ (Fin n → Fin b → Fin 2) where
  toFun x i q := finTwoEquiv.symm (blocks x i q)
  invFun y := blocks.symm (fun i q => finTwoEquiv (y i q))
  left_inv x := by simp
  right_inv y := by simp

/-- External input for the `i`-th copy. -/
def externalBlock (x : Ports (fun p => j * bits p)) (i : Fin j) : Ports bits :=
  fun u => blocks (x u) i

variable (N : Fin A → Network D P bits)
variable (place : P → EuclideanSpace ℝ (Fin D)) (hball : ∀ u, ‖place u‖ ≤ 1)

/-- Physical layout of the histogram network. Only cable widths and the
external bundle size depend on the number of copies and histogram. -/
def network (j : ℕ) (p : Fin A → ℕ) : Network D P (fun u => j * bits u) where
  Site := Unit ⊕ P ⊕ (Σ a, (N a).Site)
  Edge := P ⊕ ((Fin A × P) ⊕ (Σ a, (N a).Edge))
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src
    | .inl _ => .inl ()
    | .inr (.inl (_, u)) => .inr (.inl u)
    | .inr (.inr ⟨a, e⟩) => .inr (.inr ⟨a, (N a).src e⟩)
  dst
    | .inl u => .inr (.inl u)
    | .inr (.inl (a, u)) => .inr (.inr ⟨a, (N a).attach u⟩)
    | .inr (.inr ⟨a, e⟩) => .inr (.inr ⟨a, (N a).dst e⟩)
  width
    | .inl _ => j * Nat.clog 2 A
    | .inr (.inl (a, u)) => p a * bits u
    | .inr (.inr ⟨a, e⟩) => p a * (N a).width e
  attach u := .inr (.inl u)
  position
    | .inl () => 0
    | .inr (.inl u) => place u
    | .inr (.inr ⟨a, v⟩) => (N a).position v
  in_ball
    | .inl () => by simp
    | .inr (.inl u) => hball u
    | .inr (.inr ⟨a, v⟩) => (N a).in_ball v

/-- All external ports occupy their prescribed locations. -/
theorem network_placedAt (j : ℕ) (p : Fin A → ℕ) :
    (network N place hball j p).PlacedAt place := fun _ => rfl

/-- Exact cost of the physical profile network, including the selector
spokes. The feeder cables have zero length. -/
theorem network_cost (hp : ∀ a, (N a).PlacedAt place) (j : ℕ) (p : Fin A → ℕ) :
    (network N place hball j p).cost =
      (j * Nat.clog 2 A : ℝ) * (∑ u, ‖place u‖) + ∑ a, (p a : ℝ) * (N a).cost := by
  classical
  have hplace (a : Fin A) (u : P) : (N a).position ((N a).attach u) = place u := hp a u
  unfold Network.cost
  dsimp (config := { instances := true }) only [network]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_prod_type]
  dsimp only
  simp [hplace, Nat.cast_mul, ← Finset.mul_sum, mul_assoc]

/-- Cost bound using the paper's per-term cap and the unit-ball placement
of the terminals. -/
theorem network_cost_le (hp : ∀ a, (N a).PlacedAt place) (j : ℕ) (p : Fin A → ℕ)
    (htotal : ∑ a, p a = j) (c : ℝ) (hc : ∀ a, (N a).cost ≤ c) :
    (network N place hball j p).cost ≤ j * (c + Fintype.card P * Nat.clog 2 A) := by
  rw [network_cost N place hball hp]
  have hnorm : ∑ u, ‖place u‖ ≤ (Fintype.card P : ℝ) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun u _ => hball u)
  have hbank : ∑ a, (p a : ℝ) * (N a).cost ≤ (j : ℝ) * c := by
    calc
      _ ≤ ∑ a, (p a : ℝ) * c := by gcongr with a; exact hc a
      _ = _ := by rw [← Finset.sum_mul, ← Nat.cast_sum, htotal]
  have hsel := mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ (j : ℝ) * Nat.clog 2 A)
  linarith only [hsel, hbank]

/-- Classify every assignment of the layout into selector spokes, feeders
at the terminals, and copies of the original internal cable assignments. -/
def assignmentEquiv (j : ℕ) (p : Fin A → ℕ) :
    (network N place hball j p).Assignment ≃
      ((P → Fin j → Fin (Nat.clog 2 A) → Fin 2) ×
        (∀ a, Fin (p a) → Ports bits) × (∀ a, Fin (p a) → (N a).Assignment)) where
  toFun y := (fun u => spokeBlocks (y (.inl u)),
    (fun a i u => blocks (y (.inr (.inl (a, u)))) i,
     fun a i e => blocks (y (.inr (.inr ⟨a, e⟩))) i))
  invFun z
    | .inl u => spokeBlocks.symm (z.1 u)
    | .inr (.inl (a, u)) => blocks.symm (fun i => z.2.1 a i u)
    | .inr (.inr ⟨a, e⟩) => blocks.symm (fun i => z.2.2 a i e)
  left_inv y := by
    funext e
    rcases e with u | ⟨a, u⟩ | ⟨a, e⟩
    · exact spokeBlocks.symm_apply_apply _
    · exact blocks.symm_apply_apply _
    · exact blocks.symm_apply_apply _
  right_inv := by
    rintro ⟨s, f, z⟩
    simp

end Crossing.Profile

end BorderVNP
end Computability
end OAI
