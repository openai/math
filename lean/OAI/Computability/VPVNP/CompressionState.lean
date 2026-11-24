import OAI.Computability.VPVNP.DegreeRefreshActualStep
import OAI.Computability.VPVNP.PackingLanes
import OAI.Computability.VPVNP.Compression

/-!
# Degree and lane states of the compressor

A state retains the actual slots, their binary displacements and the width
of every individual wire. A substep specifies one such output per admitted
term of its local tensor identity. These types let Section 7.4 compose the
shrinking and degree-refresh identities even when the next topology depends
on all term choices made so far.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open NetworkKernel

/-- Degree exponent and available binary lane coordinates index a network. -/
structure State (a g : ℕ) where
  /-- Finite type of base vertices whose lifts by the lane bits give the sites of this
  compression state. -/
  Base : Type
  baseFintype : Fintype Base
  baseNonempty : Nonempty Base
  /-- Number the base vertices by consecutive finite ordinals for use in the descriptor tables. -/
  baseIndex : Base ≃ Fin (@Fintype.card Base baseFintype)
  /-- Directed slots and lane displacements describing the network lifted from the base
  vertices. -/
  slots : LiftedSlots Base (2 ^ a) (BitWord g)
  /-- Number of bits carried by an individual outgoing wire, indexed by base vertex, port, and
  lane. -/
  width : (Base × Fin (2 ^ a)) × BitWord g → ℕ

attribute [instance] State.baseFintype State.baseNonempty

variable {a b g n : ℕ}

namespace State

/-- The indexed order on a product base. The first component is the
old base address and the second is the promoted tag or port coordinate. -/
def productIndex {A B : Type*} [Fintype A] [Fintype B] {m n : ℕ}
    (e : A ≃ Fin m) (f : B ≃ Fin n) : A × B ≃ Fin (Fintype.card (A × B)) :=
  ((e.prodCongr f).trans finProdFinEquiv).trans (finCongr (by
    rw [Fintype.card_prod, Fintype.card_congr e, Fintype.card_congr f]
    simp))

/-- The wire tensor uses the finite binary word alphabet on each actual arc. -/
noncomputable def network (X : State a g) : Network := Refresh.actualWireGraph X.slots X.width

/-- Number of processor positions, including all lanes at each base vertex. -/
def positions (X : State a g) : ℕ := Fintype.card (X.Base × BitWord g)

theorem positions_pos (X : State a g) : 0 < X.positions := Fintype.card_pos

/-- Energy at the normalized mass of a single directed arc. -/
noncomputable def energy (X : State a g) : ℝ :=
  ∑ e, (X.width e : ℝ) ^ 2 / (1 / ((X.positions : ℝ) * (2 ^ a : ℕ)))

theorem energy_nonneg (X : State a g) : 0 ≤ X.energy := by unfold energy; positivity

/-- Sum of the widths of all shared fields. -/
def totalWidth (X : State a g) : ℕ := ∑ e, X.width e

theorem totalWidth_le_sqrt (X : State a g) : (X.totalWidth : ℝ) ≤ Real.sqrt X.energy := by
  let m := 1 / ((X.positions : ℝ) * (2 ^ a : ℕ))
  have hm : 0 < m := by dsimp [m]; positivity [X.positions_pos]
  have hsum : ∑ _e : (X.Base × Fin (2 ^ a)) × BitWord g, m = 1 := by
    have hc : Fintype.card ((X.Base × Fin (2 ^ a)) × BitWord g) = X.positions * 2 ^ a := by
      simp only [positions, Fintype.card_prod, Fintype.card_fin]
      ac_rfl
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, Nat.cast_mul]
    exact mul_one_div_cancel (mul_pos (Nat.cast_pos.mpr X.positions_pos)
      (Nat.cast_pos.mpr (Nat.two_pow_pos a))).ne'
  simpa only [totalWidth, Nat.cast_sum, energy] using
    widthSum_le_sqrtEnergy (fun e => (X.width e : ℝ)) (fun _ => m) (fun _ => hm) hsum

end State

/-- A local tensor identity whose output at each choice has the indicated
degree and lane count. -/
structure StatePass (R : Type*) [CommSemiring R] (X : State a g) (b n : ℕ) where
  /-- The network step expressing each input wire-tensor coefficient as the sum of the term
  values at the same half-wire assignment. -/
  step : Step R X.network
  /-- Output compression state for the network of each chosen term. -/
  next : step.Choice → State b n
  output_eq : ∀ i, (step.term i).output = (next i).network

/-- An exact computation with the same final degree and remaining lane
count for every sequence of admitted choices. -/
inductive StateExecution (R : Type*) [CommSemiring R] (b n : ℕ) :
    {a g : ℕ} → State a g → Type _
  | done (X : State b n) : StateExecution R b n X
  | more {a g a' g'} {X : State a g} (p : StatePass R X a' g')
      (tail : ∀ i, StateExecution R b n (p.next i)) : StateExecution R b n X

namespace StateExecution

variable {R : Type*} [CommSemiring R] {X : State a g}

/-- Only the motif choices are part of the path. The kernel contractions
sum over their hidden wire coordinates separately. -/
def Choices {a g : ℕ} {X : State a g} : StateExecution R b n X → Type
  | .done _ => Unit
  | .more p tail => (i : p.step.Choice) × (tail i).Choices

/-- Output topology and widths determined by the choices. -/
def finalState {a g : ℕ} {X : State a g} (P : StateExecution R b n X) : P.Choices → State b n :=
  match P with
  | .done X => fun _ => X
  | .more _ tail => fun z => (tail z.1).finalState z.2

/-- The coefficient identity is iterated over exactly these substeps. -/
noncomputable def history {a g : ℕ} {X : State a g} (P : StateExecution R b n X) :
    NetworkKernel.History R X.network :=
  match P with
  | .done _ => .stop
  | .more p tail => .branch p.step fun i => (p.output_eq i).symm ▸ (tail i).history

/-- Continue each admitted term independently. -/
def bind {b' n' a g : ℕ} {X : State a g} (P : StateExecution R b n X)
    (f : (z : P.Choices) → StateExecution R b' n' (P.finalState z)) :
    StateExecution R b' n' X :=
  match P with
  | .done _ => f ()
  | .more p tail => .more p fun i => (tail i).bind fun z => f ⟨i,z⟩

/-- Every final state of a continuation is reached by a path of the initial
execution followed by a path of the chosen continuation. -/
theorem forall_final_bind {b' n' : ℕ} (P : StateExecution R b n X)
    (f : (z : P.Choices) → StateExecution R b' n' (P.finalState z))
    (pred : State b' n' → Prop) (h : ∀ z y, pred ((f z).finalState y)) :
    ∀ y, pred ((P.bind f).finalState y) := by
  induction P with
  | done X => exact h ()
  | more p tail ih => exact fun y => ih y.1 (fun z => f ⟨y.1,z⟩) (fun z => h ⟨y.1,z⟩) y.2

end StateExecution
end Compression

end VPVNP
end Computability
end OAI
