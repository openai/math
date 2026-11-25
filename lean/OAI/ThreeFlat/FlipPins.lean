import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # Fixed Boolean offsets at the external pins

Each table row absorbs the offset of each pin it reads. The same offset is
applied at every occurrence of that pin, including repeated reads by one cell.
-/

namespace ThreeFlat

variable {F : Type*} {p : ℕ}

private def pinOffset {n : ℕ} (mask : Fin p → Bool) : BitSource n p → Bool
  | .pin i => mask i
  | .hidden _ | .constant _ => false

private theorem read_xor_pinOffset {n : ℕ} (mask pin : Fin p → Bool) (hidden : Fin n → Bool)
    (s : BitSource n p) :
    (s.read hidden pin).xor (pinOffset mask s) = s.read hidden (fun i => (pin i).xor (mask i)) := by
  cases s <;> simp [BitSource.read, pinOffset]

namespace BitNetwork

/-- Reindex each cell table by the fixed offsets of its external inputs. -/
def flipPins (N : BitNetwork F p) (mask : Fin p → Bool) : BitNetwork F p :=
  { N with table := fun i b => N.table i fun j => (b j).xor (pinOffset mask (N.source i j)) }

@[simp] theorem flipPins_cells (N : BitNetwork F p) (mask : Fin p → Bool) :
    (N.flipPins mask).cells = N.cells := rfl

@[simp] theorem flipPins_internal (N : BitNetwork F p) (mask : Fin p → Bool) :
    (N.flipPins mask).internal = N.internal := rfl

@[simp] theorem factor_flipPins (N : BitNetwork F p) (mask pin : Fin p → Bool)
    (hidden : Fin N.internal → Bool) (i : Fin N.cells) :
    (N.flipPins mask).factor pin hidden i = N.factor (fun j => (pin j).xor (mask j)) hidden i := by
  simp only [factor, flipPins, read_xor_pinOffset]

theorem eval_flipPins [CommSemiring F] (N : BitNetwork F p) (mask pin : Fin p → Bool) :
    (N.flipPins mask).eval pin = N.eval (fun j => (pin j).xor (mask j)) := by
  unfold eval weight
  apply Finset.sum_congr rfl
  intro h _
  exact Finset.prod_congr rfl fun i _ => factor_flipPins N mask pin h i

end BitNetwork

namespace Routing.TypedWiring

variable {P : Type*} [Fintype P]

/-- Apply a fixed Boolean offset to the externally labelled pins. -/
noncomputable def flipPins (N : BitNetwork F (Fintype.card P)) (mask : P → Bool) :
    BitNetwork F (Fintype.card P) :=
  N.flipPins fun i => mask ((Fintype.equivFin P).symm i)

@[simp] theorem flipPins_cells (N : BitNetwork F (Fintype.card P)) (mask : P → Bool) :
    (flipPins N mask).cells = N.cells := rfl

@[simp] theorem flipPins_internal (N : BitNetwork F (Fintype.card P)) (mask : P → Bool) :
    (flipPins N mask).internal = N.internal := rfl

theorem value_flipPins [CommSemiring F] (N : BitNetwork F (Fintype.card P)) (mask x : P → Bool) :
    value (flipPins N mask) x = value N (fun p => (x p).xor (mask p)) :=
  BitNetwork.eval_flipPins ..

end Routing.TypedWiring
end ThreeFlat

end OAI
