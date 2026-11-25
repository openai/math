import OAI.ThreeFlat.Routing.SpillLinks

namespace OAI
/-! # Data movement controlled by a deterministic matching

A selector checker reads the active mask and reported incident edges. The
selected edges become shared internal wires of the word compactor.
-/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.Spill

variable {L R F : Type*} [Fintype L] [Fintype R] [DecidableEq R]

abbrev BankPin (L R : Type*) (u : ℕ) := L ⊕ ((L × Fin u) ⊕ (R × Option (Fin u)))
private def bankPort (N : L → Finset R) (u : ℕ) : Bool → Type _
  | false => L ⊕ Candidate N
  | true => LinkPin N u

private instance (N : L → Finset R) (u : ℕ) (g : Bool) : Fintype (bankPort N u g) := by
  cases g <;> dsimp [bankPort] <;> infer_instance

private def bankWire (N : L → Finset R) (u : ℕ) :
    ∀ g : Bool, bankPort N u g → BankPin L R u ⊕ Candidate N
  | false, .inl x => .inl (.inl x)
  | false, .inr c => .inr c
  | true, .inl c => .inr c
  | true, .inr z => .inl (.inr z)

private def bankModules [Zero F] [One F] (N : L → Finset R) (u : ℕ)
    (check : BitNetwork F (Fintype.card (L ⊕ Candidate N))) :
    (g : Bool) → BitNetwork F (Fintype.card (bankPort N u g))
  | false => check
  | true => linkNetwork N u

/-- Connect each reported bit both to the planner and to its public data wires. -/
def packingNetwork [Zero F] [One F] (N : L → Finset R) (u : ℕ)
    (check : BitNetwork F (Fintype.card (L ⊕ Candidate N))) : BitNetwork F (Fintype.card (BankPin L R u)) :=
  TypedWiring.glue (bankModules N u check) (bankWire N u)

def bankPins {u : ℕ} (mask : L → Bool) (input : L → Fin u → Bool)
    (out : R → Option (Fin u) → Bool) : BankPin L R u → Bool :=
  Sum.elim mask (Sum.elim (Function.uncurry input) (Function.uncurry out))

theorem packingNetwork_cells [Zero F] [One F] (N : L → Finset R) (u : ℕ)
    (check : BitNetwork F (Fintype.card (L ⊕ Candidate N))) :
    (packingNetwork N u check).cells = check.cells + (linkNetwork (F := F) N u).cells := by
  simp [packingNetwork,bankModules,Nat.add_comm]

/-- If the selector has chosen its unique reporting bits, summing those bits
enforces the transported output word exactly. -/
theorem packingNetwork_eval [CommSemiring F] (N : L → Finset R) (u : ℕ)
    (check : BitNetwork F (Fintype.card (L ⊕ Candidate N))) (mask : L → Bool)
    (pick : Candidate N → Bool) (input : L → Fin u → Bool) (out : R → Option (Fin u) → Bool)
    (hcheck : ∀ c, TypedWiring.value check (Sum.elim mask c) = if c = pick then 1 else 0) :
    TypedWiring.value (packingNetwork N u check) (bankPins mask input out) =
      if out = packed pick input then 1 else 0 := by
  rw [packingNetwork,TypedWiring.glue_value]
  have val (c : Candidate N → Bool) :
      (∏ g : Bool, TypedWiring.value (bankModules N u check g)
        (fun k => Sum.elim (bankPins mask input out) c (bankWire N u g k))) =
      (if c = pick then 1 else 0) * (if out = packed c input then 1 else 0) := by
    rw [Fintype.prod_bool]
    have p : (fun k => Sum.elim (bankPins mask input out) c (bankWire N u false k)) =
        Sum.elim mask c := by funext k; cases k <;> rfl
    have l : (fun k => Sum.elim (bankPins mask input out) c (bankWire N u true k)) =
        linkPins c input out := by funext k; cases k <;> rfl
    rw [p,l]
    exact (congrArg₂ (· * ·) (linkNetwork_eval (F := F) N u c input out) (hcheck c)).trans
      (mul_comm _ _)
  simp_rw [val]
  rw [Finset.sum_eq_single pick]
  · simp
  · intro c _ hc
    rw [ite_eq_right hc,zero_mul]
  · simp

theorem packingNetwork_reject [CommSemiring F] (N : L → Finset R) (u : ℕ)
    (check : BitNetwork F (Fintype.card (L ⊕ Candidate N))) (mask : L → Bool)
    (input : L → Fin u → Bool) (out : R → Option (Fin u) → Bool)
    (hcheck : ∀ c, TypedWiring.value check (Sum.elim mask c) = 0) :
    TypedWiring.value (packingNetwork N u check) (bankPins mask input out) = 0 := by
  rw [packingNetwork,TypedWiring.glue_value]
  apply Finset.sum_eq_zero
  intro c _
  apply Finset.prod_eq_zero (Finset.mem_univ false)
  change TypedWiring.value check _ = 0
  have p : (fun k => Sum.elim (bankPins mask input out) c (bankWire N u false k)) =
      Sum.elim mask c := by funext k; cases k <;> rfl
  exact (congrArg (TypedWiring.value check) p).trans (hcheck c)

end ThreeFlat.Routing.Spill

end
end OAI
