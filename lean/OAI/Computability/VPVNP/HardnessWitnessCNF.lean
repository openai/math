import OAI.Computability.VPVNP.HardnessCNF
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum

/-! # Copying selection flags and testing witness bits

The augmented formula contains the original selection flags, a second copy of
each flag and one bit per witness variable. Each selected event labelled by a
witness variable forces the corresponding witness bit to be true.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessWitness

open HardnessCNF

/-- The augmented formula has the original `k` flags, their `k` copies, and one Boolean
variable for each witness coordinate. -/
def width (k : ℕ) (W : Type*) [Fintype W] := k + (k + Fintype.card W)

/-- The three disjoint blocks of Boolean slots. -/
noncomputable def slots (k : ℕ) (W : Type*) [Fintype W] :
    (Fin k ⊕ (Fin k ⊕ W)) ≃ Fin (width k W) :=
  Fintype.equivFinOfCardEq (by simp [width])

variable {k : ℕ} {X W : Type*} [Fintype W]

private def relabel {k m : ℕ} (f : Fin k → Fin m) (φ : CNF k) : CNF m :=
  φ.map fun c => c.map fun p => (f p.1, p.2)

private noncomputable def flagClauses (i : Fin k) (tag : Option (X ⊕ W)) : CNF (width k W) :=
  let a := slots k W (.inl i)
  let b := slots k W (.inr (.inl i))
  [[(a, false), (b, true)], [(b, false), (a, true)]] ++
    match tag with
    | some (.inr w) => [[(a, false), (slots k W (.inr (.inr w)), true)]]
    | _ => []

/-- Lift all original clauses, constrain the copied flags, and add witness implications. -/
noncomputable def augment (φ : CNF k) (tag : Fin k → Option (X ⊕ W)) : CNF (width k W) :=
  relabel (fun i => slots k W (.inl i)) φ ++
    (List.finRange k).flatMap (fun i => flagClauses i (tag i))

/-- Each selected flag with a witness label has a true bit for its label. -/
def Compatible (tag : Fin k → Option (X ⊕ W)) (x : Fin k → Bool) (y : W → Bool) : Prop :=
  ∀ i w, x i = true → tag i = some (.inr w) → y w = true

private theorem satisfies_relabel {k m : ℕ} (f : Fin k → Fin m) (φ : CNF k) (z : Fin m → Bool) :
    Satisfies (relabel f φ) z ↔ Satisfies φ (fun i => z (f i)) := by
  simp [Satisfies, relabel]

private theorem satisfies_flagClauses (i : Fin k) (tag : Option (X ⊕ W))
    (z : Fin (width k W) → Bool) : Satisfies (flagClauses i tag) z ↔
    z (slots k W (.inr (.inl i))) = z (slots k W (.inl i)) ∧
      (∀ w, z (slots k W (.inl i)) = true → tag = some (.inr w) →
        z (slots k W (.inr (.inr w))) = true) := by
  rcases tag with _ | v | w <;>
    cases hx : z (slots k W (.inl i)) <;> cases hb : z (slots k W (.inr (.inl i))) <;>
      simp only [flagClauses, List.cons_append, List.nil_append, Satisfies, List.forall_mem_cons] <;>
      simp [hx, hb]

/-- Satisfiability of the augmented formula separates into the original clauses,
equality of every copy with its flag, and the witness implications. -/
theorem satisfies_augment (φ : CNF k) (tag : Fin k → Option (X ⊕ W))
    (z : Fin (width k W) → Bool) :
    Satisfies (augment φ tag) z ↔
      Satisfies φ (fun i => z (slots k W (.inl i))) ∧
      (∀ i, z (slots k W (.inr (.inl i))) = z (slots k W (.inl i))) ∧
      Compatible tag (fun i => z (slots k W (.inl i))) (fun w => z (slots k W (.inr (.inr w)))) := by
  have split : Satisfies (augment φ tag) z ↔
      Satisfies (relabel (fun i => slots k W (.inl i)) φ) z ∧
        ∀ i, Satisfies (flagClauses i (tag i)) z := by
    simp only [augment, Satisfies, List.mem_append, List.mem_flatMap, List.mem_finRange,
      true_and]
    aesop
  rw [split, satisfies_relabel]
  simp only [satisfies_flagClauses, forall_and, Compatible]

private theorem literalCount_relabel {m : ℕ} (f : Fin k → Fin m) (φ : CNF k) :
    literalCount (relabel f φ) = literalCount φ := by
  simp [relabel, literalCount, List.map_map, Function.comp_def]

private theorem literalCount_flagClauses_le (i : Fin k) (t : Option (X ⊕ W)) :
    literalCount (flagClauses i t) ≤ 6 := by
  cases t with
  | none => simp [flagClauses, literalCount]
  | some e => cases e <;> simp [flagClauses, literalCount]

private theorem literalCount_flags_le (is : List (Fin k)) (tag : Fin k → Option (X ⊕ W)) :
    literalCount (is.flatMap (fun i => flagClauses i (tag i))) ≤ 6 * is.length := by
  induction is with
  | nil => simp [literalCount]
  | cons i is ih =>
    have h := Nat.add_le_add (literalCount_flagClauses_le i (tag i)) ih
    simpa [literalCount, Nat.mul_succ, Nat.add_comm] using h

/-- Each original flag contributes at most six literals to the augmented CNF. -/
theorem literalCount_augment_le (φ : CNF k) (tag : Fin k → Option (X ⊕ W)) :
    literalCount (augment φ tag) ≤ literalCount φ + 6 * k := by
  have hadd (a b : CNF (width k W)) : literalCount (a ++ b) = literalCount a + literalCount b := by
    simp [literalCount]
  rw [augment, hadd, literalCount_relabel]
  exact Nat.add_le_add_left (by simpa using literalCount_flags_le (List.finRange k) tag) _

end HardnessWitness

end VPVNP
end Computability
end OAI
