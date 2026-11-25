import OAI.Computability.BorderVNP.ParseFanoutBounds
import OAI.Computability.BorderVNP.ParseBooleanRows
import Mathlib.Data.Fin.VecNotation

/-! # Ternary factors for a shared Boolean circuit and weighted guesses

Only the distinguished unary factors need non-Boolean entries. Two private
wires, checked against their names, provide the two Boolean constants.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch.BooleanLayout

open VPVNP (Ref)
open VPVNP.BooleanTranscript
open scoped Classical

variable {X W J : Type} {s : ℕ}

/-- Private guesses, intermediate Boolean gate values and two fixed Boolean constants. -/
abbrev Hidden (W : Type) (s : ℕ) := W ⊕ (Fin s ⊕ Bool)

/-- The gate constraints, constant checks, output acceptance and unary weight factors. -/
abbrev Tests (J : Type) (s : ℕ) := Fin s ⊕ (Bool ⊕ (Unit ⊕ J))

/-- Every Boolean gate test takes two operands and its output. All other tests are unary. -/
abbrev arity : Tests J s → ℕ := Sum.elim (fun _ => 3) (fun _ => 1)

private def wire {k : ℕ} (emb : Fin k → Fin s) : Ref Bool (X ⊕ W) k → X ⊕ Hidden W s
  | .var (.inl x) => .inl x
  | .var (.inr w) => .inr (.inl w)
  | .gate i => .inr (.inr (.inl (emb i)))
  | .const b => .inr (.inr (.inr b))

private def earlier (i : Fin s) (j : Fin i.val) : Fin s := ⟨j.val,j.isLt.trans i.isLt⟩

private def gateArgs (i : Fin s) (g : Gate (X ⊕ W) i.val) : Fin 3 → X ⊕ Hidden W s :=
  match g with
  | .and a b => ![wire (earlier i) a, wire (earlier i) b, .inr (.inr (.inl i))]
  | .not a => ![wire (earlier i) a, .inr (.inr (.inr false)), .inr (.inr (.inl i))]

/-- Assignment of each local argument to its original variable. -/
def args (c : Circuit (X ⊕ W) s) (weighted : J → W) :
    (t : Tests J s) → Fin (arity t) → X ⊕ Hidden W s
  | .inl i => gateArgs i (BooleanRows.row c.program i)
  | .inr (.inl b) => fun _ => .inr (.inr (.inr b))
  | .inr (.inr (.inl _)) => fun _ => wire id c.output
  | .inr (.inr (.inr j)) => fun _ => .inr (.inl (weighted j))

variable {R : Type*} [CommSemiring R]

private def gateOk {σ : Type} {k : ℕ} (g : Gate σ k) (z : Fin 3 → Bool) : Bool :=
  match g with
  | .and _ _ => (z 0 && z 1) == z 2
  | .not _ => (!z 0) == z 2

/-- The local tensor tables of the Boolean computation. -/
def factor (c : Circuit (X ⊕ W) s) (weight : J → Bool → R) :
    (t : Tests J s) → (Fin (arity t) → Bool) → R
  | .inl i => fun z => if gateOk (BooleanRows.row c.program i) z then 1 else 0
  | .inr (.inl b) => fun z => if z (0 : Fin 1) = b then 1 else 0
  | .inr (.inr (.inl _)) => fun z => if z (0 : Fin 1) then 1 else 0
  | .inr (.inr (.inr j)) => fun z => weight j (z (0 : Fin 1))

/-- A particular truth assignment before splitting variables across their occurrences. -/
def assignment (x : X → Bool) (w : W → Bool) (v : Fin s → Bool) (k : Bool → Bool) :
    X ⊕ Hidden W s → Bool := Sum.elim x (Sum.elim w (Sum.elim v k))

private theorem read_wire {k : ℕ} (emb : Fin k → Fin s) (r : Ref Bool (X ⊕ W) k)
    (x : X → Bool) (w : W → Bool) (v : Fin s → Bool) :
    assignment x w v id (wire emb r) = r.read id (Sum.elim x w) (v ∘ emb) := by
  cases r with
  | var a => cases a <;> rfl
  | gate i => rfl
  | const b => rfl

private theorem check_gate (i : Fin s) (g : Gate (X ⊕ W) i.val)
    (x : X → Bool) (w : W → Bool) (v : Fin s → Bool) :
    gateOk g (assignment x w v id ∘ gateArgs i g) =
      decide (g.eval (Sum.elim x w) (BooleanRows.before v i) = v i) := by
  cases g with
  | and a b =>
    change ((assignment x w v id (wire (earlier i) a) &&
      assignment x w v id (wire (earlier i) b)) == v i) = _
    rw [read_wire, read_wire]
    rfl
  | not a =>
    change ((!assignment x w v id (wire (earlier i) a)) == v i) = _
    rw [read_wire]
    rfl

/-- Multiplying all local factors enforces the Boolean transcript and its accepted output. -/
theorem factors_eq [Fintype J] (c : Circuit (X ⊕ W) s) (weighted : J → W) (weight : J → Bool → R)
    (x : X → Bool) (w : W → Bool) (v : Fin s → Bool) (k : Bool → Bool) :
    (∏ t, factor c weight t (assignment x w v k ∘ args c weighted t)) =
      if k = id then if v = c.program.run (Sum.elim x w) then
        (if c.eval (Sum.elim x w) then 1 else 0) * ∏ j, weight j (w (weighted j))
      else 0 else 0 := by
  classical
  let test (i : Fin s) := gateOk (BooleanRows.row c.program i)
    (assignment x w v k ∘ gateArgs i (BooleanRows.row c.program i))
  have expand :
      (∏ t, factor c weight t (assignment x w v k ∘ args c weighted t)) =
        (∏ i : Fin s, (if test i then 1 else 0 : R)) *
        ((∏ b : Bool, (if k b = b then 1 else 0 : R)) *
        ((if assignment x w v k (wire id c.output) then 1 else 0) *
          ∏ j, weight j (w (weighted j)))) := by
    simp only [test, Fintype.prod_sum_type, Fintype.prod_unique, factor, args,
      Function.comp_apply, assignment, Sum.elim_inl, Sum.elim_inr]
    rfl
  have constCheck : (∏ b : Bool, (if k b = b then 1 else 0 : R)) =
      if k = id then 1 else 0 := by
    rw [Fintype.prod_boole]
    congr 1
    exact propext ⟨fun h => funext h, fun h b => congrFun h b⟩
  rw [expand, constCheck]
  by_cases hk : k = id
  · subst k
    have good : (∀ i, test i = true) ↔ v = c.program.run (Sum.elim x w) := by
      simpa only [test, check_gate, decide_eq_true_eq] using
        (BooleanRows.rows_iff c.program (Sum.elim x w) v)
    simp only [Fintype.prod_boole, good]
    by_cases hv : v = c.program.run (Sum.elim x w)
    · subst v
      have out : assignment x w (c.program.run (Sum.elim x w)) id (wire id c.output) =
          c.eval (Sum.elim x w) := read_wire id c.output x w _
      simp [out]
    · simp [hv]
  · simp [hk]

end ParseBatch.BooleanLayout

end BorderVNP
end Computability
end OAI
