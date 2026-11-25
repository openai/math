import OAI.ThreeFlat.Routing.TypedWiring
import Mathlib.Tactic

namespace OAI
/-! # Deterministic word scans for radix checks

For a fixed finite-state scan, composing its truth tables costs linearly many
trivalent gates. Its hidden state bits have one consistent assignment. A scan
may use different transitions at each bit, for example on the two sides of a
pack boundary.
-/

namespace Hierarchy.Tagged.Scan

open ThreeFlat
open Routing Routing.TypedWiring
open scoped BigOperators Classical

noncomputable section

abbrev Bits (b : ℕ) := Fin b → Bool
abbrev Ports (n t : ℕ) := Fin n × Fin t
abbrev States (n b : ℕ) := Fin (n+1) × Fin b
abbrev Local (b t : ℕ) := Fin b ⊕ (Fin b ⊕ Fin t)
abbrev Gate (n : ℕ) := Bool ⊕ Fin n

def run {n b t : ℕ} (init : Bits b) (next : Fin n → Bits b → Bits t → Bits b)
    (x : Ports n t → Bool) : Fin (n+1) → Bits b :=
  Fin.induction init fun i s => next i s (fun j => x (i,j))

def check {n b t : ℕ} (init : Bits b) (next : Fin n → Bits b → Bits t → Bits b)
    (accept : Bits b → Prop) (g : Gate n) (v : Local b t → Bool) : Prop :=
  match g with
  | .inl false => (fun j => v (.inl j)) = init
  | .inl true => accept (fun j => v (.inl j))
  | .inr i => (fun j => v (.inr (.inl j))) = next i (fun j => v (.inl j))
      (fun j => v (.inr (.inr j)))

def wires {n b t : ℕ} [NeZero b] (g : Gate n) : Local b t → Ports n t ⊕ States n b :=
  match g with
  | .inl last => fun p => .inr (if last then Fin.last n else 0, p.elim id (Sum.elim id (fun _ => 0)))
  | .inr i => Sum.elim (fun j => .inr (i.castSucc,j))
      (Sum.elim (fun j => .inr (i.succ,j)) (fun j => .inl (i,j)))

def network (F : Type*) [Zero F] [One F] {n b t : ℕ} [NeZero b]
    (init : Bits b) (next : Fin n → Bits b → Bits t → Bits b) (accept : Bits b → Prop) :
    BitNetwork F (Fintype.card (Ports n t)) :=
  glue (fun g : Gate n => localTable (fun v => if check init next accept g v then (1:F) else 0)) wires

private theorem consistent {n b t : ℕ} [NeZero b] (init : Bits b)
    (next : Fin n → Bits b → Bits t → Bits b) (accept : Bits b → Prop)
    (x : Ports n t → Bool) (h : States n b → Bool) :
    (∀ g, check init next accept g (fun k => Sum.elim x h (wires g k))) ↔
      h = Function.uncurry (run init next x) ∧ accept (run init next x (Fin.last n)) := by
  constructor
  · intro good
    have zero : (fun j => h (0,j)) = init := good (.inl false)
    have step (i : Fin n) : (fun j => h (i.succ,j)) = next i (fun j => h (i.castSucc,j))
        (fun j => x (i,j)) := good (.inr i)
    have unique (i : Fin (n+1)) : (fun j => h (i,j)) = run init next x i := by
      induction i using Fin.induction with
      | zero => simpa [run] using zero
      | succ i ih => rw [step, ih]; simp [run]
    refine ⟨funext fun (i,j) => congrFun (unique i) j, ?_⟩
    rw [← unique]
    exact good (.inl true)
  · rintro ⟨rfl, ok⟩ (flag | i)
    · cases flag
      · simp [check, wires, run, Function.uncurry]
      · simpa [check, wires, Function.uncurry] using ok
    · simp [check, wires, run, Function.uncurry]

theorem eval (F : Type*) [CommSemiring F] {n b t : ℕ} [NeZero b]
    (init : Bits b) (next : Fin n → Bits b → Bits t → Bits b) (accept : Bits b → Prop)
    (x : Ports n t → Bool) :
    value (network F init next accept) x = if accept (run init next x (Fin.last n)) then 1 else 0 := by
  simp only [network, glue_value, localTable_value, Fintype.prod_boole, consistent]
  by_cases h : accept (run init next x (Fin.last n)) <;> simp [h]

theorem size (F : Type*) [Zero F] [One F] {n b t : ℕ} [NeZero b]
    (init : Bits b) (next : Fin n → Bits b → Bits t → Bits b) (accept : Bits b → Prop) :
    let W := network F init next accept
    let ar := b+(b+t)
    W.cells + W.internal = (n+1)*b+(n+2)*2^ar*(2*ar+3) := by
  dsimp only
  simp [network, localTable, TableCompiler.localTableNetwork_cells,
    TableCompiler.localTableNetwork_internal, Local, Gate, States]
 ; ring

end
end Hierarchy.Tagged.Scan

end OAI
