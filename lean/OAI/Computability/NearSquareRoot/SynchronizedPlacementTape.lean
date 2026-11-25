import OAI.Computability.NearSquareRoot.SynchronizedPlacementAddress
import OAI.Computability.NearSquareRoot.PhaseProgramRelease
import OAI.Computability.IntegerMultiplication.Staff.Nat

/-! # Tape evaluation of borrowing-batch addresses -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedBorrowing
open IntegerMultiplication Code Strip Staff

variable {J : Type} {s : Regime J} {start v a r i flat phys : J → ℕ}

private theorem min_realizes {f g : J → ℕ} (F : Realizes s f) (G : Realizes s g) :
    Realizes s (fun j => min (f j) (g j)) := by
  have h : (fun j => min (f j) (g j)) = (fun j => if f j < g j then f j else g j) := by
    funext j
    split_ifs with h
    · exact min_eq_left h.le
    · exact min_eq_right (Nat.le_of_not_gt h)
  rw [h]
  exact F.select G (F.below G)

theorem first_realizes {b : J → ℕ} {batch : J → Fin 15}
    (B : Realizes s b) (T : Realizes s (fun j => (batch j).val)) :
    Realizes s (fun j => first (b j) (batch j)) :=
  min_realizes B (T.times (B.dividing (.fix 8)))

theorem size_realizes {b : J → ℕ} {batch : J → Fin 15}
    (B : Realizes s b) (T : Realizes s (fun j => (batch j).val)) :
    Realizes s (fun j => size (b j) (batch j)) :=
  min_realizes (B.dividing (.fix 8)) (B.minused (first_realizes B T))

/-- Compute the global row-major rank of a local cell from unary parameters. -/
theorem physicalRank_realizes (S : Realizes s start) (V : Realizes s v)
    (A : Realizes s a) (R : Realizes s r) (I : Realizes s i) (F : Realizes s flat) :
    Realizes s (fun j => physicalRank (start j) (v j) (a j) (r j) (i j) (flat j)) := by
  have C := ((Realizes.fix 2).times R).minused A
  have Z := (I.times C).plus (F.minused A)
  exact (((S.plus I).times A).plus F).select
    (Z.select (Z.plus (V.times A)) (Z.below (S.times A))) (F.below A)

/-- Unary pair encoding of the partial inverse of a borrowing placement. -/
def encodeLookup (q : Option (ℕ × ℕ)) : Option (Tally × Tally) :=
  q.map fun p => (tally p.1, tally p.2)

private theorem select_has {X : Type} [Codec X] {p : J → Prop} [DecidablePred p]
    {f g : J → X} (P : Classified s p) (F : s.Has f) (G : s.Has g) :
    s.Has (fun j => if p j then f j else g j) := by
  obtain ⟨b, B, hb⟩ := P
  have result := (B.pair (G.pair F)).ez (Easy.ifst Easy.fst Easy.snd)
  convert result using 1
  funext j
  cases h : b j <;> simp [h, hb j]

/-- Compute a local fiber number and flat rank on occupied cells, and emit
`none` at every unused physical rank. -/
theorem lookupRank_has (S : Realizes s start) (V : Realizes s v)
    (A : Realizes s a) (R : Realizes s r) (X : Realizes s phys) :
    s.Has (fun j => encodeLookup (lookupRank (start j) (v j) (a j) (r j) (phys j))) := by
  let z := fun j => if phys j < start j * a j then phys j else phys j - v j * a j
  let c := fun j => 2 * r j - a j
  have Z : Realizes s z := X.select (X.minused (V.times A)) (X.below (S.times A))
  have C : Realizes s c := ((Realizes.fix 2).times R).minused A
  have primary := (Regime.Has.pair ((X.dividing A).minused S) (X.rem A)).ez Easy.some
  have borrowed := (Regime.Has.pair (Z.dividing C) (A.plus (Z.rem C))).ez Easy.some
  have outside := select_has (Z.below (V.times C)) borrowed (Regime.fixed none)
  have output := select_has (X.below (S.times A)) outside
    (select_has (X.below ((S.plus V).times A)) primary outside)
  convert output using 1
  funext j
  by_cases h₁ : phys j < start j * a j <;> by_cases h₂ : phys j < (start j + v j) * a j <;>
    simp [lookupRank, encodeLookup, z, c, h₁, h₂, Nat.le_of_not_gt, Nat.not_le.mpr, apply_ite]

namespace PlacementTape

/-- The four fields are the start and size of the batch, the primary dimension,
and the padded dimension. -/
abbrev Shape := (Tally × Tally) × (Tally × Tally)

def physicalReply (p : Shape × Tally × Tally) : Tally :=
  tally (physicalRank p.1.1.1.length p.1.1.2.length p.1.2.1.length
    p.1.2.2.length p.2.1.length p.2.2.length)

def lookupReply (p : Shape × Tally) : Option (Tally × Tally) :=
  encodeLookup (lookupRank p.1.1.1.length p.1.1.2.length p.1.2.1.length
    p.1.2.2.length p.2.length)

private def input (X : Type) [Codec X] : Regime X := ⟨Code.size, send, Dom.base _⟩

private theorem field {X : Type} [Codec X] (f : X → Tally) (F : Easy f) :
    Realizes (input X) (fun x => (f x).length) := by
  have h : (input X).Has id := (input X).self
  simpa only [Realizes, Function.comp_def, id_eq, recover_tally] using h.ez F

theorem physicalReply_poly : Poly physicalReply :=
  physicalRank_realizes
    (field (fun p : Shape × Tally × Tally => p.1.1.1) (by fun_prop))
    (field (fun p : Shape × Tally × Tally => p.1.1.2) (by fun_prop))
    (field (fun p : Shape × Tally × Tally => p.1.2.1) (by fun_prop))
    (field (fun p : Shape × Tally × Tally => p.1.2.2) (by fun_prop))
    (field (fun p : Shape × Tally × Tally => p.2.1) (by fun_prop))
    (field (fun p : Shape × Tally × Tally => p.2.2) (by fun_prop))

theorem lookupReply_poly : Poly lookupReply :=
  lookupRank_has
    (field (fun p : Shape × Tally => p.1.1.1) (by fun_prop))
    (field (fun p : Shape × Tally => p.1.1.2) (by fun_prop))
    (field (fun p : Shape × Tally => p.1.2.1) (by fun_prop))
    (field (fun p : Shape × Tally => p.1.2.2) (by fun_prop))
    (field (fun p : Shape × Tally => p.2) (by fun_prop))

/-- One fixed deterministic machine evaluates the forward permutation address
query, with polynomially many steps and visited cells in the unary input size. -/
theorem physical_machine :
    PolyTreeMachine Code.size send (fun p => send (physicalReply p)) :=
  polyTreeMachine_of_BT physicalReply_poly (Dom.base _)

/-- One fixed deterministic machine evaluates the partial inverse, including
the unused-cell test, with polynomial time and visited-cell bounds. -/
theorem lookup_machine :
    PolyTreeMachine Code.size send (fun p => send (lookupReply p)) :=
  polyTreeMachine_of_BT lookupReply_poly (Dom.base _)

end PlacementTape
end SynchronizedBorrowing

end NearSquareRoot
end Computability
end OAI
