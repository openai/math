import OAI.Computability.NearSquareRoot.SynchronizedPlacedPermutation
import OAI.Computability.NearSquareRoot.SynchronizedPlacementTape

/-! # Unary tape queries for a permutation at a borrowing placement

Given the tape evaluator for a local source rank, evaluate the corresponding
physical row and column. Each active coordinate is decoded by integer division
and remainder. The generator preserves unused cells and padded columns.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open IntegerMultiplication Code Strip Staff SynchronizedBorrowing

namespace PlacedPermutationTape

variable {J : Type} {s : Regime J}

/-- Spelling of the two physical source coordinates. -/
def coordinates (p : ℕ × ℕ) : Tally × Tally := (tally p.1, tally p.2)

private theorem choose {X : Type} [Codec X] {p : J → Prop} [DecidablePred p]
    {f g : J → X} (test : Classified s p) (yes : s.Has f) (no : s.Has g) :
    s.Has (fun j => if p j then f j else g j) := by
  obtain ⟨flag, available, correct⟩ := test
  have selected := (available.pair (no.pair yes)).ez (Easy.ifst Easy.fst Easy.snd)
  convert selected using 1
  funext j
  cases h : flag j <;> simp [h, correct j]

/-- A polynomial computation of an arbitrary local rank map gives a polynomial
computation of the corresponding physical source coordinates on every query. -/
theorem placedPermTarget_has {start v a r row col : J → ℕ} {f : J → ℕ → ℕ}
    (S : Realizes s start) (V : Realizes s v) (A : Realizes s a) (R : Realizes s r)
    (Row : Realizes s row) (Col : Realizes s col)
    (F : ∀ t : J → ℕ, Realizes s t → Realizes s (fun j => f j (t j))) :
    s.Has (fun j => coordinates (placedPermTarget (start j) (v j) (a j) (r j)
      (f j) (row j) (col j))) := by
  let raw := fun j => row j * a j + col j
  let z := fun j => if raw j < start j * a j then raw j else raw j - v j * a j
  let c := fun j => 2*r j - a j
  have X : Realizes s raw := (Row.times A).plus Col
  have Z : Realizes s z := X.select (X.minused (V.times A)) (X.below (S.times A))
  have C : Realizes s c := ((Realizes.fix 2).times R).minused A
  have hit {i t : J → ℕ} (I : Realizes s i) (T : Realizes s t) :
      s.Has (fun j => let x := physicalRank (start j) (v j) (a j) (r j) (i j) (f j (t j))
        coordinates (x / a j, x % a j)) := by
    have x := physicalRank_realizes S V A R I (F t T)
    exact Regime.Has.pair (x.dividing A) (x.rem A)
  have idle : s.Has (fun j => coordinates (row j,col j)) := Regime.Has.pair Row Col
  have primary := hit ((X.dividing A).minused S) (X.rem A)
  have spare := hit (Z.dividing C) (A.plus (Z.rem C))
  have rest := choose (Z.below (V.times C)) spare idle
  have inside := choose (X.below (S.times A)) rest
    (choose (X.below ((S.plus V).times A)) primary rest)
  have out := choose (Col.below A) inside idle
  convert out using 1
  funext j
  simp only [placedPermTarget, lookupRank, show row j * a j + col j = raw j from rfl,
    show 2 * r j - a j = c j from rfl,
    show (if raw j < start j * a j then raw j else raw j - v j * a j) = z j from rfl]
  by_cases h₁ : raw j < start j * a j <;> by_cases h₂ : raw j < (start j + v j) * a j <;>
    by_cases h₃ : z j < v j * c j <;> by_cases h₄ : col j < a j <;>
    simp [h₁, h₂, h₃, h₄, Nat.not_le.mpr, Nat.le_of_not_gt]

/-- The local rank evaluator may inspect an extra header, such as an opcode and
its radix stage index. All six shape and coordinate fields are unary. -/
abbrev Query (H : Type) := H × PlacementTape.Shape × Tally × Tally

def reply {H : Type} (f : H → ℕ → ℕ) (q : Query H) : Tally × Tally :=
  coordinates (placedPermTarget q.2.1.1.1.length q.2.1.1.2.length
    q.2.1.2.1.length q.2.1.2.2.length (f q.1) q.2.2.1.length q.2.2.2.length)

private def input (X : Type) [Codec X] : Regime X := ⟨Code.size, send, Dom.base _⟩

private theorem field {X : Type} [Codec X] (f : X → Tally) (hf : Easy f) :
    Realizes (input X) (fun x => (f x).length) := by
  have h : (input X).Has id := (input X).self
  simpa only [Realizes, Function.comp_def, id_eq, recover_tally] using h.ez hf

theorem reply_poly {H : Type} [Codec H] (f : H → ℕ → ℕ)
    (hf : Poly (fun x : H × Tally => tally (f x.1 x.2.length))) : Poly (reply f) := by
  apply placedPermTarget_has (s := input (Query H)) (f := fun q => f q.1)
    (field (fun q : Query H => q.2.1.1.1) (by fun_prop))
    (field (fun q : Query H => q.2.1.1.2) (by fun_prop))
    (field (fun q : Query H => q.2.1.2.1) (by fun_prop))
    (field (fun q : Query H => q.2.1.2.2) (by fun_prop))
    (field (fun q : Query H => q.2.2.1) (by fun_prop))
    (field (fun q : Query H => q.2.2.2) (by fun_prop))
  intro t T
  have q : (input (Query H)).Has id := (input _).self
  have hdr : (input (Query H)).Has (fun q => q.1) := q.ez Easy.fst
  simpa only [Realizes, Function.comp_def, tally_length] using (hdr.pair T).thenDo hf

/-- One deterministic multitape machine evaluates all placed rank queries for
this local evaluator. Its time and visited-cell count are polynomial in the
size of the header and the six unary fields. -/
theorem reply_machine {H : Type} [Codec H] (f : H → ℕ → ℕ)
    (hf : Poly (fun x : H × Tally => tally (f x.1 x.2.length))) :
    PolyTreeMachine Code.size send (fun q => send (reply f q)) :=
  polyTreeMachine_of_BT (reply_poly f hf) (Dom.base _)

end PlacedPermutationTape
end ShortFourier

end NearSquareRoot
end Computability
end OAI
