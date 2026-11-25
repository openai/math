import OAI.Computability.IntegerMultiplication.Code.Auto

/-! # Packing adjacent records into butterfly inputs

An odd-bit butterfly pairs consecutive records on a lexicographic tape.
Both conversions below have linear cost in the encoded array size.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PairRows

open IntegerMultiplication IntegerMultiplication.Code

variable {X : Type*}

/-- The serialization of a row of ordered pairs as consecutive records. -/
def consecutive (l : List (X × X)) : List X := l.flatMap (fun p => [p.1, p.2])

@[simp] theorem consecutive_nil : consecutive ([] : List (X × X)) = [] := rfl

@[simp] theorem consecutive_cons (p : X × X) (l : List (X × X)) :
    consecutive (p :: l) = p.1 :: p.2 :: consecutive l := rfl

variable [Codec X]

theorem size_consecutive (l : List (X × X)) : size (consecutive l) = size l := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [ih]; omega

private def pairBody : Cmd :=
  splitRoot 0 (give 0) <|
    (move 0 1 2).join (splitRoot 0 (fun _ => .pass) <|
      (move 1 0 2).join ((pack 0).join <|
        (move 0 1 2).join ((Prog.again 0).join ((move 1 0 2).join (pack 0)))))

private theorem fits_pairBody (l : List (X × X)) (env : Env) (tail : Deck) :
    Fits (pairBody :: env) pairBody (pile 0 (send (consecutive l)) tail)
      (pile 0 (send l) tail) (200 * size l) := by
  induction l generalizing tail with
  | nil =>
    exact (fits_bit (c := give 0) (b := false) (fits_give false tail 0 _)).mono (by simp)
  | cons p l ih =>
    let G := pairBody :: env
    let x := send p.1
    let y := send p.2
    let s := send (consecutive l)
    have parkX := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide) x G
      (pile 0 (.fork y s) tail)
    rw [pile_comm 1 x tail 0 _ (by decide)] at parkX
    have restoreX := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide) x G
      (pile 0 y (pile 0 s tail))
    rw [pile_comm 1 x _ 0 y (by decide), pile_comm 1 x tail 0 s (by decide)] at restoreX
    have pair := fits_pack x y (pile 0 s tail) 0 G
    have parkPair := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide)
      (.fork x y) G (pile 0 s tail)
    rw [pile_comm 1 (.fork x y) tail 0 s (by decide)] at parkPair
    have recur := Fits.again0 (ih (pile 1 (.fork x y) tail))
    have restorePair := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide)
      (.fork x y) G (pile 0 (send l) tail)
    rw [pile_comm 1 (.fork x y) tail 0 _ (by decide)] at restorePair
    have prepend := fits_pack (.fork x y) (send l) tail 0 G
    have scan := restoreX.join (pair.join (parkPair.join (recur.join (restorePair.join prepend))))
    refine (fits_pair (parkX.join (fits_pair scan))).mono ?_
    simp only [x, y, Tree.count, size_cons, size_prod]
    simp only [size]
    omega

/-- Compile the stream scan that turns adjacent records into encoded pairs. -/
theorem packPairs : Task size (fun l : List (X × X) => send (consecutive l)) send := by
  refine ⟨.tie pairBody, 200, fun l env tail => ?_⟩
  exact (fits_pairBody l env tail).tie.mono (by omega)

/-- Write the two components of each pair to consecutive output positions. -/
theorem unpackPairs : Easy (consecutive (X := X)) := by
  have localPair : Easy (fun p : X × X => [p.1, p.2]) := by fun_prop
  have flatten := localPair.mapping.compose Easy.flatten
  have h : consecutive (X := X) =
      (fun l : List (X × X) => (l.map fun p => [p.1, p.2]).flatten) := by
    funext l
    induction l with
    | nil => rfl
    | cons p l ih => simp [ih]
  rw [h]
  exact flatten

end PairRows

end NearSquareRoot
end Computability
end OAI
