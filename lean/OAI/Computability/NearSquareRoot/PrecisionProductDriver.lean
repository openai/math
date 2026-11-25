import OAI.Computability.IntegerMultiplication.Code.Task

/-! # Record-by-record product passes

The dispatcher keeps the untouched input suffix on stack zero and the
already computed outputs in reverse order on stack one. Each call processes a
single input record and returns to this layout before the next dispatch.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductDriver

open IntegerMultiplication IntegerMultiplication.Code

variable {X Y : Type*} [Codec X] [Codec Y]

/-- Physical stack layout at a dispatch boundary, with caller data below. -/
def ready (xs : List X) (out : List Y) (tail : Deck) : Deck :=
  pile 0 (.fork (send xs) (.atom false)) (pile 1 (send out) tail)

/-- Dispatch boundary for a standalone pass. -/
def packet (xs : List X) (out : List Y) : Deck := ready xs out (fun _ => [])

private theorem commute_pile_one (a b : Tree) (r : Deck) :
    pile 1 a (pile 0 b r) = pile 0 b (pile 1 a r) := pile_comm 1 a r 0 b (by decide)

/-- A dispatch step removes the input marker and cons constructor, applies
the command to the exposed record, and moves the result before re-tagging
both streams. The suffix and previous output have no traversal cost. -/
def stepCmd (c : Cmd) : Cmd :=
  splitRoot 0 (fun _ => .pass) <|
    splitRoot 0 (fun _ => .pass) <|
      c.join <| (move 0 1 2).join <| (pack 1).join (pack 0)

theorem exists_step {f : X → Y} {b : X → ℕ} (h : Computes b f) :
    ∃ step : Cmd, ∃ C : ℕ, ∀ x xs out tail env,
      Fits env step (ready (x::xs) out tail) (ready xs (f x::out) tail)
        (C*(b x + size (f x) + 1)) := by
  obtain ⟨c, C, hc⟩ := h
  refine ⟨stepCmd c, C+60, ?_⟩
  intro x xs out tail env
  let marker : Tree := .atom false
  let base := pile 0 (send xs) (pile 0 marker (pile 1 (send out) tail))
  have call := hc x env base
  have moved := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide)
    (send (f x)) env base
  have cons := fits_pack (send (f x)) (send out)
    (pile 0 (send xs) (pile 0 marker tail)) 1 env
  simp only [commute_pile_one] at cons
  have tagged := fits_pack (send xs) marker (pile 1 (send (f x::out)) tail) 0 env
  simp only [base, commute_pile_one] at moved
  apply (fits_pair (fits_pair (call.join (moved.join (cons.join tagged))))).mono
  change C*(b x+1) + (42 * size (f x) + (1+1+2)+2)+2+4+4 ≤ _
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- Insert the query sentinel beneath the input, then initialize the output register. -/
def loadCmd : Cmd :=
  (move 0 1 2).join ((give 0 false).join ((move 1 0 2).join ((pack 0).join (give 1 false))))

theorem fits_load (xs : List X) (tail : Deck) (env : Env) :
    Fits env loadCmd (pile 0 (send xs) tail) (ready xs ([] : List Y) tail)
      (200 * (size xs + 1)) := by
  let z := send xs
  let marker := Tree.atom false
  have park := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide) z env tail
  have init := fits_give false (pile 1 z tail) 0 env
  have restore := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide) z env
    (pile 0 marker tail)
  rw [pile_comm 1 z tail 0 marker (by decide)] at restore
  have pair := fits_pack z marker tail 0 env
  have out := fits_give false (pile 0 (.fork z marker) tail) 1 env
  rw [pile_comm 1 _ tail 0 _ (by decide)] at out
  exact (park.join (init.join (restore.join (pair.join out)))).mono (by
    change _ ≤ 200 * (z.count + 1)
    omega)

/-- Consume the exhausted query and sentinel; return the output from its register. -/
def emitCmd : Cmd :=
  splitRoot 0 (fun _ => .pass)
    (splitRoot 0 (fun _ => splitRoot 0 (fun _ => move 1 0 2) .pass) .pass)

theorem fits_emit (out : List Y) (tail : Deck) (env : Env) :
    Fits env emitCmd (ready ([] : List X) out tail) (pile 0 (send out) tail)
      (200 * (size out + 1)) := by
  have h := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide) (send out) env tail
  exact (fits_pair (fits_bit (b := false) (fits_bit (b := false) h))).mono (by
    change _ ≤ 200 * ((send out).count + 1)
    omega)

end ProductDriver

end NearSquareRoot
end Computability
end OAI
