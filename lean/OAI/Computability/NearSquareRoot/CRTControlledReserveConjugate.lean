import OAI.Computability.NearSquareRoot.CRTControlledReserve
import OAI.Computability.NearSquareRoot.CRTPositionDescriptor
import OAI.Computability.IntegerMultiplication.Code.Loop

/-! # Compiling conjugation by a list of position transpositions

Each cursor is unary. A swap changes it only to another endpoint already in the
stored list; the fold therefore has a uniform polynomial intermediate-size bound.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveProgram
open IntegerMultiplication IntegerMultiplication.Code
open NearSquareRoot.Controlled.Reflections

def endpointPair {k : ℕ} (p : Fin k × Fin k) : Pair := (tally p.1.val,tally p.2.val)

def encodedMoves {k : ℕ} (l : List (Fin k × Fin k)) := l.map endpointPair

private def cursorSwap (z : Tally × Pair) :=
  bif decide (z.1.length = z.2.1.length) then z.2.2 else
  bif decide (z.1.length = z.2.2.length) then z.2.1 else z.1

private theorem cursorSwap_poly : Poly cursorSwap := by
  have eq₁ := (Easy.fst.pair (Easy.snd.compose Easy.fst) : Easy (fun z : Tally × Pair => (z.1,z.2.1))).compose (Iter.linked (X := Unit) (Y := Unit))
  have eq₂ := (Easy.fst.pair (Easy.snd.compose Easy.snd) : Easy (fun z : Tally × Pair => (z.1,z.2.2))).compose (Iter.linked (X := Unit) (Y := Unit))
  exact Poly.choose eq₁.poly (by fun_prop) (Poly.choose eq₂.poly (by fun_prop) (by fun_prop))

private theorem cursorSwap_size (x : Tally) (y : Pair) : size (cursorSwap (x,y)) ≤ size x + size y := by
  unfold cursorSwap
  cases h : decide (x.length = y.1.length) <;> cases g : decide (x.length = y.2.length) <;>
    simp only [Bool.cond_false,Bool.cond_true,size_prod] <;> omega

def sweep (z : List Pair × Tally) := z.1.foldl (fun x y => cursorSwap (x,y)) z.2

private theorem sweep_size (l : List Pair) (x : Tally) : size (sweep (l,x)) ≤ size x + size l := by
  induction l generalizing x with
  | nil => simp [sweep]
  | cons p ps ih =>
    change size (sweep (ps,cursorSwap (x,p))) ≤ _
    have ht := ih (cursorSwap (x,p))
    have hu := cursorSwap_size x p
    rw [size_cons]; omega

@[fun_prop] theorem sweep_poly : Poly sweep := by
  apply Poly.fold_left cursorSwap_poly 1 1
  intro z l h
  obtain ⟨rest,ht⟩ := h
  have e := sweep_size l z.2
  have cap := size_append_right l rest
  rw [ht] at cap
  have := size_pos rest
  simp only [one_mul,pow_one]
  exact e.trans (by rw [size_prod]; omega)

private theorem cursorSwap_value {k : ℕ} (p : Fin k × Fin k) (x : Fin k) :
    cursorSwap (tally x.val,endpointPair p) = tally ((Equiv.swap p.1 p.2) x).val := by
  by_cases h : x = p.1
  · subst x
    simp [cursorSwap,endpointPair]
  · by_cases v : x = p.2
    · subst x
      have ne : p.2.val ≠ p.1.val := fun e => h (Fin.ext e)
      simp [cursorSwap,endpointPair,ne]
    · have u₁ : x.val ≠ p.1.val := fun e => h (Fin.ext e)
      have u₂ : x.val ≠ p.2.val := fun e => v (Fin.ext e)
      simp [cursorSwap,endpointPair,u₁,u₂,Equiv.swap_apply_of_ne_of_ne h v]

theorem sweep_value {k : ℕ} (l : List (Fin k × Fin k)) (x : Fin k) :
    sweep (encodedMoves l,tally x.val) = tally ((positionExchanges l).symm x).val := by
  induction l generalizing x with
  | nil => rfl
  | cons p ps ih =>
    change sweep (encodedMoves ps,cursorSwap (tally x.val,endpointPair p)) = _
    rw [cursorSwap_value, ih]
    rfl

theorem exchange_append {α : Type} [DecidableEq α] (l m : List (α × α)) :
    positionExchanges (l ++ m) = (positionExchanges m).trans (positionExchanges l) := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    apply Equiv.ext
    intro i
    change Equiv.swap p.1 p.2 (positionExchanges (ps++m) i) = _
    rw [ih]; rfl

theorem exchange_reverse {α : Type} [DecidableEq α] (l : List (α × α)) :
    positionExchanges l.reverse = (positionExchanges l).symm := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    rw [List.reverse_cons,exchange_append,ih]
    rfl

private def image (z : (List Pair × Table) × Tally) :=
  let mv := z.1.1
  sweep (mv, next (z.1.2, sweep (mv.reverse,z.2)))

@[fun_prop] private theorem image_poly : Poly image := by
  unfold image
  fun_prop

def conjugate (z : List Pair × Table) : Table :=
  polyPush image (z,Iter.lineup (ruler z.2))

@[fun_prop] theorem conjugate_poly : Poly conjugate := by
  have ticks : Poly (fun z : List Pair × Table => Iter.lineup (ruler z.2)) := (Easy.ruler Easy.snd).poly.compose Iter.poly_line
  exact (Poly.identity.pair ticks).compose (Poly.push ([],[]) [] image_poly)

theorem conjugate_value {k : ℕ} (p : Equiv.Perm (Fin k)) (l : List (Fin k × Fin k)) :
    conjugate (encodedMoves l,table p) =
      table (((positionExchanges l).trans p).trans (positionExchanges l).symm) := by
  have e : ruler (table p) = tally k := by rw [← recover_tally (ruler (table p)),ruler_length]; simp [table]
  change (Iter.lineup (ruler (table p))).map (fun j => image ((encodedMoves l,table p),j)) =
    List.ofFn _
  rw [e, Iter.lined, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  change sweep (encodedMoves l, next (table p,sweep ((encodedMoves l).reverse,tally j.val))) = _
  rw [show (encodedMoves l).reverse = encodedMoves l.reverse from List.map_reverse.symm,
    sweep_value,exchange_reverse,Equiv.symm_symm, next_table,sweep_value]
  rfl

end Controlled.ReserveProgram

end NearSquareRoot
end Computability
end OAI
