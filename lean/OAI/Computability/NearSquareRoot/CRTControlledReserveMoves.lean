import OAI.Computability.NearSquareRoot.CRTControlledReserveConjugate
import OAI.Computability.IntegerMultiplication.Match

/-! # Producing the reserve exchanges from a unary position table

The program enumerates all positions in order, looks up their images and keeps
the occupied end positions and fixed interior positions in two lists. The
result pairs the lists up to the length of the shorter one.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open NearSquareRoot.Controlled.Reflections (Pair Table table next next_table)

private abbrev Input := Tally × Tally × Table

private def starts (z : Input) : Tally :=
  (cutLists (z.2.1, ruler z.2.2)).2

@[local fun_prop] private theorem starts_poly : Poly starts :=
  (easy_cut (show Easy (fun z : Input => (z.2.1, ruler z.2.2)) by fun_prop)).sndCompose.poly

private def onEnd (v : Input × Tally) :=
  Iter.small (v.2, v.1.1) || !(Iter.small (v.2, starts v.1))

@[local fun_prop] private theorem onEnd_poly : Poly onEnd := by
  have left : Poly (fun v : Input × Tally => (v.2,v.1.1)) := by fun_prop
  have right : Poly (fun v : Input × Tally => (v.2,starts v.1)) := by fun_prop
  exact ((left.compose Iter.small_easy.poly).pair ((right.compose Iter.small_easy.poly).compose
    Iter.negate.poly)).compose Iter.conn_easy.poly

private def stays (v : Input × Tally) := decide ((next (v.1.2.2, v.2)).length = v.2.length)

@[local fun_prop] private theorem stays_poly : Poly stays := by
  have args : Poly (fun v : Input × Tally => (next (v.1.2.2,v.2),v.2)) := by fun_prop
  exact args.compose Iter.linked.poly

private def keep (bad : Bool) (v : Input × Tally) :=
  bif bad then onEnd v && !(stays v) else !(onEnd v) && stays v

@[local fun_prop] private theorem keep_poly (bad : Bool) : Poly (keep bad) := by
  have both : Easy (fun b : Bool × Bool => b.1 && b.2) := Easy.finite _
  cases bad with
  | false => exact ((onEnd_poly.compose Iter.negate.poly).pair stays_poly).compose both.poly
  | true => exact (onEnd_poly.pair (stays_poly.compose Iter.negate.poly)).compose both.poly

private def endpoints (bad : Bool) (z : Input) : List Tally :=
  ((polyPush id (z, Iter.lineup (ruler z.2.2))).filter (keep bad)).map Prod.snd

@[local fun_prop] private theorem endpoints_poly (bad : Bool) : Poly (endpoints bad) := by
  have len : Easy (fun z : Input => ruler z.2.2) := by fun_prop
  have enumeration := (Poly.identity (X := Input)).pair (len.poly.compose Iter.poly_line)
  have pairs := enumeration.compose (Poly.push ([],[],[]) ([] : Tally) Poly.identity)
  exact (pairs.compose (Poly.filter _ (keep_poly bad))).compose (Poly.maps _ Easy.snd.poly)

private theorem zip_easy : Easy (fun z : List Tally × List Tally => z.1.zip z.2) := by
  let fit (z : List Tally × List Tally) :=
    ((cutLists (ruler z.2,z.1)).1, (cutLists (ruler z.1,z.2)).1)
  have hfit : Easy fit := (easy_cut (by fun_prop)).fstCompose.pair (easy_cut (by fun_prop)).fstCompose
  convert hfit.compose (easy_zip [] []) using 1
  funext z
  rcases z with ⟨l,r⟩
  have h := fair Prod.fst Prod.snd (l.zip r) ([] : Tally) ([] : Tally)
  have proj (a b : List Tally) : (a.zip b).map Prod.fst = a.take b.length ∧
      (a.zip b).map Prod.snd = b.take a.length := by
    induction a generalizing b with
    | nil => simp
    | cons c a ih => cases b with
      | nil => simp
      | cons d b => simp [List.take_succ_cons, (ih b).1, (ih b).2]
  simpa [fit, cutLists, (proj l r).1, (proj l r).2] using h.symm

/-- The unary pairs passed to the elementary exchanges, in matching order. -/
def gather (z : Tally × Tally × Table) : List Pair :=
  (endpoints true z).zip (endpoints false z)

@[fun_prop] theorem gather_poly : Poly gather :=
  ((endpoints_poly true).pair (endpoints_poly false)).compose zip_easy.poly

private theorem enumeration_value {k : ℕ} (p : Equiv.Perm (Fin k)) :
    Iter.lineup (ruler (table p)) = (List.finRange k).map (fun j => tally j.val) := by
  rw [← recover_tally (ruler (table p)), ruler_length, show (table p).length = k by simp [table],
    Iter.lined, ← List.ofFn_id k, List.map_ofFn]
  rfl

private theorem keep_value {k : ℕ} (p : Equiv.Perm (Fin k)) (lo hi : ℕ) (j : Fin k) (bad : Bool) :
    keep bad ((tally lo,tally hi,table p),tally j.val) =
      (bif bad then endPosition lo hi j && decide (p j ≠ j)
       else !(endPosition lo hi j) && decide (p j = j)) := by
  have endEq : onEnd ((tally lo,tally hi,table p),tally j.val) = endPosition lo hi j := by
    simp only [onEnd, endPosition, Iter.small, starts, cutLists, table, List.length_drop, ruler_length,
      List.length_ofFn, tally_length, Bool.decide_or, ← decide_not, not_lt]
  have fixEq : stays ((tally lo,tally hi,table p),tally j.val) = decide (p j = j) := by
    simp only [stays,next_table,tally_length,Fin.val_inj]
  cases bad <;> simp [keep,endEq,fixEq]

private theorem endpoints_value {k : ℕ} (p : Equiv.Perm (Fin k)) (lo hi : ℕ) (bad : Bool) :
    endpoints bad (tally lo,tally hi,table p) =
      (bif bad then misplaced p lo hi else available p lo hi).map (fun j => tally j.val) := by
  simp only [endpoints, polyPush, enumeration_value, List.map_map, List.filter_map, Function.comp_def, id_eq,
    keep_value]
  cases bad <;> rfl

theorem gather_value {k : ℕ} (p : Equiv.Perm (Fin k)) (lo hi : ℕ) :
    gather (tally lo,tally hi,table p) =
      encodedMoves (reserveMoves p lo hi) := by
  simp only [encodedMoves, gather, endpoints_value, Bool.cond_true, Bool.cond_false, reserveMoves,
    List.zip_map]
  apply List.map_congr_left
  intro xy _
  cases xy
  rfl

theorem gather_uniform {X : Type} {r : Regime X} (k lo hi : X → ℕ)
    (p : (x : X) → Equiv.Perm (Fin (k x)))
    (low : r.Has (tally ∘ lo)) (high : r.Has (tally ∘ hi)) (tab : r.Has fun x => table (p x)) :
    r.Has (fun x => encodedMoves (reserveMoves (p x) (lo x) (hi x))) := by
  have h := (low.pair (high.pair tab)).thenDo gather_poly
  simpa only [Function.comp_apply, gather_value] using h

end Controlled.ReserveProgram

end NearSquareRoot
end Computability
end OAI
