import OAI.Computability.NearSquareRoot.SynchronizedRoutingTable
import OAI.Computability.NearSquareRoot.PhaseProgramRelease
import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Polynomial tape programs for both local pair routing tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.RoutingTable

open IntegerMultiplication IntegerMultiplication.Code

section Generic
variable {A : Type} [Codec A] [DecidableEq A] [Inhabited A]

private def hits (p : A × A) : List Bool := if p.1 = p.2 then [true] else []

omit [Inhabited A] in
private theorem hits_poly (eq : Poly (fun p : A × A => decide (p.1=p.2))) : Poly (hits (A := A)) := by
  unfold hits
  simpa only [Bool.cond_decide] using Poly.choose eq (Code.Poly.const [true]) (Code.Poly.const [])

omit [Codec A] [Inhabited A] in
private theorem scan_hits (a : A) (l : List A) :
    ((l.flatMap (fun b => hits (a,b))).headD false) = decide (a ∈ l) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.flatMap_cons]
    by_cases h : a = b
    · subst b; simp [hits]
    · rw [show hits (a,b)=[] by simp [hits,h], List.nil_append,ih]
      simp [h]

theorem contains_poly (eq : Poly (fun p : A × A => decide (p.1=p.2))) :
    Poly (fun p : A × List A => decide (p.1 ∈ p.2)) := by
  have hp := (Poly.push default default (hits_poly eq)).compose (Easy.flatten.compose (Iter.leader false)).poly
  convert hp using 1
  funext p
  exact (scan_hits p.1 p.2).symm

private def idleRow (p : List A × A) : List A := if p.2 ∈ p.1 then [] else [p.2]

private theorem idleRow_poly (eq : Poly (fun p : A × A => decide (p.1=p.2))) : Poly (idleRow (A := A)) := by
  have choose := (Easy.exchange.poly.compose (contains_poly eq))
  unfold idleRow
  simpa only [Bool.cond_decide, Prod.fst_swap, Prod.snd_swap] using Poly.choose choose
    (Code.Poly.const []) (show Poly (fun p : List A × A => [p.2]) by fun_prop)

omit [Codec A] [Inhabited A] in
private theorem idleRow_filter (used rows : List A) :
    rows.flatMap (fun b => idleRow (used,b)) = rows.filter (fun b => b ∉ used) := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
    rw [List.flatMap_cons,ih]
    by_cases h : a ∈ used <;> simp [idleRow,h]

omit [DecidableEq A] [Inhabited A] in
theorem endpoints_poly : Poly (@endpoints A) := by
  exact (Poly.maps _ (show Poly (fun p : A × A => [p.1,p.2]) by fun_prop)).compose Easy.flatten.poly

/-- Construct the routing list for arbitrary encoded cells and active endpoint pairs. -/
theorem complete_poly (eq : Poly (fun p : A × A => decide (p.1=p.2))) :
    Poly (fun p : List A × List (A × A) => complete p.1 p.2) := by
  have used := (Easy.snd (X := List A) (Y := List (A × A))).poly.compose endpoints_poly
  have idle := ((used.pair Easy.fst.poly).compose (Poly.push [] default (idleRow_poly eq))).compose Easy.flatten.poly
  have result := (used.pair idle).compose Easy.append.poly
  convert result using 1
  funext p
  unfold complete
  exact congrArg (endpoints p.2 ++ ·) (idleRow_filter _ _).symm

end Generic

private theorem tallyEq : Poly (fun p : Tally × Tally => decide (p.1=p.2)) := by
  have h (x y : Tally) : (x=y) ↔ x.length=y.length := List.length_injective.eq_iff.symm
  simpa only [h] using (Iter.linked (X := Unit) (Y := Unit)).poly

abbrev Header := Tally × List (Tally × Tally)

/-- Flattened active pairs followed by the physical-order unused cells. -/
def encodeRouting (p : Header) : List Tally := complete (Iter.lineup p.1) p.2

@[fun_prop] theorem encodeRouting_poly : Poly encodeRouting :=
  ((Easy.fst.poly.compose Iter.poly_line).pair Easy.snd.poly).compose (complete_poly tallyEq)

/-- A table of physical address pairs, paired with the inverse table in matching order. -/
def bothTables (p : Header) : List (Tally × Tally) × List (Tally × Tally) :=
  let cells := encodeRouting p
  let rows := (Iter.lineup (ruler cells)).map (fun j => (j, Iter.pick [] (cells,j)))
  (rows, rows.map Prod.swap)

@[fun_prop] theorem bothTables_poly : Poly bothTables := by
  let read (q : List Tally × Tally) := (q.2, Iter.pick [] q)
  have rd : Poly read := Easy.snd.poly.pair (Iter.facile []).poly
  have rows := (encodeRouting_poly.pair (encodeRouting_poly.compose (Easy.ruler Easy.identity).poly |>.compose Iter.poly_line)).compose
    (Poly.push [] [] rd)
  exact rows.pair (rows.compose (Poly.maps _ Easy.exchange.poly))

/-- One finite deterministic multitape machine prepares both tables with polynomial time
and visited-cell bounds on the encoded header. -/
theorem bothTables_machine :
    PolyTreeMachine (fun p : Header => size p) (fun p => send p) (fun p => send (bothTables p)) :=
  polyTreeMachine_of_BT (bothTables_poly.on (Dom.base _)) (Dom.base _)

private theorem map_endpoints {A B : Type} (f : A → B) (ps : List (A × A)) :
    endpoints (ps.map (Prod.map f f)) = (endpoints ps).map f := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact congrArg (fun l => f p.1 :: f p.2 :: l) ih

private theorem map_complete {A B : Type} [DecidableEq A] [DecidableEq B] {f : A → B}
    (hf : Function.Injective f) (cells : List A) (ps : List (A × A)) :
    complete (cells.map f) (ps.map (Prod.map f f)) = (complete cells ps).map f := by
  unfold complete
  rw [map_endpoints, List.map_append]
  congr 1
  induction cells with
  | nil => rfl
  | cons a cells ih =>
    have hm : (f a ∈ (endpoints ps).map f) ↔ a ∈ endpoints ps := by
      simp [hf.eq_iff]
    simp only [List.map_cons,List.filter_cons]
    by_cases ha : a ∈ endpoints ps
    · rw [ite_eq_right (by simpa using hm.mpr ha),ite_eq_right (by simpa using ha),ih]
    · rw [ite_eq_left (by simpa using mt hm.mp ha),ite_eq_left (by simpa using ha),List.map_cons,ih]

def encodeAddress {n : ℕ} (x : Fin n) : Tally := tally x.val

private theorem encodeAddress_injective (n : ℕ) : Function.Injective (@encodeAddress n) := by
  intro a b h
  exact Fin.ext (by simpa [encodeAddress] using congrArg List.length h)

/-- The unary encoded header consumed by the table builder. -/
def header (n : ℕ) (ps : List (Fin n × Fin n)) : Header :=
  (tally n, ps.map (Prod.map encodeAddress encodeAddress))

theorem encodeRouting_correct {n : ℕ} (ps : List (Fin n × Fin n)) (hp : (endpoints ps).Nodup) :
    encodeRouting (header n ps) = List.ofFn (fun i : Fin n => encodeAddress (routing ps hp i)) := by
  have el : Iter.lineup (tally n) = (List.finRange n).map encodeAddress := by
    rw [Iter.lined, List.ofFn_eq_map]; rfl
  change complete (Iter.lineup (tally n)) (ps.map (Prod.map encodeAddress encodeAddress)) = _
  rw [el,map_complete (encodeAddress_injective n)]
  have he := complete_perm (List.finRange n) ps (List.nodup_finRange _) hp (by simp)
  apply List.ext_getElem (by simp [he.length_eq])
  intro i hi hj
  simp only [List.getElem_map,List.getElem_ofFn]
  rfl

/-- The two tables emitted by the physical program encode the forward routing and
its inverse, including on every unused cell. -/
theorem bothTables_correct {n : ℕ} (ps : List (Fin n × Fin n)) (hp : (endpoints ps).Nodup) :
    bothTables (header n ps) =
      (List.ofFn (fun i : Fin n => (encodeAddress i,encodeAddress (routing ps hp i))),
       List.ofFn (fun i : Fin n => (encodeAddress (routing ps hp i),encodeAddress i))) := by
  unfold bothTables
  rw [encodeRouting_correct ps hp]
  have hr : ruler (List.ofFn (fun i : Fin n => encodeAddress (routing ps hp i))) = tally n :=
    List.length_injective (by simp)
  dsimp only
  rw [hr,Iter.lined,List.map_ofFn,List.map_ofFn]
  congr 1 <;> apply congrArg List.ofFn <;> funext i <;> simp only [Function.comp_apply,Iter.entry] <;> rfl

end ShortFourier.RoutingTable

end NearSquareRoot
end Computability
end OAI
