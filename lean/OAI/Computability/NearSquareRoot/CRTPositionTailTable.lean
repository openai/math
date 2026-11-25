import OAI.Computability.NearSquareRoot.CRTPositionDescriptor
import OAI.Computability.NearSquareRoot.CRTPositionTailFold

/-! # Computing the bulk restriction and its remaining individual exchanges

A boundary splits the position indices into a bulk prefix and a short suffix.
The program enumerates only the suffix when issuing individual exchanges. An edge
within the suffix is emitted by its smaller endpoint, and an edge crossing the
boundary is emitted by its suffix endpoint.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.TailTable
open IntegerMultiplication IntegerMultiplication.Code
open Reflections (Table Pair table next next_table)

abbrev Query := Tally × Table

private def bulkImage (x : Query × Tally) : Tally :=
  let y := next (x.1.2,x.2)
  bif Iter.small (y,x.1.1) then y else x.2

private theorem poly_bulkImage : Poly bulkImage := by
  let Y := Query × Tally
  have q : Easy (fun x : Y => next (x.1.2,x.2)) := by fun_prop
  exact Poly.choose ((q.pair (by fun_prop)).compose Iter.small_easy).poly q.poly Easy.snd.poly

private def tailRow (z : Tally × Tally × Tally) : List Pair :=
  bif Iter.small (z.2.2,z.1) then [(z.2.1,z.2.2)] else
    bif Iter.small (z.2.1,z.2.2) then [(z.2.1,z.2.2)] else []

private theorem poly_tailRow : Poly tailRow := by
  let Z := Tally × Tally × Tally
  have a : Poly (fun z : Z => Iter.small (z.2.2,z.1)) := (show Easy _ by fun_prop).poly
  have b : Poly (fun z : Z => Iter.small (z.2.1,z.2.2)) := (show Easy _ by fun_prop).poly
  have entry : Poly (fun z : Z => [z.2]) :=
    (Easy.snd.poly.pair (Code.Poly.const [])).compose Code.Poly.cons
  exact Poly.choose a entry (Poly.choose b entry (Code.Poly.const []))

private def tailImage (x : Query × Tally) : List Pair :=
  let j := x.1.1 ++ x.2
  tailRow (x.1.1,j,next (x.1.2,j))

private theorem poly_tailImage : Poly tailImage := by
  have h : Easy (fun x : Query × Tally => (x.1.1,x.1.1 ++ x.2,next (x.1.2,x.1.1 ++ x.2))) := by
    fun_prop
  exact h.poly.compose poly_tailRow

/-- The first table addresses the bulk alone. Each pair in the second table is
an exchange on the original index space. -/
def prepare (q : Query) : Table × List Pair :=
  (polyPush bulkImage (q,Iter.lineup q.1),
    (polyPush tailImage (q,Iter.lineup (cutLists (q.1,ruler q.2)).2)).flatten)

@[fun_prop] theorem poly_prepare : Poly prepare := by
  have a := (Easy.identity.poly.pair (Easy.fst.poly.compose Iter.poly_line)).compose
    (Poly.push ([],[]) [] poly_bulkImage)
  have clock : Easy (fun x : Query => (cutLists (x.1,ruler x.2)).2) :=
    (easy_cut (g := fun x : Query => (x.1,ruler x.2)) (by fun_prop)).sndCompose
  have b := ((Easy.identity.poly.pair (clock.poly.compose Iter.poly_line)).compose
    (Poly.push ([],[]) [] poly_tailImage)).compose Easy.flatten.poly
  exact a.pair b

private def tailIndex {n k : ℕ} (i : Fin (k-n)) : Fin k := ⟨n+i.val,by omega⟩

variable {n k : ℕ} (p : Equiv.Perm (Fin k)) (h : n ≤ k)

def bulkVal (x : Fin n) : Fin n :=
  let y := p (Fin.castLE h x)
  if hy : y.val < n then ⟨y.val,hy⟩ else x

theorem bulkVal_involutive (hp : Function.Involutive p) : Function.Involutive (bulkVal p h) := by
  intro x
  by_cases hy : (p (Fin.castLE h x)).val < n
  · have e : Fin.castLE h (bulkVal p h x) = p (Fin.castLE h x) := by
      apply Fin.ext; simp [bulkVal,hy]
    have second : p (Fin.castLE h (bulkVal p h x)) = Fin.castLE h x := e ▸ hp (Fin.castLE h x)
    have good : (p (Fin.castLE h (bulkVal p h x))).val < n := second.symm ▸ x.isLt
    have val_of (y : Fin n) (inb : (p (Fin.castLE h y)).val < n) :
        (bulkVal p h y).val = (p (Fin.castLE h y)).val := by simp [bulkVal,inb]
    exact Fin.ext ((val_of _ good).trans (congrArg Fin.val second))
  · have e : bulkVal p h x = x := by simp [bulkVal,hy]
    rw [e,e]

def residual (hp : Function.Involutive p) : Equiv.Perm (Fin n) :=
  ⟨bulkVal p h,bulkVal p h,bulkVal_involutive p h hp,bulkVal_involutive p h hp⟩


def owners : List (Fin k) :=
  (List.ofFn (tailIndex (k := k) (n := n))).filter (fun j => decide ((p j).val < n ∨ j < p j))

theorem owners_length : (owners (n := n) p).length ≤ k - n :=
  (List.length_filter_le ..).trans (List.length_ofFn.le)

private theorem add_tally (a b : ℕ) : tally a ++ tally b = tally (a+b) := by
  rw [← recover_tally (tally a ++ tally b)]
  simp

private theorem bulkImage_eval (x : Fin n) :
    bulkImage ((tally n,table p),tally x.val) = tally (bulkVal p h x).val := by
  change (bif Iter.small (next (table p,tally (Fin.castLE h x).val),tally n)
    then next (table p,tally (Fin.castLE h x).val) else tally x.val) = _
  rw [next_table]
  by_cases hy : (p (Fin.castLE h x)).val < n <;> simp [bulkVal,Iter.small,hy]

private theorem tailImage_eval (z : Fin (k-n)) :
    let j := tailIndex z
    tailImage ((tally n,table p),tally z.val) =
      if (p j).val < n ∨ j < p j then [(tally j.val,tally (p j).val)] else [] := by
  dsimp only
  let j : Fin k := tailIndex z
  unfold tailImage
  dsimp only
  rw [add_tally]
  change tailRow (tally n,tally j.val,next (table p,tally j.val)) = _
  rw [next_table]
  by_cases lo : (p j).val < n <;> by_cases lt : j < p j <;>
    simp [tailRow,Iter.small,lo,lt,j] at *

private theorem packRows {A B : Type} (l : List A) (keep : A → Prop) [DecidablePred keep]
    (f : A → B) :
    (l.map (fun a => if keep a then [f a] else [])).flatten = (l.filter (fun a => decide (keep a))).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : keep a <;> simp [h,ih]

/-- Exact images computed by the bulk and individual-exchange tables. -/
theorem prepare_spec (hp : Function.Involutive p) :
    prepare (tally n,table p) =
      (table (residual p h hp),
        (owners (n := n) p).map (fun j => (tally j.val,tally (p j).val))) := by
  have clk : (cutLists (tally n,ruler (table p))).2 = tally (k-n) := by
    rw [← recover_tally ((cutLists (tally n,ruler (table p))).2)]
    simp [cutLists,table]
  simp only [prepare,clk,polyPush,Iter.lined]
  apply Prod.ext
  · rw [List.map_ofFn]
    exact congrArg List.ofFn (funext (bulkImage_eval p h))
  · simp only [List.map_ofFn,Function.comp_def,tailImage_eval]
    simpa only [owners,List.map_ofFn,Function.comp_def] using
      packRows (List.ofFn (tailIndex (k := k) (n := n)))
        (fun j => (p j).val < n ∨ j < p j) (fun j => (tally j.val,tally (p j).val))


theorem mem_owners (x : Fin k) : x ∈ owners (n := n) p ↔ n ≤ x.val ∧ ((p x).val < n ∨ x < p x) := by
  simp only [owners,List.mem_filter,List.mem_ofFn,decide_eq_true_eq,and_congr_left_iff]
  intro _
  constructor
  · rintro ⟨z,rfl⟩
    exact Nat.le_add_right ..
  · intro hx
    refine ⟨⟨x.val-n,by omega⟩,Fin.ext ?_⟩
    dsimp [tailIndex]
    omega

private theorem owners_nodup : (owners (n := n) p).Nodup := by
  apply List.Nodup.filter
  apply List.nodup_ofFn_ofInjective
  intro a b e
  apply Fin.ext
  have t := congrArg Fin.val e
  dsimp [tailIndex] at t
  omega

/-- The extension of the emitted bulk table to all indices fixes the tail. -/
def extended (x : Fin k) : Fin k :=
  if x.val < n ∧ (p x).val < n then p x else x

theorem extended_bulk (i : Fin n) (hp : Function.Involutive p) :
    extended (n := n) p (Fin.castLE h i) = Fin.castLE h (residual p h hp i) := by
  apply Fin.ext
  change (extended (n := n) p (Fin.castLE h i)).val = (bulkVal p h i).val
  by_cases hy : (p (Fin.castLE h i)).val < n <;> simp [extended,bulkVal,i.isLt,hy]

theorem extended_tail (x : Fin k) (hx : n ≤ x.val) : extended (n := n) p x = x := by
  simp [extended,not_lt_of_ge hx]

/-- Executing the particular list of tail transpositions returned by the table
generator after the bulk permutation gives the input involution at every position. -/
theorem run_owners (hp : Function.Involutive p) (x : Fin k) :
    (owners (n := n) p).foldl (fun a j => Equiv.swap j (p j) a) (extended (n := n) p x) = p x := by
  have distinct : ∀ i ∈ owners (n := n) p, p i ∉ owners (n := n) p := by
    intro i hi hpi
    rw [mem_owners] at hi hpi
    rw [hp i] at hpi
    omega
  rw [tailSwaps_fold p hp _ (owners_nodup p) distinct]
  by_cases hb : x.val < n ∧ (p x).val < n
  · simp [extended,hb,mem_owners,hp x,Nat.not_le_of_gt hb.1,Nat.not_le_of_gt hb.2]
  · rw [extended,ite_eq_right hb]
    by_cases same : p x = x
    · simp [same]
    · apply ite_eq_left
      simp only [mem_owners,hp x]
      have ne : (p x).val ≠ x.val := fun e => same (Fin.ext e)
      change n ≤ x.val ∧ ((p x).val < n ∨ x.val < (p x).val) ∨ n ≤ (p x).val ∧ (x.val < n ∨ (p x).val < x.val)
      omega

theorem three_chunks_count (p : Equiv.Perm (Fin k)) : (owners (n := 3*(k/3)) p).length ≤ 2 :=
  (owners_length p).trans (by omega)

end Controlled.TailTable

end NearSquareRoot
end Computability
end OAI
