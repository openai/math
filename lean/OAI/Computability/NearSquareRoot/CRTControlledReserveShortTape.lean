import OAI.Computability.NearSquareRoot.CRTPositionDescriptor
import OAI.Computability.IntegerMultiplication.Staff.Nat

/-! # Preparing two short matchings on the unary position table

The program lists the smaller endpoint of each pair in ascending order. Its first
output handles the first ceiling-quarter of these endpoints. The second output
handles the remaining pairs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveShort

open IntegerMultiplication IntegerMultiplication.Code
open NearSquareRoot.Controlled.Reflections (Table table next next_table)

private def filterWith {A B : Type} (pred : A × B → Bool) (z : A × List B) : List B :=
  z.2.filter fun b => pred (z.1,b)

private theorem poly_filterWith {A B : Type} [Codec A] [Codec B] (a : A) (b : B)
    {pred : A × B → Bool} (h : Poly pred) : Poly (filterWith pred) := by
  let emit (p : A × B) : List B := bif pred p then [p.2] else []
  have he : Poly emit := Poly.choose h (by fun_prop) (Code.Poly.const [])
  have H := (Poly.push a b he).compose Easy.flatten.poly
  suffices eq : filterWith pred = fun z => (polyPush emit z).flatten from eq ▸ H
  funext z
  rcases z with ⟨v,bs⟩
  unfold filterWith polyPush
  induction bs with
  | nil => rfl
  | cons x xs ih => cases e : pred (v,x) <;> simp [emit, e, ih]

private def addresses (t : Table) : List Tally := Iter.lineup (ruler t)

@[local fun_prop] private theorem poly_addresses : Poly addresses := (Easy.ruler Easy.identity).poly.compose Iter.poly_line

private def smaller (z : Table × Tally) : Bool := Iter.small (z.2, next z)

@[local fun_prop] private theorem poly_smaller : Poly smaller := (Easy.snd.poly.pair Reflections.poly_next).compose Iter.small_easy.poly

private def quota (t : Table) : Tally := (Staff.quot (ruler t ++ tally 3,tally 4)).1

@[local fun_prop] private theorem poly_quota : Poly quota := by
  have h : Easy (fun t : Table => (ruler t ++ tally 3,tally 4)) := by fun_prop
  exact (h.poly.compose Staff.stable_q).fstCompose

/-- Encoded smaller endpoints used by the first factor. -/
def kept (t : Table) : List Tally := (filterWith smaller (t,addresses t)).take (quota t).length

@[fun_prop] theorem poly_kept : Poly kept := by
  have hl := (Poly.identity.pair poly_addresses).compose (poly_filterWith [] [] poly_smaller)
  exact ((poly_quota.pair hl).compose (easy_cut Easy.identity).poly).fstCompose

private def contains (z : Tally × Table) : Bool := decide (z.1 ∈ z.2)

private theorem poly_contains : Poly contains := by
  let same (z : Tally × Tally) := decide (z.1.length = z.2.length)
  have found := poly_filterWith ([] : Tally) ([] : Tally) (pred := same) Iter.linked.poly
  have test := ((Code.Poly.const ([] : Table)).pair found).compose (Iter.small_easy (X := Tally) (Y := Tally)).poly
  convert test using 1
  funext z
  change decide (z.1 ∈ z.2) = decide (0 < (z.2.filter fun b => decide (z.1.length = b.length)).length)
  simp only [decide_eq_decide]
  constructor
  · intro hz
    exact List.length_pos_iff_exists_mem.mpr ⟨z.1, List.mem_filter.mpr ⟨hz, by simp⟩⟩
  · intro h
    obtain ⟨b,hb⟩ := List.length_pos_iff_exists_mem.mp h
    obtain ⟨mem,test⟩ := List.mem_filter.mp hb
    have eq : z.1 = b := by rw [← recover_tally z.1, of_decide_eq_true test, recover_tally]
    rwa [eq]

private def minor (z : Tally × Tally) : Tally := bif Iter.small z then z.1 else z.2

@[local fun_prop] private theorem poly_minor : Poly minor := Poly.choose Iter.small_easy.poly Easy.fst.poly Easy.snd.poly

private def allot (z : Table × (Tally × Tally)) : Tally × Tally :=
  bif contains (minor z.2,z.1) then (z.2.2,z.2.1) else z.2

private theorem poly_allot : Poly allot := by
  unfold allot
  exact Poly.choose ((by fun_prop : Poly (fun z : Table × (Tally × Tally) => (minor z.2,z.1))).compose
    poly_contains) (by fun_prop) (by fun_prop)

private def successors (t : Table) : List (Tally × Tally) :=
  polyPush (fun z => (z.2,next z)) (t,addresses t)

@[local fun_prop] private theorem poly_successors : Poly successors :=
  (Poly.identity.pair poly_addresses).compose (Poly.push [] [] (by fun_prop))

/-- Produce both permutation tables in their original position order. -/
def split (t : Table) : Table × Table :=
  let rows := polyPush allot (kept t,successors t)
  (rows.map Prod.fst, rows.map Prod.snd)

@[fun_prop] theorem poly_split : Poly split := by
  have rows := (poly_kept.pair poly_successors).compose (Poly.push [] ([],[]) poly_allot)
  exact (rows.compose (Poly.maps _ Easy.fst.poly)).pair (rows.compose (Poly.maps _ Easy.snd.poly))

private theorem addresses_table {k : ℕ} (p : Equiv.Perm (Fin k)) :
    addresses (table p) = (List.finRange k).map (fun j => tally j.val) := by
  unfold addresses
  rw [← recover_tally (ruler (table p)), ruler_length, show (table p).length = k by simp [table],
    Iter.lined, ← List.ofFn_id k, List.map_ofFn]
  rfl

private theorem quota_length (t : Table) : (quota t).length = (t.length+3)/4 := by
  unfold quota
  rw [← recover_tally (ruler t ++ tally 3), List.length_append, ruler_length, tally_length,
    Staff.quot_r, tally_length]

theorem kept_value {k : ℕ} (p : Equiv.Perm (Fin k)) :
    kept (table p) = (((List.finRange k).filter (fun j => decide (j < p j))).take ((k+3)/4)).map
      (fun j => tally j.val) := by
  have ht : (table p).length = k := by simp [table]
  simp only [kept, quota_length, filterWith, addresses_table, List.filter_map, List.map_take,
    smaller, next_table, Iter.small, tally_length, Function.comp_def, ht]
  rfl

private theorem allot_value {k : ℕ} (p : Equiv.Perm (Fin k)) (j : Fin k) :
    allot (kept (table p),tally j.val,tally (p j).val) =
      if min j (p j) ∈ ((List.finRange k).filter (fun a => decide (a < p a))).take ((k+3)/4) then
        (tally (p j).val,tally j.val) else (tally j.val,tally (p j).val) := by
  have hm : minor (tally j.val,tally (p j).val) = tally (min j (p j)).val := by
    by_cases h : j < p j
    · simp [minor, Iter.small, min_eq_left h.le, show j.val < (p j).val from h]
    · simp [minor, Iter.small, min_eq_right (le_of_not_gt h), show ¬j.val < (p j).val from h]
  rw [allot, hm, kept_value]
  have inj : Function.Injective (fun i : Fin k => tally i.val) := by
    intro x y h
    apply Fin.ext
    simpa only [tally_length] using congrArg List.length h
  unfold contains
  simp only [List.mem_map_of_injective inj, Bool.cond_decide]

theorem split_value {k : ℕ} (p : Equiv.Perm (Fin k)) :
    let selected j := min j (p j) ∈ ((List.finRange k).filter fun a => decide (a < p a)).take ((k+3)/4)
    split (table p) =
      (List.ofFn fun j => if selected j then tally (p j).val else tally j.val,
       List.ofFn fun j => if selected j then tally j.val else tally (p j).val) := by
  dsimp only
  simp only [split, successors, addresses_table, polyPush, ← List.ofFn_id k, List.map_ofFn,
    Function.comp_def, id_eq, next_table, allot_value]
  apply Prod.ext <;> apply congrArg List.ofFn <;> funext j <;> split_ifs <;> rfl

end Controlled.ReserveShort

end NearSquareRoot
end Computability
end OAI
