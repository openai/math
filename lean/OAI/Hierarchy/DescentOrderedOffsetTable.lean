import OAI.Hierarchy.DescentSparseWordOrder

namespace OAI
/-! # One pass over all sorted items computes every local contact offset -/

namespace Hierarchy.DescentOrderedWords
open scoped BigOperators Classical
variable {I C : Type*} [DecidableEq C] (tag : I→C) (size : I→ℕ)

/-- In a row-addressed array the iteration reads and updates just the one
counter named by its contact. The second result counts these row visits. -/
def makeOffsets (initial : C→ℕ) : List I→List (I×ℕ)×ℕ
  | [] => ([],0)
  | a::as =>
    let c := tag a
    let start := initial c
    let tail := makeOffsets (fun j=>if j=c then start+size a else initial j) as
    ((a,start)::tail.1,tail.2+1)

theorem visits (initial : C→ℕ) (xs : List I) : (makeOffsets tag size initial xs).2=xs.length := by
  induction xs generalizing initial with
  | nil => rfl
  | cons a as ih => simp [makeOffsets,ih]

theorem rowIds (initial : C→ℕ) (xs : List I) : (makeOffsets tag size initial xs).1.map Prod.fst=xs := by
  induction xs generalizing initial with
  | nil => rfl
  | cons a as ih => simp [makeOffsets,ih]

def paidBefore (c : C) (xs : List I) := (xs.map fun j=>if tag j=c then size j else 0).sum

theorem row_at (initial : C→ℕ) (pre : List I) (i : I) (post : List I) :
    (i,initial (tag i)+paidBefore tag size (tag i) pre)∈(makeOffsets tag size initial (pre++i::post)).1 := by
  induction pre generalizing initial with
  | nil => simp [paidBefore,makeOffsets]
  | cons a as ih =>
    apply List.mem_cons_of_mem
    let after := fun c=>if c=tag a then initial (tag a)+size a else initial c
    have eq : initial (tag i)+paidBefore tag size (tag i) (a::as)=after (tag i)+paidBefore tag size (tag i) as := by
      by_cases same : tag a=tag i
      · simp [paidBefore,after,same,Nat.add_assoc]
      · simp [paidBefore,after,same,Ne.symm same]
    exact eq ▸ ih after

variable {N : ℕ} (key : I↪Fin N)

/-- An input certificate here is only the address order of the existing rows.
The prefix/offset table is computed once for all contacts together. -/
theorem prefix_eq {pre post : List I} {i : I}
    (sorted : (pre++i::post).Pairwise (fun x y=>key x<key y)) :
    paidBefore tag size (tag i) pre=
      ((pre++i::post).map (fun j=>if key j<key i then if tag j=tag i then size j else 0 else 0)).sum := by
  have ss := List.pairwise_append.mp sorted
  have a : ∀x∈pre,key x<key i := fun x hx=>ss.2.2 x hx i (List.mem_cons_self ..)
  have b : ∀x∈post,key i<key x := (List.pairwise_cons.mp ss.2.1).1
  have eqpre := List.map_congr_left (f:=fun j=>if key j<key i then if tag j=tag i then size j else 0 else 0)
    (g:=fun j=>if tag j=tag i then size j else 0) (l:=pre) (fun x hx=>ite_eq_left (a x hx))
  have eqpost := List.map_congr_left (f:=fun j=>if key j<key i then if tag j=tag i then size j else 0 else 0)
    (g:=fun _=>0) (l:=post) (fun x hx=>ite_eq_right (not_lt_of_gt (b x hx)))
  simp [paidBefore,List.map_append,eqpre,eqpost]

variable [Fintype I]
theorem realised (directory : List I) (sorted : directory.Pairwise (fun x y=>key x<key y))
    (nodup : directory.Nodup) (whole : ∀i,i∈directory) (i : I) :
    (i,offset key (fun j=>if tag j=tag i then size j else 0) i)∈
      (makeOffsets tag size (fun _=>0) directory).1 := by
  obtain ⟨pre,post,eq⟩ := List.append_of_mem (whole i)
  subst directory
  have receipt := row_at tag size (fun _=>0) pre i post
  rw [Nat.zero_add,prefix_eq tag size key sorted] at receipt
  have same := congrArg Prod.fst (scan_offset key (fun j=>if tag j=tag i then size j else 0) (pre++i::post) nodup whole i)
  rw [scan_spec] at same
  change ((pre++i::post).map (fun j => if key j<key i then if tag j=tag i then size j else 0 else 0)).sum =
    offset key (fun j => if tag j=tag i then size j else 0) i at same
  rwa [same] at receipt

/-- A local cell's offset in its compact word agrees with the global pass
which increments just this cell's counter on each actual bundle. -/
theorem fibre_offset (i : I) :
    offset ((Function.Embedding.subtype (fun j=>tag j=tag i)).trans key)
      (fun j=>size j.val) ⟨i,rfl⟩ = offset key (fun j=>if tag j=tag i then size j else 0) i := by
  classical
  rw [offset,offset,←Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨by simpa [before] using hj, j.property⟩
  · intro x _ y _ same
    exact Subtype.ext same
  · intro j hj
    obtain ⟨earlier,matched⟩ := Finset.mem_filter.mp hj
    refine ⟨⟨j,matched⟩,?_,rfl⟩
    simpa [before] using earlier
  · intro j _
    rfl

end Hierarchy.DescentOrderedWords

end OAI
