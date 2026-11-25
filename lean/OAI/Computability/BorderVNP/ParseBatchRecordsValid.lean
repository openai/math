import OAI.Computability.BorderVNP.ParseBatchRecords

/-! # Soundness of the preorder encoding for the simultaneous child checks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP VPVNP.ParseGrammar

variable {V H : Type*} {n : ℕ}

private def Slice {α : Type*} (xs ys : List α) (offset : ℕ) : Prop :=
  offset + xs.length ≤ ys.length ∧ ∀ i < xs.length, ys[offset+i]? = xs[i]?

private theorem slice_left {α : Type*} (a : α) (xs ys : List α) :
    Slice xs (a :: (xs ++ ys)) 1 := by
  constructor
  · simp; omega
  · intro i hi
    rw [Nat.add_comm, List.getElem?_cons_succ, List.getElem?_append_left hi]

private theorem slice_right {α : Type*} (a : α) (xs ys : List α) :
    Slice ys (a :: (xs ++ ys)) (xs.length+1) := by
  constructor
  · simp; omega
  · intro i _
    rw [show xs.length + 1 + i = (xs.length + i) + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

private theorem root_shift {xs ys : List (GrammarLabel V H n)} {v u k : ℕ} {h : H}
    (hs : Slice xs ys v) (hx : RootAt xs u k h) : RootAt ys (v+u) k h := by
  obtain ⟨r, hread, hdepth, hstate⟩ := hx
  exact ⟨r, (hs.2 u (List.getElem?_eq_some_iff.mp hread).choose).trans hread, hdepth, hstate⟩

private theorem local_shift {xs ys : List (GrammarLabel V H n)} {v u : ℕ} {r : GrammarLabel V H n}
    (hs : Slice xs ys v) (hx : Local xs u r) : Local ys (v+u) r := by
  refine ⟨by have := hx.1; have := hs.1; omega, ?_⟩
  rcases r with r | ⟨d, h, b, i, j⟩
  · trivial
  · exact ⟨by simpa only [Nat.add_assoc] using root_shift hs hx.2.1,
           by simpa only [Nat.add_assoc] using root_shift hs hx.2.2⟩

/-- Every preorder certificate emitted by an ordered tree passes all interval, label,
and child-address checks simultaneously. -/
theorem encode_valid (d : Fin n) (h : H) (p : OrderedParse V H d.val) : Valid d h (encode d h p) := by
  induction d using (measure (fun d : Fin n => d.val)).wf.induction generalizing h with
  | h d ih =>
    refine ⟨encode_length .., encode_root .., ?_⟩
    obtain ⟨k, hk⟩ := d
    cases k with
    | zero =>
      cases p with
      | leaf v =>
        rw [encode]
        intro u r hr
        obtain ⟨hu, hval⟩ := List.getElem?_eq_some_iff.mp hr
        have : u = 0 := by simpa using hu
        subst u; subst r
        exact ⟨by simp [depth], trivial⟩
    | succ k =>
      cases p with
      | node b i j l r =>
        let d : Fin n := ⟨k+1,hk⟩
        let L := encode (leftDegree d b) i l
        let R := encode (rightDegree d b) j r
        let row : GrammarLabel V H n := .inr ⟨d,h,b,i,j⟩
        have hl := ih _ (leftDegree_lt d b) i l
        have hr := ih _ (rightDegree_lt d b) j r
        have hlLen : L.length = 2*b.val+1 := hl.1
        have hrLen : R.length = 2*(k-b.val)+1 := hr.1
        have sl := slice_left row L R
        have sr := slice_right row L R
        rw [encode]
        change ∀ u t, (row :: (L ++ R))[u]? = some t → Local (row :: (L ++ R)) u t
        intro u t ht
        cases u with
        | zero =>
          have ht' : row = t := Option.some.inj ht
          subst t
          refine ⟨?_, ?_, ?_⟩
          · simp only [row, depth, d, List.length_cons, List.length_append, hlLen, hrLen]
            have := b.isLt; omega
          · have hh := root_shift sl hl.2.1
            exact hh
          · have e : 0+2*(b.val+1) = (L.length+1)+0 := by omega
            rw [e]
            exact root_shift sr hr.2.1
        | succ u =>
          by_cases hu : u < L.length
          · have eq : L[u]? = some t := by
              simpa only [List.getElem?_cons_succ, List.getElem?_append_left hu] using ht
            simpa only [Nat.add_comm 1 u] using local_shift sl (hl.2.2 u t eq)
          · have hu' : L.length ≤ u := by omega
            have eq : R[u-L.length]? = some t := by
              simpa only [List.getElem?_cons_succ, List.getElem?_append_right hu'] using ht
            have e : u+1 = (L.length+1)+(u-L.length) := by omega
            rw [e]
            exact local_shift sr (hr.2.2 _ t eq)

end ParseRecords

end BorderVNP
end Computability
end OAI
