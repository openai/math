import OAI.Computability.BorderVNP.CellPacketGeometrySiteSort
import OAI.Computability.BorderVNP.CellPacketGeometrySitePrefix

/-! # Physical correctness of the stable site-sort inside the public word stream -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteSort

open ParseBatchSort VPVNP.VerifierNetwork
variable {s C N M R p q k w start : ℕ} {E : Type*} [Fintype E]

/-- The numerical final cell label and row word at one physical public source slot. -/
def pair (pins : Schema.Pins N M k w E → Bool) (i : Fin N) : ℕ × ℕ :=
  (value (fun j => pins (.inl (i,.inl j))),value (fun j => pins (.inl (i,.inr j))))

private theorem middle {A : Type*} (pre body post : List A) (j : ℕ) (hj : j<body.length) :
    (pre++body++post)[pre.length+j]? = body[j]? := by
  rw [List.append_assoc,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]

private theorem outer {A : Type*} (pre old new post : List A) (same : old.length=new.length) (i : ℕ)
    (outside : i < pre.length ∨ pre.length + old.length ≤ i) :
    (pre++old++post)[i]? = (pre++new++post)[i]? := by
  rcases outside with early | late
  · rw [List.append_assoc,List.append_assoc,List.getElem?_append_left early,List.getElem?_append_left early]
  · rw [List.getElem?_append_right (by simp only [List.length_append]; omega),
      List.getElem?_append_right (by simp only [List.length_append]; omega)]
    simp [same]

/-- Reconstruct the whole actual source column after the site sort, including
the unchanged source prefix and suffix. Only site IDs and the original physical
scalar words enter the table. The stable permutation is computed by its gates. -/
theorem splice_values (pre post : List (Fin C × ℕ)) (raw : List (Fin s × (Fin C × ℕ)))
    (nPre : pre.length=start) (nRaw : raw.length=R) (room : start+R ≤ N) (fit : R ≤ 2^p)
    (pad : s < 2^q) (x : Input N M R q k w E → Bool) (width : 2^p ≤ 2^(w+k))
    (fields : ∀ i : Fin N, (pre++raw.map Prod.snd++post)[i.val]?.map (fun z => (z.1.val,z.2)) =
      some (pair (fun z => x (.inl z)) i))
    (sites : ∀ i : Fin R, (raw[i.val]?).map (fun z => z.1.val) = some (value fun j => x (.inr (i,j)))) :
    let result := (frame room fit ⟨s,pad⟩).eval x
    let sorted := (List.finRange s).flatMap fun a => raw.filterMap fun z => if z.1=a then some z.2 else none
    (∀ i : Fin N, (pre++sorted++post)[i.val]?.map (fun z => (z.1.val,z.2)) = some (pair result i)) ∧
      ∀ z, result (.inr z) = x (.inl (.inr z)) := by
  subst start R
  intro result sorted
  obtain ⟨π,order,moved,kept,rest⟩ := frame_values room fit ⟨s,pad⟩ x width
  have row (i : Fin raw.length) : value (fun j => x (.inr (i,j))) = raw[i.val].1.val := by
    simpa only [List.getElem?_eq_getElem i.isLt,Option.map_some,Option.some.injEq] using (sites i).symm
  have keys (i : Fin (2^p)) : key s (fun a => value fun j => x (.inr (a,j))) i = SiteOrder.rowKey raw i.val := by
    simp only [key,SiteOrder.rowKey,row]
  simp only [keys] at order
  have len : sorted.length = raw.length := SiteOrder.sorted_prefix_length raw fit π order
  refine ⟨fun i => ?_,rest⟩
  by_cases h : pre.length ≤ i.val ∧ i.val-pre.length < raw.length
  · let j : Fin raw.length := ⟨i.val-pre.length,h.2⟩
    have dest : pos room j = i := Fin.ext (by simp [pos,j]; omega)
    obtain ⟨hi,selected⟩ := SiteOrder.sorted_prefix_get raw fit π order j
    let src : Fin raw.length := ⟨(π (j.castLE fit)).val,hi⟩
    have source := fields (pos room src)
    change (pre++raw.map Prod.snd++post)[pre.length+src.val]?.map _ = _ at source
    rw [middle _ _ _ _ (by simp),List.getElem?_map,List.getElem?_eq_getElem src.isLt,
      Option.map_some,Option.map_some,Option.some.injEq] at source
    rw [← dest]
    change (pre++sorted++post)[pre.length+j.val]?.map _ = _
    rw [middle _ _ _ _ (j.isLt.trans_le len.ge),selected,Option.map_some,Option.some.injEq]
    have eqn : pair result (pos room j) = pair (fun z => x (.inl z)) (pos room src) :=
      Prod.ext (congrArg value (funext fun a => moved j hi (.inl a)))
        (congrArg value (funext fun a => moved j hi (.inr a)))
    exact source.trans eqn.symm
  · have outside : i.val < pre.length ∨ pre.length+raw.length ≤ i.val := by omega
    have old := fields i
    rw [outer pre (raw.map Prod.snd) sorted post (by simpa using len.symm) i.val (by simpa using outside)] at old
    have eqn : pair result i = pair (fun z => x (.inl z)) i :=
      Prod.ext (congrArg value (funext fun a => kept i outside (.inl a)))
        (congrArg value (funext fun a => kept i outside (.inr a)))
    exact old.trans (congrArg some eqn.symm)

end CellPacketGeometry.SiteSort

end BorderVNP
end Computability
end OAI
