import OAI.Hierarchy.DescentMatchedPairOrdinal

namespace OAI
/-! # Bounded relative records of the exact whole-item allocator -/

noncomputable section
namespace Hierarchy.DescentPacking.PackedLocalMatch
open scoped Classical BigOperators

structure Record where
  accepted : ℕ
  bin : ℕ
  thin : ℕ
  thick : ℕ
  deriving DecidableEq, Repr

variable {packs bins limit : ℕ}

/-- Numerical physical index in the first-fit directory. -/
def position (n : ℕ) : Equiv.Perm (Fin n) :=
  (Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin _))

def packing (need : Fin packs→ℕ) (cap : Fin bins→ℕ) :=
  pack (id : ℕ→ℕ) (List.ofFn need) (cap ∘ position bins)

abbrev Unit (need : Fin packs→ℕ) (cap : Fin bins→ℕ) :=
  Pairs (id : ℕ→ℕ) (packing need cap).decisions

theorem length (need : Fin packs→ℕ) (cap : Fin bins→ℕ) : (packing need cap).decisions.length=packs := by
  simpa using congrArg List.length (packing need cap).order

def index (need : Fin packs→ℕ) (cap : Fin bins→ℕ) :=
  finCongr (length need cap)

theorem amount_at (need : Fin packs→ℕ) (cap : Fin bins→ℕ) (i : Fin (packing need cap).decisions.length) :
    ((packing need cap).decisions.get i).1=need (index need cap i) := by
  have small : i.val<packs := i.isLt.trans_eq (length need cap)
  have h := congrArg (fun l : List ℕ=>l[i.val]?) (packing need cap).order
  calc
    _ = need ⟨i.val,small⟩ := by
      simpa only [List.getElem?_map,List.getElem?_ofFn,small,dite_eq_left,List.getElem?_eq_getElem i.isLt,
          Option.map_some,Option.some.injEq,List.get_eq_getElem] using h
    _ = _ := congrArg need (Fin.ext rfl)

def fields (need : Fin packs→ℕ) (cap : Fin bins→ℕ) (e : Unit need cap) : Record :=
  let ds := (packing need cap).decisions
  let i := index need cap e.2.1.val
  let v := position bins e.1
  ⟨(pairNumber id ds e).val,v.val,ProtocolRAMPortRanks.«prefix» need Fin.val i+e.2.2.val,
    ProtocolRAMPortRanks.«prefix» cap Fin.val v+(thickEnd (packing need cap) e).2.val⟩

private def pairAtLocation (need : Fin packs→ℕ) (cap : Fin bins→ℕ)
    (t : Locations (packing need cap).decisions) (j : Fin limit) : Option (Unit need cap) :=
  let row := (packing need cap).decisions.get t
  if yes : row.2.isSome then
    if fits : j.val<row.1 then some ⟨row.2.get yes,⟨t,(Option.some_get yes).symm⟩,⟨j.val,fits⟩⟩ else none
  else none

def pairAt (need : Fin packs→ℕ) (cap : Fin bins→ℕ) (i : Fin packs) (j : Fin limit) : Option (Unit need cap) :=
  pairAtLocation need cap ((index need cap).symm i) j

def record (need : Fin packs→ℕ) (cap : Fin bins→ℕ) (i : Fin packs) (j : Fin limit) : Option Record :=
  (pairAt need cap i j).map (fields need cap)

/-- The dense index is the actual chronological accepted-unit rank. Invalid
decoded need fields are skipped when they exceed the public query window. -/
def dense (need : Fin packs→ℕ) (cap : Fin bins→ℕ) (limit u : ℕ) : Option Record :=
  if h : u<Fintype.card (Unit need cap) then
    let e := (pairNumber id (packing need cap).decisions).symm ⟨u,h⟩
    if e.2.2.val<limit then some (fields need cap e) else none
  else none

theorem record_at (need : Fin packs→ℕ) (cap : Fin bins→ℕ) (e : Unit need cap) (j : Fin limit)
    (offset : j.val=e.2.2.val) :
    record need cap (index need cap e.2.1.val) j=some (fields need cap e) := by
  obtain ⟨v,⟨t,choice⟩,q⟩ := e
  let ds := (packing need cap).decisions
  have valid : (ds.get t).2.isSome := by rw [choice]; rfl
  have fits : j.val<(ds.get t).1 := offset ▸ q.isLt
  let original : Unit need cap := ⟨v,⟨t,choice⟩,q⟩
  let numbered := byItem id ds
  have flat : (⟨⟨t,valid⟩,⟨j.val,fits⟩⟩ : Σ u : Active ds,Fin ((ds.get u.val).1)) =
      numbered original := by
    have same : (⟨j.val,fits⟩ : Fin ((ds.get t).1))=q := Fin.ext offset
    exact congrArg (fun x : Fin ((ds.get t).1) =>
      (⟨⟨t,valid⟩,x⟩ : Σ u : Active ds, Fin ((ds.get u.val).1))) same
  change (pairAtLocation need cap ((index need cap).symm ((index need cap) t)) j).map (fields need cap)=_
  rw [Equiv.symm_apply_apply]
  unfold pairAtLocation
  dsimp only
  rw [dite_eq_left valid,dite_eq_left fits]
  change some (fields need cap (numbered.symm ⟨⟨t,valid⟩,⟨j.val,fits⟩⟩))=some (fields need cap original)
  rw [flat,Equiv.symm_apply_apply]

theorem dense_at (need : Fin packs→ℕ) (cap : Fin bins→ℕ) (e : Unit need cap) (live : e.2.2.val<limit) :
    dense need cap limit (fields need cap e).accepted=some (fields need cap e) := by
  let f := pairNumber id (packing need cap).decisions
  change (if h : (f e).val<Fintype.card (Unit need cap) then _ else _)=_
  rw [dite_eq_left (f e).isLt]
  change (if (f.symm (f e)).2.2.val<limit then some (fields need cap (f.symm (f e))) else none)=_
  rw [Equiv.symm_apply_apply,ite_eq_left live]

theorem dense_none (need : Fin packs→ℕ) (cap : Fin bins→ℕ) (u : ℕ)
    (bounded : ∀j,need j≤limit) :
    dense need cap limit u=none ↔ Fintype.card (Unit need cap)≤u := by
  by_cases h : u<Fintype.card (Unit need cap)
  · let q : Fin (Fintype.card (Unit need cap)) := ⟨u,h⟩
    let e := (pairNumber id (packing need cap).decisions).symm q
    have room : e.2.2.val<limit := e.2.2.isLt.trans_le ((amount_at need cap e.2.1.val).le.trans (bounded _))
    simp only [dense,dite_eq_left h]
    change ((if e.2.2.val<limit then some (fields need cap e) else none)=none) ↔ _
    rw [ite_eq_left room]
    constructor
    · intro impossible
      contradiction
    · intro oversize
      exact False.elim (h.not_ge oversize)
  · rw [dense,dite_eq_right h]
    exact iff_of_true rfl (Nat.le_of_not_gt h)

theorem record_void (need : Fin packs→ℕ) (cap : Fin bins→ℕ) (i : Fin packs) (j : Fin limit)
    (empty : need i≤j.val) : record need cap i j=none := by
  have same := amount_at need cap ((index need cap).symm i)
  rw [Equiv.apply_symm_apply] at same
  have h : ¬j.val<((packing need cap).decisions.get ((index need cap).symm i)).1 := by omega
  by_cases valid : ((packing need cap).decisions.get ((index need cap).symm i)).2.isSome
  · unfold record pairAt pairAtLocation
    dsimp only
    rw [dite_eq_left valid,dite_eq_right h]; rfl
  · unfold record pairAt pairAtLocation
    dsimp only
    rw [dite_eq_right valid]; rfl

theorem count_le (need : Fin packs→ℕ) (cap : Fin bins→ℕ) : Fintype.card (Unit need cap)≤∑i,need i := by
  have bound := Fintype.card_le_of_injective _ (thinEnd_injective id (packing need cap).decisions)
  let ds := (packing need cap).decisions
  calc
    Fintype.card (Unit need cap) ≤ Fintype.card (Σ i : Locations ds,Fin ((ds.get i).1)) := bound
    _ = ∑ i : Locations ds,(ds.get i).1 := by simp
    _ = _ := Fintype.sum_equiv (index need cap) _ _ (amount_at need cap)

theorem count_le_window (need : Fin packs→ℕ) (cap : Fin bins→ℕ) (small : ∀i,need i≤limit) :
    Fintype.card (Unit need cap)≤packs*limit := by
  apply (count_le need cap).trans
  simpa using (Finset.sum_le_sum (s:=Finset.univ) (fun i _=>small i))

theorem bounds (need : Fin packs→ℕ) (cap : Fin bins→ℕ) (e : Unit need cap) :
    let r := fields need cap e
    r.accepted<(∑i,need i) ∧ r.bin<bins ∧ r.thin<(∑i,need i) ∧ r.thick<∑v,cap v := by
  let i := index need cap e.2.1.val
  let v := position bins e.1
  have thin : e.2.2.val<need i := e.2.2.isLt.trans_le (amount_at need cap _).le
  have thick : (thickEnd (packing need cap) e).2.val<cap v := (thickEnd (packing need cap) e).2.isLt
  exact ⟨(pairNumber id (packing need cap).decisions e).isLt.trans_le (count_le need cap),
    v.isLt,(Nat.add_lt_add_left thin _).trans_le (ProtocolRAMPortRanks.prefix_end need Fin.val i),
    (Nat.add_lt_add_left thick _).trans_le (ProtocolRAMPortRanks.prefix_end cap Fin.val v)⟩

end Hierarchy.DescentPacking.PackedLocalMatch

end
end OAI
