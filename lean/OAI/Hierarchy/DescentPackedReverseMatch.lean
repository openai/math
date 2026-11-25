import OAI.Hierarchy.DescentPackedMatchingTable

namespace OAI
/-! # Reverse incidence in the published positive whole-match window -/

namespace Hierarchy.DescentPacking.PackedMatch
open DescentSIMDLookup PackedLocalMatch
open scoped Classical
noncomputable section
variable {s : Shape}

def handleField (thick : Bool) : Fin 12 := if thick then 8 else 5
def acceptedAt (out : Output s) (thick : Bool) (code : Cell s.digit) (j : Fin s.pairs) : Bool :=
  decide ((out.row j 0).val=1 ∧ out.row j (handleField thick)=code)

/-- A source inspects only its own bounded window. No dense global edge ordinal
is a key to this reverse lookup. -/
def reverse (out : Output s) (thick : Bool) (code : Cell s.digit) : Option (Fin s.pairs) :=
  (List.finRange s.pairs).find? (acceptedAt out thick code)

def handleOf (x : Inputs s) (h : Bounded x) (e : MatchedUnit x) (thick : Bool) : Cell s.digit :=
  let record:=fields (need x) (cap x) e
  let room:=bounds (need x) (cap x) e
  if thick then x.thick ⟨record.thick,room.2.2.2.trans_le h.thick⟩ 0
  else x.thin ⟨record.thin,room.2.2.1.trans_le h.thin⟩ 0

private theorem ordinal (x : Inputs s) (e : MatchedUnit x) :
    (fields (need x) (cap x) e).accepted=(pairNumber id (packing (need x) (cap x)).decisions e).val := rfl

theorem reported_handle (x : Inputs s) (h : Bounded x) (wide : 0<s.digit) (thick : Bool) (code : Cell s.digit)
    (e : MatchedUnit x) :
    let j : Fin s.pairs:=⟨(fields (need x) (cap x) e).accepted,unit_index x h e⟩
    acceptedAt (decodeOutput s (lookupCell s (encodeInput x))) thick code j=true ↔ handleOf x h e thick=code := by
  dsimp only
  simp only [acceptedAt,decide_eq_true_eq]
  rw [unit_row x h e]
  have one : (short s.digit 1).val=1 := short_val (Nat.one_lt_two_pow (by omega))
  cases thick <;> simp [describe,handleField,handleOf,one]

theorem reverse_live (x : Inputs s) (h : Bounded x) (wide : 0<s.digit) (thick : Bool) (code : Cell s.digit) :
    (reverse (decodeOutput s (lookupCell s (encodeInput x))) thick code).isSome=true ↔
      ∃e : MatchedUnit x,handleOf x h e thick=code := by
  unfold reverse
  rw [List.find?_isSome]
  constructor
  · rintro ⟨row,_,yes⟩
    by_cases existsRow : row.val<amount x
    · let rank:=pairNumber id (packing (need x) (cap x)).decisions
      let e : MatchedUnit x:=rank.symm ⟨row.val,existsRow⟩
      have same : (⟨(fields (need x) (cap x) e).accepted,unit_index x h e⟩ : Fin s.pairs)=row :=
        Fin.ext (congrArg (fun i : Fin (amount x) => i.val)
          (rank.apply_symm_apply ⟨row.val,existsRow⟩))
      rw [←same] at yes
      exact ⟨e,(reported_handle x h wide thick code e).mp yes⟩
    · simp only [acceptedAt,empty_row x h row (Nat.le_of_not_gt existsRow),Fin.val_zero,Nat.zero_ne_one,
        false_and,decide_false] at yes
      cases yes
  · rintro ⟨e,atE⟩
    exact ⟨_,List.mem_finRange _,(reported_handle x h wide thick code e).mpr atE⟩

/-- Every field returned by the reverse search is a real positive report
with the same numeric handle, even when unused rows share all-zero payloads. -/
theorem reverse_read (x : Inputs s) (h : Bounded x) (thick : Bool) (code : Cell s.digit)
    (j : Fin s.pairs) (got : reverse (decodeOutput s (lookupCell s (encodeInput x))) thick code=some j) :
    ∃e : MatchedUnit x,(fields (need x) (cap x) e).accepted=j.val ∧
      (decodeOutput s (lookupCell s (encodeInput x))).row j (handleField thick)=code := by
  have live:=List.find?_some got
  change acceptedAt _ thick code j=true at live
  have data:=(of_decide_eq_true live)
  have actual : j.val<amount x := by
    by_contra! past
    rw [empty_row x h j past] at data
    have := data.1
    simp at this
  let ranking:=pairNumber id (packing (need x) (cap x)).decisions
  refine ⟨ranking.symm ⟨j.val,actual⟩,?_,data.2⟩
  exact congrArg Fin.val (ranking.apply_symm_apply _)

end
end Hierarchy.DescentPacking.PackedMatch

end OAI
