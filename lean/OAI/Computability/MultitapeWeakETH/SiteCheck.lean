import OAI.Computability.MultitapeWeakETH.AddressProgram
import OAI.Computability.MultitapeWeakETH.FrameDecoding

/-! # The Boolean checks at variable slots and clause sites -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SiteCheck

open Algorithms.SubexponentialSAT IntegerMultiplication Code Carry FormulaRanks
open private left left_poly tail tail_poly from OAI.Computability.MultitapeWeakETH.EndpointProgram

abbrev Row := Bool × Bool

/-- Existential search over a materialized list of records. -/
theorem any_poly {A : Type} [Codec A] (test : A → Bool) (ht : Poly test) : Poly (fun xs : List A => xs.any test) := by
  let existsOne (xs : List A) : Bool := List.casesOn (motive:=fun _ => Bool) xs false (fun _ _ => true)
  have p : Poly (fun xs : List A => existsOne (xs.filter test)) :=
    (Poly.filter test ht).compose (Easy.listCase false (Easy.const true)).poly
  convert p using 1
  funext xs
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : test x <;> simp_all [List.any_cons,List.filter,existsOne]

def check (q : Bool × List Row) : Bool :=
  bif q.1 then !(q.2.any Prod.fst) || !(q.2.any (fun r => !r.1))
  else q.2.any (fun r => r.1 == r.2)

theorem check_poly : Poly check := by
  have someBit (f : Row → Bool) := Easy.snd (X:=Bool) |>.poly.compose (any_poly f (Easy.finite f).poly)
  have nope (f : Row → Bool) := (someBit f).compose Iter.negate.poly
  exact Poly.choose Easy.fst.poly (((nope Prod.fst).pair (nope (fun r => !r.1))).compose Iter.conn_easy.poly)
    (someBit (fun r => r.1 == r.2))

private theorem check_slot (ls : List Row) :
    check (true,ls) = true ↔ ∃ b : Bool, ∀ r ∈ ls, r.1=b := by
  simp only [check,Bool.cond_true,Bool.or_eq_true,Bool.not_eq_eq_eq_not,Bool.not_true]
  cases e : ls.any Prod.fst <;> cases f : ls.any (fun r : Row => !r.1) <;>
    simp_all [List.any_eq_false,List.any_eq_true,Bool.exists_bool]
  grind

private theorem check_clause (ls : List Row) :
    check (false,ls) = true ↔ ∃ r ∈ ls, r.1=r.2 := by simp [check]

/-- The third number of a clause endpoint key is its encoded literal.
The one-offset unary representation reverses the parity. -/
def sign (e : Key) : Bool := !(half ((tail (tail e)).headD [])).2

theorem sign_poly : Poly sign :=
  (tail_poly.compose tail_poly).compose ((Iter.leader []).compose halfCost.sndCompose |>.compose Iter.negate).poly

variable {n : ℕ} (F : SAT.CNF (Fin n))

private theorem sign_literal (p : Occ F) : sign (encodeKey (endKey F (.inr (.inr p)))) = p.2.val.positive := by
  change (!(half (tally (Encoding.literalCode p.2.val+1))).2) = _
  rw [half_v,tally_length]
  cases b : p.2.val.positive <;> simp [parity,Encoding.literalCode,b,Nat.add_mod]

def halfAt (bits : End F → Bool) (v : Site F) : (network F).Half v :=
  (fun e _ => bits (.inl e),fun e _ => bits (.inr e))

/-- The cyclic equality checks use every incident endpoint. A self-loop
gives two independent inputs to the test. -/
private theorem uniform_slot (s : Slot F) (bits : End F → Bool) :
    (∃ b : Bool, ∀ e, host F e=.inl s → bits e=b) ↔ localOK F (.inl s) (halfAt F bits (.inl s)) := by
  constructor
  · rintro ⟨b,all⟩
    have same := all (.inl (.inl s)) rfl
    constructor
    · intro t h
      exact (all (.inr (.inl t)) (congrArg Sum.inl h.symm)).trans same.symm
    · intro p h
      exact (all (.inl (.inr p)) (congrArg Sum.inl h.symm)).trans same.symm
  · intro ok
    refine ⟨bits (.inl (.inl s)),?_⟩
    rintro ((t|p)|(t|p)) h
    · exact congrArg (fun t => bits (.inl (.inl t))) (Sum.inl.inj h)
    · exact ok.2 p (Sum.inl.inj h).symm
    · exact ok.1 t (Sum.inl.inj h).symm
    · contradiction

/-- A clause succeeds precisely when an incident input equals its polarity,
including the case of a clause with no literals. -/
private theorem satisfied_clause (c : ↥F) (bits : End F → Bool) :
    (∃ e, host F e=.inr c ∧ bits e=sign (encodeKey (endKey F e))) ↔
    localOK F (.inr c) (halfAt F bits (.inr c)) := by
  constructor
  · rintro ⟨((s|p)|(s|⟨cc,l⟩)),h,hit⟩ <;> try contradiction
    obtain rfl := Sum.inr.inj h
    exact ⟨l,hit.trans (sign_literal F _)⟩
  · rintro ⟨l,hit⟩
    exact ⟨.inr (.inr ⟨c,l⟩),rfl,hit.trans (sign_literal F ⟨c,l⟩).symm⟩

/-- The Boolean record test agrees with the formula tensor on the observed
endpoints. Only the membership of the rows matters. -/
theorem check_eq (v : Site F) (bits : End F → Bool) (rows : List Row)
    (listed : ∀ r, r∈rows ↔ ∃ e, host F e=v ∧ (bits e,sign (encodeKey (endKey F e)))=r) :
    check (left (encodeKey (siteKey F v)),rows) = true ↔ localOK F v (halfAt F bits v) := by
  cases v with
  | inl s =>
    change check (true,rows) = true ↔ _
    rw [check_slot,← uniform_slot]
    constructor
    · rintro ⟨b,all⟩
      exact ⟨b,fun e he => all _ ((listed _).mpr ⟨e,he,rfl⟩)⟩
    · rintro ⟨b,all⟩
      refine ⟨b,fun r hr => ?_⟩
      obtain ⟨e,he,rfl⟩ := (listed r).mp hr
      exact all e he
  | inr c =>
    change check (false,rows) = true ↔ _
    rw [check_clause,← satisfied_clause]
    constructor
    · rintro ⟨r,hr,eq⟩
      obtain ⟨e,he,rfl⟩ := (listed r).mp hr
      exact ⟨e,he,eq⟩
    · rintro ⟨e,he,eq⟩
      exact ⟨_,(listed _).mpr ⟨e,he,rfl⟩,eq⟩

end OAI.Computability.MultitapeWeakETH.CNFNetwork.SiteCheck
