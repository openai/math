import OAI.Computability.BorderVNP.ParseBatchRecordsDecode
import OAI.Computability.BorderVNP.ParseBatchRecordsValid
import Mathlib.Data.Multiset.Sort

/-! # Comparing padded query records and counting each ordered parse once -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP VPVNP.ParseGrammar

variable {V H : Type*} {n m : ℕ}

/-- The list of records emits one key per slot, with a single dummy key for every
internal node. -/
def keys (rs : List (GrammarLabel V H n)) : Multiset (Option V) :=
  (rs.map terminal : List (Option V))

/-- The preorder encoding produces exactly one dummy for each internal node and the
multiset of the actual terminal variables with all repetitions. -/
theorem keys_encode (d : Fin n) (h : H) (p : OrderedParse V H d.val) :
    keys (encode d h p) =
      Multiset.replicate d.val none + (p.leaves : Multiset V).map some := by
  induction d using (measure (fun d : Fin n => d.val)).wf.induction generalizing h with
  | h d ih =>
    obtain ⟨k, hk⟩ := d
    cases k with
    | zero => cases p; rw [encode]; rfl
    | succ k =>
      cases p with
      | node b i j l r =>
        let d : Fin n := ⟨k+1,hk⟩
        let L := encode (leftDegree d b) i l
        let R := encode (rightDegree d b) j r
        rw [encode]
        simp only [keys, List.map_cons, List.map_append, terminal, OrderedParse.leaves]
        change none ::ₘ (keys L + keys R) =
          Multiset.replicate (k+1) none + ((l.leaves : Multiset V) + r.leaves).map some
        have hl := ih _ (leftDegree_lt d b) i l
        have hr := ih _ (rightDegree_lt d b) j r
        change keys L = Multiset.replicate b.val none + _ at hl
        change keys R = Multiset.replicate (k-b.val) none + _ at hr
        have split : b.val + (k-b.val) = k := by have := b.isLt; omega
        have hrep : Multiset.replicate k (none : Option V) =
            Multiset.replicate b.val none + Multiset.replicate (k-b.val) none :=
          (congrArg (fun z => Multiset.replicate z none) split.symm).trans
            (Multiset.replicate_add ..)
        rw [hl, hr, Multiset.replicate_succ, Multiset.cons_add, Multiset.map_add, hrep]
        congr 1
        ac_rfl

/-- Padded comparison against the requested variables. Both sides contain one key for
each of the `2m−1` slots when the query has the prescribed degree. -/
def Matches (d : Fin n) (q : Fin m → V) (rs : List (GrammarLabel V H n)) : Prop :=
  keys rs = Multiset.replicate d.val none + (List.ofFn q : Multiset V).map some

/-- The comparison can be implemented by sorting both key blocks and testing equality. -/
theorem matches_iff_sorted [LinearOrder (Option V)] (d : Fin n) (q : Fin m → V)
    (rs : List (GrammarLabel V H n)) :
    Matches d q rs ↔ (keys rs).sort (· ≤ ·) =
      (Multiset.replicate d.val none + (List.ofFn q : Multiset V).map some).sort (· ≤ ·) := by
  constructor
  · exact congrArg (fun s : Multiset (Option V) => s.sort (· ≤ ·))
  · intro he
    have := congrArg (fun xs : List (Option V) => (xs : Multiset (Option V))) he
    simpa only [Matches, Multiset.sort_eq] using this

/-- For an encoded tree the padded-key comparison is exactly the leaf assignment
condition of the coefficient query. -/
theorem matches_encode_iff (d : Fin n) (h : H) (p : OrderedParse V H d.val) (q : Fin m → V) :
    Matches d q (encode d h p) ↔ Nonempty (LeafBijection p.leaves q) := by
  rw [Matches, keys_encode, add_right_inj, LeafBijection.nonempty_iff]
  exact (Multiset.map_injective (Option.some_injective _)).eq_iff

/-- Ordered parse choices for a paired variable query are in bijection with the accepted
preorder blocks. Equality of variables includes the queried position, making the assignment
of the leaves to positions unique. -/
noncomputable def queryEquiv (d : Fin n) (h : H) (x : Fin m → Bool) :
    ParseChoice H d x ≃ {rs : List (GrammarLabel (Fin m × Bool) H n) //
      Valid d h rs ∧ Matches d (fun i => (i, x i)) rs} := by
  classical
  let f := fun a : ParseChoice H d x =>
    (⟨encode d h a.1, encode_valid d h a.1,
      (matches_encode_iff ..).mpr ⟨a.2⟩⟩ :
      {rs : List (GrammarLabel (Fin m × Bool) H n) //
        Valid d h rs ∧ Matches d (fun i => (i, x i)) rs})
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨p, bp⟩ ⟨q, bq⟩ he
    have hpq := encode_injective d h (congrArg Subtype.val he)
    change p = q at hpq
    subst q
    have := LeafBijection.subsingleton_of_injective p.leaves (q := fun i => (i, x i))
      fun _ _ he => congrArg Prod.fst he
    rw [Subsingleton.elim bp bq]
  · rintro ⟨rs, hvalid, hmatch⟩
    obtain ⟨p, rfl, _⟩ := existsUnique_encode_of_valid hvalid
    obtain ⟨b⟩ := (matches_encode_iff ..).mp hmatch
    exact ⟨⟨p, b⟩, rfl⟩

/-- The bijection sends each counted parse to its actual preorder records. -/
theorem queryEquiv_apply (d : Fin n) (h : H) (x : Fin m → Bool) (p : ParseChoice H d x) :
    (queryEquiv d h x p).val = encode d h p.1 := rfl

end ParseRecords

end BorderVNP
end Computability
end OAI
