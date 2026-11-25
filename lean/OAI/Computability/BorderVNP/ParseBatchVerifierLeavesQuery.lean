import OAI.Computability.BorderVNP.ParseBatchVerifierLeaves
import OAI.Computability.BorderVNP.ParseBatchBitsQuery

/-!
# Ordered parse choices after the physical leaf test

Successful decoding determines one word per row. Replacing the mathematical
multiset predicate by the compiled gate test thus preserves the parse bijection.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchLeaves

open VPVNP VPVNP.ParseGrammar BorderVNP.ParseRecords

variable {m g n b : ℕ}

/-- After the raw records are decoded, the circuit tests the leaf predicate on their
actual decoded list. -/
theorem frame_eval_of_readBlock (d : Fin n) (q : Fin m → Bool)
    (bs : Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool)
    {rs : List (GrammarLabel (Fin m × Bool) (Fin g) n)}
    (hread : readBlock m g n (List.ofFn bs) = some rs)
    (hm : m = d.val+1) (hcap : 2*d.val+1 ≤ 2^b) :
    (frame m g n (2*d.val+1) b).eval (Sum.elim q (fun ij => bs ij.1 ij.2)) () = true ↔
      Matches d (fun i => (i,q i)) rs := by
  have hc := readBlock_eq_some_iff.mp hread
  have hl : 2*d.val+1 = rs.length := by simpa using congrArg List.length hc
  let a (i : Fin (2*d.val+1)) := rs[i.val]'(hl ▸ i.isLt)
  have ha : List.ofFn a = rs := by
    apply List.ext_getElem
    · simpa using hl
    · intro j hj hk; simp only [List.getElem_ofFn, a]
  rw [← ha, List.map_ofFn] at hc
  have hraw : ∀ i, unpack m g n (fieldsOfBits (bs i)) = some (a i) := fun i =>
    unpack_bits_iff.mpr (congrFun (List.ofFn_injective hc) i)
  simpa only [ha, Sum.elim_inl] using frame_eval_of_unpacked d (Sum.elim q (fun ij => bs ij.1 ij.2))
    a hraw rfl hm hcap

/-- Valid raw guesses using the physical leaf check are counted once for each ordered
parse contributing the queried monomial. No sorting permutation is a witness. -/
noncomputable def queryEquiv (d : Fin n) (h : Fin g) (q : Fin m → Bool)
    (hm : m = d.val+1) (hcap : 2*d.val+1 ≤ 2^b) :
    ParseChoice (Fin g) d q ≃
      {bs : Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool //
        ∃ rs, readBlock m g n (List.ofFn bs) = some rs ∧ Valid d h rs ∧
          (frame m g n (2*d.val+1) b).eval (Sum.elim q (fun ij => bs ij.1 ij.2)) () = true} := by
  refine (queryBitsEquiv d h q).trans (Equiv.subtypeEquivRight fun bs => ?_)
  constructor
  · rintro ⟨rs, hd, hv, hm'⟩
    exact ⟨rs, hd, hv, (frame_eval_of_readBlock d q bs hd hm hcap).mpr hm'⟩
  · rintro ⟨rs, hd, hv, hf⟩
    exact ⟨rs, hd, hv, (frame_eval_of_readBlock d q bs hd hm hcap).mp hf⟩

end ParseBatchLeaves

end BorderVNP
end Computability
end OAI
