import OAI.Computability.BorderVNP.ParseBatchRecords

/-! # Unique decoding of a locally checked preorder certificate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP VPVNP.ParseGrammar

variable {V H : Type*} {n : ℕ}

/-- Preorder records determine the tree: the split fixes the exact length of each child block. -/
theorem encode_injective (d : Fin n) (h : H) : Function.Injective (encode (V := V) d h) := by
  induction d using (measure (fun d : Fin n => d.val)).wf.induction generalizing h with
  | h d ih =>
    obtain ⟨k, hk⟩ := d
    cases k with
    | zero =>
      intro p q e
      cases p with
      | leaf v =>
        cases q with
        | leaf w =>
          rw [encode, encode] at e
          simpa using e
    | succ k =>
      intro p q e
      cases p with
      | node b i j l r =>
        cases q with
        | node b' i' j' l' r' =>
          rw [encode, encode] at e
          obtain ⟨he, ht⟩ := List.cons.inj e
          have es : (i, b, j) = (i', b', j') := by
            have hp := eq_of_heq (Sigma.mk.inj (Sum.inr.inj he)).2
            simpa using congrArg (fun x => (x.2.2.1, x.2.1, x.2.2.2)) hp
          obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj es |>.imp_right Prod.mk.inj
          let d : Fin n := ⟨k+1,hk⟩
          obtain ⟨hl, hr⟩ := List.append_inj ht
            ((encode_length (leftDegree d b) i l).trans (encode_length (leftDegree d b) i l').symm)
          have el := ih _ (leftDegree_lt ⟨k+1,hk⟩ b) i hl
          have er := ih _ (rightDegree_lt ⟨k+1,hk⟩ b) j hr
          cases el
          cases er
          rfl

private theorem decode_at (rs : List (GrammarLabel V H n))
    (loc : ∀ u r, rs[u]? = some r → Local rs u r) (d : Fin n) (h : H) (u : ℕ)
    (root : RootAt rs u d.val h) :
    ∃ p : OrderedParse V H d.val, ∀ t < (encode d h p).length,
      rs[u+t]? = (encode d h p)[t]? := by
  induction d using (measure (fun d : Fin n => d.val)).wf.induction generalizing h u with
  | h d ih =>
    obtain ⟨record, hread, hd, hs⟩ := root
    rcases record with ⟨a, v⟩ | ⟨e, a, b, i, j⟩
    · obtain ⟨k,hk⟩ := d
      change 0 = k at hd
      subst k
      change a = h at hs
      subst a
      refine ⟨.leaf v, ?_⟩
      rw [encode]
      intro t ht
      have : t = 0 := by simpa using ht
      subst t
      simpa using hread
    · have de : e = d := Fin.ext hd
      subst e
      change a = h at hs
      subst a
      obtain ⟨k, hk⟩ := d
      cases k with
      | zero => exact Fin.elim0 b
      | succ k =>
        let d : Fin n := ⟨k+1,hk⟩
        have check := loc _ _ hread
        obtain ⟨l, hl⟩ := ih _ (leftDegree_lt d b) i (u+1) check.2.1
        obtain ⟨r, hr⟩ := ih _ (rightDegree_lt d b) j (u+2*(b.val+1)) check.2.2
        refine ⟨.node b i j l r, ?_⟩
        rw [encode.eq_2 h k hk b i j l r]
        let L := encode (leftDegree d b) i l
        let R := encode (rightDegree d b) j r
        let row : GrammarLabel V H n := .inr ⟨d, h, b, i, j⟩
        change ∀ t < (row :: (L ++ R)).length, rs[u+t]? = (row :: (L ++ R))[t]?
        have hL : L.length = 2*b.val+1 := encode_length ..
        intro t ht
        cases t with
        | zero => simpa using hread
        | succ t =>
          rw [List.getElem?_cons_succ]
          by_cases small : t < L.length
          · rw [List.getElem?_append_left small, show u + (t+1) = (u+1) + t by omega]
            exact hl t small
          · rw [List.getElem?_append_right (Nat.le_of_not_gt small)]
            have bound : t-L.length < R.length := by
              simp only [List.length_cons, List.length_append] at ht
              omega
            rw [show u + (t+1) = (u + 2*(b.val+1)) + (t-L.length) by omega]
            exact hr _ bound

/-- A locally valid block encodes exactly one ordered parse of the prescribed layer and state. -/
theorem existsUnique_encode_of_valid {d : Fin n} {h : H} {rs : List (GrammarLabel V H n)}
    (valid : Valid d h rs) : ∃! p : OrderedParse V H d.val, encode d h p = rs := by
  obtain ⟨p, hp⟩ := decode_at rs valid.2.2 d h 0 valid.2.1
  have e : encode d h p = rs := by
    apply List.ext_getElem
    · exact (encode_length ..).trans valid.1.symm
    · intro i hi hi'
      have hi_eq := hp i hi
      simpa only [Nat.zero_add, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
        Option.some.injEq] using hi_eq.symm
  exact ⟨p, e, fun q hq => encode_injective d h (hq.trans e.symm)⟩

end ParseRecords

end BorderVNP
end Computability
end OAI
