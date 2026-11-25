import OAI.Computability.VPVNP.ParseHistogram

/-!
# Preorder records for a coefficient query

The table requests of Lemma 2.3 serve directly as the node records. A terminal record
stores its state and variable, while a production record stores its layer, state, split
and two child states. The finite types check the ranges. The tagged alternatives carry
only the fields they use, so there is a unique representation for each record.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP VPVNP.ParseGrammar

variable {V H : Type*} {n : ℕ}

/-- The layer of a record is one less than its number of terminal descendants. -/
def depth : GrammarLabel V H n → ℕ
  | .inl _ => 0
  | .inr ⟨d, _⟩ => d.val

/-- The grammar state required at this node. -/
def state : GrammarLabel V H n → H
  | .inl (h, _) => h
  | .inr ⟨_, h, _⟩ => h

/-- A terminal contributes its query variable, and an internal production contributes none. -/
def terminal : GrammarLabel V H n → Option V
  | .inl (_, v) => some v
  | .inr _ => none

/-- Encode an ordered parse in preorder, retaining every table label exactly once. -/
def encode (d : Fin n) (h : H) (p : OrderedParse V H d.val) : List (GrammarLabel V H n) :=
  match d, p with
  | ⟨0, _⟩, .leaf v => [.inl (h, v)]
  | ⟨k+1, hk⟩, .node b i j l r =>
    .inr ⟨⟨k+1, hk⟩, h, b, i, j⟩ ::
      (encode (leftDegree ⟨k+1, hk⟩ b) i l ++ encode (rightDegree ⟨k+1, hk⟩ b) j r)
termination_by d.val
decreasing_by all_goals first | exact leftDegree_lt _ _ | exact rightDegree_lt _ _

/-- The layer-`k` block contains exactly `2k+1` records, including its root. -/
theorem encode_length (d : Fin n) (h : H) (p : OrderedParse V H d.val) :
    (encode d h p).length = 2*d.val+1 := by
  induction d using (measure (fun d : Fin n => d.val)).wf.induction generalizing h with
  | h d ih =>
    obtain ⟨k, hk⟩ := d
    cases k with
    | zero => cases p; rw [encode]; rfl
    | succ k =>
      cases p with
      | node b i j l r =>
        rw [encode, List.length_cons, List.length_append, ih _ (leftDegree_lt ⟨k+1,hk⟩ b) i l,
          ih _ (rightDegree_lt ⟨k+1,hk⟩ b) j r]
        dsimp [leftDegree, rightDegree]
        have := b.isLt
        omega

/-- The terminal fields in the block, read with their multiplicities, are the ordered
terminal word of the tree. -/
theorem encode_filterMap_terminal (d : Fin n) (h : H) (p : OrderedParse V H d.val) :
    (encode d h p).filterMap terminal = p.leaves := by
  induction d using (measure (fun d : Fin n => d.val)).wf.induction generalizing h with
  | h d ih =>
    obtain ⟨k, hk⟩ := d
    cases k with
    | zero => cases p; rw [encode]; rfl
    | succ k =>
      cases p with
      | node b i j l r =>
        rw [encode, List.filterMap_cons_none (by rfl), List.filterMap_append,
          ih _ (leftDegree_lt ⟨k+1,hk⟩ b) i l, ih _ (rightDegree_lt ⟨k+1,hk⟩ b) j r]
        rfl

/-- The parameter exponents are exactly the counts of the corresponding records. -/
theorem encode_histogram (d : Fin n) (h : H) (p : OrderedParse V H d.val) :
    ((encode d h p).map (fun r => Finsupp.single r 1)).sum = histogram d h p := by
  induction d using (measure (fun d : Fin n => d.val)).wf.induction generalizing h with
  | h d ih =>
    obtain ⟨k, hk⟩ := d
    cases k with
    | zero => cases p; rw [encode, histogram]; simp
    | succ k =>
      cases p with
      | node b i j l r =>
        rw [encode, histogram, List.map_cons, List.map_append, List.sum_cons, List.sum_append,
          ih _ (leftDegree_lt ⟨k+1,hk⟩ b) i l, ih _ (rightDegree_lt ⟨k+1,hk⟩ b) j r, add_assoc]

/-- A bounded-address read checks the layer and state of one record. -/
def RootAt (rs : List (GrammarLabel V H n)) (u k : ℕ) (h : H) : Prop :=
  ∃ r, rs[u]? = some r ∧ depth r = k ∧ state r = h

/-- A local check requires the entire declared interval to fit and the two child addresses
to carry their prescribed layer and state. A terminal has no child requests. -/
def Local (rs : List (GrammarLabel V H n)) (u : ℕ) (r : GrammarLabel V H n) : Prop :=
  u + 2*depth r < rs.length ∧ match r with
  | .inl _ => True
  | .inr ⟨d, _, b, i, j⟩ =>
      RootAt rs (u+1) b.val i ∧ RootAt rs (u+2*(b.val+1)) (d.val-1-b.val) j

/-- These simultaneous per-record checks constitute the preorder block verifier. -/
def Valid (d : Fin n) (h : H) (rs : List (GrammarLabel V H n)) : Prop :=
  rs.length = 2*d.val+1 ∧ RootAt rs 0 d.val h ∧ ∀ u r, rs[u]? = some r → Local rs u r

/-- The preorder block starts with the requested state and degree. -/
theorem encode_root (d : Fin n) (h : H) (p : OrderedParse V H d.val) :
    RootAt (encode d h p) 0 d.val h := by
  obtain ⟨k, hk⟩ := d
  cases k with
  | zero => cases p; rw [encode]; exact ⟨_, rfl, rfl, rfl⟩
  | succ k => cases p; rw [encode]; exact ⟨_, rfl, rfl, rfl⟩

end ParseRecords

end BorderVNP
end Computability
end OAI
