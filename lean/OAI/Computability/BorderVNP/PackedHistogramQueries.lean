import OAI.Computability.BorderVNP.PackedHistogram

/-! # Padded layout for arbitrary source rows and sparse query ordinals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistogram

open ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {U Q P σ : Type*} {b k w : ℕ}

/-- Physical lanes are source rows, query rows, and zero-weight padding. -/
abbrev Rows (U Q P : Type*) := U ⊕ (Q ⊕ P)

/-- Canonical padding to the first power of two accommodating both batches. -/
noncomputable def layout (U Q : Type*) [Fintype U] [Fintype Q] :
    let n := Fintype.card U + Fintype.card Q
    let b := Nat.clog 2 n
    Fin (2^b) ≃ Rows U Q (Fin (2^b-n)) := by
  dsimp only
  apply Fintype.equivOfCardEq
  simp only [Rows, Fintype.card_sum, Fintype.card_fin]
  have := Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card U + Fintype.card Q)
  omega

/-- Above zero rows the padded size is strictly less than twice the source plus query count. -/
theorem layout_size (U Q : Type*) [Fintype U] [Fintype Q] (h : 0 < Fintype.card U + Fintype.card Q) :
    2^(Nat.clog 2 (Fintype.card U + Fintype.card Q)) < 2*(Fintype.card U + Fintype.card Q) :=
  TeamSorting.padding_lt_twice h

/-- Raw row formulas for the two sorts. Source and query tags are hardwired. -/
def encode (e : Fin (2^b) ≃ Rows U Q P) (ks : U → Fin k → Expr σ) (vs : U → Fin w → Expr σ)
    (qs : Q → Fin k → Expr σ) (p : Raw b k w) : Expr σ :=
  match e p.1, p.2 with
  | .inl u, .inl j => ks u j
  | .inl u, .inr (.inr j) => vs u j
  | .inr (.inl q), .inl j => qs q j
  | .inr (.inl _), .inr (.inl _) => .const true
  | _, _ => .const false

/-- The bits fed into the raw sort-and-scan network. -/
def assignment (e : Fin (2^b) ≃ Rows U Q P) (ks : U → Fin k → Expr σ) (vs : U → Fin w → Expr σ)
    (qs : Q → Fin k → Expr σ) (x : σ → Bool) (p : Raw b k w) : Bool :=
  (encode e ks vs qs p).eval x

private theorem zeroValue : ∀ w, value (fun _ : Fin w => false) = 0
  | 0 => rfl
  | w+1 => by simp [value, zeroValue w]

private theorem key_source (e : Fin (2^b) ≃ Rows U Q P) (ks : U → Fin k → Expr σ)
    (vs : U → Fin w → Expr σ) (qs : Q → Fin k → Expr σ) (x : σ → Bool) (u : U) :
    keyValue (assignment e ks vs qs x) (e.symm (.inl u)) = wordValue x (ks u) := by
  simp [keyValue, assignment, encode, wordValue]

private theorem key_query (e : Fin (2^b) ≃ Rows U Q P) (ks : U → Fin k → Expr σ)
    (vs : U → Fin w → Expr σ) (qs : Q → Fin k → Expr σ) (x : σ → Bool) (q : Q) :
    keyValue (assignment e ks vs qs x) (e.symm (.inr (.inl q))) = wordValue x (qs q) := by
  simp [keyValue, assignment, encode, wordValue]

private theorem value_source (e : Fin (2^b) ≃ Rows U Q P) (ks : U → Fin k → Expr σ)
    (vs : U → Fin w → Expr σ) (qs : Q → Fin k → Expr σ) (x : σ → Bool) (u : U) :
    weightValue (assignment e ks vs qs x) (e.symm (.inl u)) = wordValue x (vs u) := by
  simp [weightValue, assignment, encode, wordValue]

private theorem value_other (e : Fin (2^b) ≃ Rows U Q P) (ks : U → Fin k → Expr σ)
    (vs : U → Fin w → Expr σ) (qs : Q → Fin k → Expr σ) (x : σ → Bool) (o : Q ⊕ P) :
    weightValue (assignment e ks vs qs x) (e.symm (.inr o)) = 0 := by
  cases o <;> simp [weightValue, assignment, encode, StatementCircuit.Expr.eval, zeroValue]

variable [Fintype U] [Fintype Q] [Fintype P]

private theorem assignment_bucket (e : Fin (2^b) ≃ Rows U Q P) (ks : U → Fin k → Expr σ)
    (vs : U → Fin w → Expr σ) (qs : Q → Fin k → Expr σ) (x : σ → Bool) (a : ℕ) :
    bucket (keyValue (assignment e ks vs qs x)) (weightValue (assignment e ks vs qs x)) a =
      ∑ u, if wordValue x (ks u) = a then wordValue x (vs u) else 0 := by
  classical
  unfold bucket
  rw [← e.symm.sum_comp (fun i => if keyValue (assignment e ks vs qs x) i = a then
    weightValue (assignment e ks vs qs x) i else 0), Fintype.sum_sum_type]
  simp [key_source, value_source, value_other]

variable [Fintype σ]

/-- Batch weighted bucket queries from arbitrary field formulas. Substitution can feed the pins
from an earlier shared circuit. -/
noncomputable def queries (e : Fin (2^b) ≃ Rows U Q P) (ks : U → Fin k → Expr σ)
    (vs : U → Fin w → Expr σ) (qs : Q → Fin k → Expr σ) : Frame σ (Q × Fin w) :=
  ((frame b k w).subst ((Frame.initial id).step (encode e ks vs qs))).select
    fun qj => (e.symm (.inr (.inl qj.1)),qj.2)

/-- Every request reads exactly the sum of source rows at its key. -/
theorem queries_value (e : Fin (2^b) ≃ Rows U Q P) (ks : U → Fin k → Expr σ)
    (vs : U → Fin w → Expr σ) (qs : Q → Fin k → Expr σ) (x : σ → Bool)
    (fits : ∀ a, (∑ u, if wordValue x (ks u) = a then wordValue x (vs u) else 0) < 2^w) (q : Q) :
    value (fun j => (queries e ks vs qs).eval x (q,j)) =
      ∑ u, if wordValue x (ks u) = wordValue x (qs q) then wordValue x (vs u) else 0 := by
  let z := assignment e ks vs qs x
  have he : ((Frame.initial id).step (encode e ks vs qs)).eval x = z := by
    have hid : (Frame.initial (id : σ → σ)).eval x = x := funext fun i => Frame.initial_eval id x i
    funext p
    simp [z, assignment, hid]
  have hq : isQuery z (e.symm (.inr (.inl q))) = true := by simp [z, isQuery, assignment, encode, StatementCircuit.Expr.eval]
  have hz (l) (hl : isQuery z l = true) : weightValue z l = 0 := by
    obtain ⟨o,rfl⟩ := e.symm.surjective l
    rcases o with u | v
    · simp [z, isQuery, assignment, encode, StatementCircuit.Expr.eval] at hl
    · exact value_other _ _ _ _ _ v
  have hf a : bucket (keyValue z) (weightValue z) a < 2^w := (assignment_bucket _ _ _ _ _ _).trans_lt (fits a)
  simp only [queries, Frame.select_eval, Frame.subst_eval, he]
  rw [frame_value z hz hf _ hq, assignment_bucket, key_query]

omit [Fintype U] [Fintype P] in
/-- Charging at most D gates per raw address or payload bit preserves the near-linear gate count. -/
theorem queries_size (e : Fin (2^b) ≃ Rows U Q P) (ks : U → Fin k → Expr σ)
    (vs : U → Fin w → Expr σ) (qs : Q → Fin k → Expr σ) (D : ℕ) (hD : 1 ≤ D)
    (hk : ∀ u j, (ks u j).size ≤ D) (hv : ∀ u j, (vs u j).size ≤ D)
    (hq : ∀ q j, (qs q j).size ≤ D) :
    (queries e ks vs qs).size ≤ 2^b * ((k+1+w)*D + ((w+b)+1+k) +
      b^2*(24*((w+b)+1+k)+1) + w*(60*k+16*w+33) + b^2*(24*(w+b)+1)) := by
  have hb (p : Raw b k w) : (encode e ks vs qs p).size ≤ D := by
    rcases he : e p.1 with u | q | pad <;> rcases hp : p.2 with i | tag | j <;>
      simp [encode, he, hp, StatementCircuit.Expr.size, hD, hk, hv, hq]
  have hs := Frame.step_size_le (Frame.initial (id : σ → σ)) (encode e ks vs qs) D hb
  simp only [Raw, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit,
    Frame.initial_size, zero_add] at hs
  simp only [queries, Frame.select_size, Frame.subst_size]
  exact (Nat.add_le_add hs (frame_size b k w)).trans (by ring_nf; rfl)

end PackedHistogram

end BorderVNP
end Computability
end OAI
