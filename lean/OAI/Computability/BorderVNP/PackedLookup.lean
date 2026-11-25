import OAI.Computability.BorderVNP.PackedHistogramQueries

/-! # Deterministic batched reads from a shared table

Each table address has one source row. The zero-weight request rows follow it
after sorting, so a source payload is propagated to every matching request.
The final sort restores every request to its original ordinal.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistogram

open ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

/-- Hardwired big-endian encoding of a legal address. -/
noncomputable def fixed {σ : Type*} {k : ℕ} (a : Fin (2^k)) : Fin k → Expr σ :=
  fun j => .const ((numberWords k).symm a j)

@[simp] theorem fixed_value {σ : Type*} {k : ℕ} (x : σ → Bool) (a : Fin (2^k)) :
    wordValue x (fixed a) = a.val := value_encode a

end PackedHistogram

namespace PackedLookup

open PackedHistogram ParseBatchSort VPVNP.VerifierNetwork

variable {U Q P σ : Type*} [Fintype U] [Fintype Q] [Fintype P] [Fintype σ] {b k w : ℕ}

/-- Hardwire each table row's unique address and read an arbitrary sparse batch of query words. -/
noncomputable def lookup (e : Fin (2^b) ≃ Rows U Q P) (index : U ↪ Fin (2^k))
    (table : U → Fin w → Expr σ) (requests : Q → Fin k → Expr σ) : Frame σ (Q × Fin w) :=
  queries e (fun u => fixed (index u)) table requests

omit [Fintype Q] [Fintype P] [Fintype σ] in
private theorem singleton_sum (index : U ↪ Fin (2^k)) (table : U → Fin w → Expr σ)
    (x : σ → Bool) (u : U) :
    (∑ l, if (index l).val = (index u).val then wordValue x (table l) else 0) = wordValue x (table u) := by
  classical
  simp [Fin.val_inj, index.injective.eq_iff]

/-- A valid read returns the addressed table word exactly, independently of all other reads. -/
theorem lookup_value (e : Fin (2^b) ≃ Rows U Q P) (index : U ↪ Fin (2^k))
    (table : U → Fin w → Expr σ) (requests : Q → Fin k → Expr σ) (x : σ → Bool)
    (q : Q) (u : U) (address : wordValue x (requests q) = (index u).val) :
    value (fun j => (lookup e index table requests).eval x (q,j)) = wordValue x (table u) := by
  have fits (a : ℕ) : (∑ l, if wordValue x (fixed (index l)) = a then wordValue x (table l) else 0) < 2^w := by
    simp only [fixed_value]
    by_cases h : ∃ v, (index v).val = a
    · obtain ⟨v,rfl⟩ := h
      rw [singleton_sum]
      exact value_lt _
    · have hn (v) : (index v).val ≠ a := fun he => h ⟨v,he⟩
      simp [hn]
  rw [lookup, queries_value _ _ _ _ _ fits]
  simp only [fixed_value, address]
  exact singleton_sum index table x u

/-- The complete Boolean payload is recovered bitwise, including leading zeroes. -/
theorem lookup_bits (e : Fin (2^b) ≃ Rows U Q P) (index : U ↪ Fin (2^k))
    (table : U → Fin w → Expr σ) (requests : Q → Fin k → Expr σ) (x : σ → Bool)
    (q : Q) (u : U) (address : wordValue x (requests q) = (index u).val) (j : Fin w) :
    (lookup e index table requests).eval x (q,j) = (table u j).eval x :=
  congrFun (value_injective w (lookup_value e index table requests x q u address)) j

end PackedLookup

end BorderVNP
end Computability
end OAI
