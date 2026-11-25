import OAI.Optimization.LinearProgramming.OracleSpec.Compression
import Mathlib.Data.List.Lex
import Mathlib.Data.List.OfFn

/-! A computable ordering of minor requests from their public register encoding. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace MinorLog

/-- With its length supplied by `order`, each half of the serialized index can be recovered. -/
theorem squareWords_injective {r n : ℕ} (tag : ℕ) : Function.Injective (squareWords (r := r) (n := n) tag) := by
  rintro ⟨k, r₁, c₁, hr₁, hc₁⟩ ⟨l, r₂, c₂, hr₂, hc₂⟩ h
  simp only [squareWords, List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
  obtain ⟨hkl, h⟩ := h
  have hkey : k = l := Fin.ext hkl
  subst l
  obtain ⟨hr, hc⟩ := List.append_inj h (by simp)
  have hr' : r₁ = r₂ := funext fun i ↦ Fin.ext (congrFun (List.ofFn_injective hr) i)
  have hc' : c₁ = c₂ := funext fun i ↦ Fin.ext (congrFun (List.ofFn_injective hc) i)
  subst r₂; subst c₂; rfl

theorem words_injective {r s n : ℕ} : Function.Injective (words (d := r) (e := s) (n := n)) := by
  intro u v huv
  cases u with
  | inl u => cases v with
    | inl v => exact congrArg Sum.inl (squareWords_injective 0 huv)
    | inr v => simp [words, squareWords] at huv
  | inr u => cases v with
    | inl v => simp [words, squareWords] at huv
    | inr v => exact congrArg Sum.inr (squareWords_injective 1 huv)

/-- Compare a pair of indexed requests through the two short lists actually supplied. -/
@[instance_reducible] def requestWordOrder {r s n : ℕ} (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ) :
    LinearOrder (Index D E) :=
  LinearOrder.lift' (fun i : Index D E ↦ words i.val) (words_injective.comp Subtype.val_injective)

/-- Number of registers in the public request is exactly two plus two per selected index. -/
theorem squareWords_length {r n : ℕ} (tag : ℕ) (u : Square r n) :
    (squareWords tag u).length = 2 + 2*u.order.val := by simp [squareWords]; omega

/-- Each word is an ordinary dimension-bounded address, including the tag and order. -/
theorem word_bound {r s n : ℕ} (u : RawIndex r s n) {i : ℕ} (h : i ∈ words u) :
    i ≤ r+s+n+1 := by
  cases u with
  | inl u =>
    simp [words, squareWords, List.mem_ofFn] at h
    rcases h with h | h | ⟨j,h⟩ | ⟨j,h⟩
    · omega
    · have := u.order.isLt; omega
    · have := (u.rows j).isLt; omega
    · have := (u.cols j).isLt; omega
  | inr u =>
    simp [words, squareWords, List.mem_ofFn] at h
    rcases h with h | h | ⟨j,h⟩ | ⟨j,h⟩
    · omega
    · have := u.order.isLt; omega
    · have := (u.rows j).isLt; omega
    · have := (u.cols j).isLt; omega

end MinorLog
end OracleSpec
end LinearProgramming
end Optimization
end OAI
