import OAI.Optimization.LinearProgramming.Compression.ServiceGeneratorTable
import Mathlib.Data.List.TakeDrop

/-! Lexicographic comparisons performed from the least significant index pair backwards.
Unused padded words are zero, so no index beyond the genuine minor order affects a result. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

variable {d e n : ℕ}

/-- Codes in the output address register are zero, one, and two. -/
def orderCode {α : Type*} [LinearOrder α] (x y : α) : ℕ := if x<y then 0 else if x=y then 1 else 2

/-- A preceding word supersedes the result from the suffix precisely when the words differ. -/
def prependCode (a b tail : ℕ) := if a<b then 0 else if b<a then 2 else tail

theorem orderCode_cons (a b : ℕ) (xs ys : List ℕ) :
    orderCode (a::xs) (b::ys) = prependCode a b (orderCode xs ys) := by
  rcases lt_trichotomy a b with h|h|h
  · simp [orderCode,prependCode,List.cons_lt_cons_iff,h]
  · subst b
    by_cases h : xs<ys <;> by_cases he : xs=ys <;> simp [orderCode,prependCode,h,he]
  · simp [orderCode,prependCode,List.cons_lt_cons_iff,h,not_lt_of_gt h,ne_of_gt h]

def pairWord (u : PairMinorIndex d e n) (i : ℕ) := Nat.pair (rowWord u i) (colWord u i)

def pairBody (u : PairMinorIndex d e n) := List.ofFn (fun i : Fin (order u) => pairWord u i.val)

@[simp] theorem pairBody_length (u : PairMinorIndex d e n) : (pairBody u).length = order u := by
  simp [pairBody]

theorem pairWord_pad (u : PairMinorIndex d e n) {i : ℕ} (h : order u ≤ i) : pairWord u i = 0 := by
  cases u with
  | inl u => simp [pairWord,rowWord,colWord,order] at h ⊢; simp [h.not_gt,Nat.pair]
  | inr u => simp [pairWord,rowWord,colWord,order] at h ⊢; simp [h.not_gt,Nat.pair]

/-- Reverse-scanning a valid position prepends the native paired word to the comparison. -/
theorem pairBody_drop_code (u v : PairMinorIndex d e n) (ho : order u=order v) (i : ℕ) :
    orderCode ((pairBody u).drop i) ((pairBody v).drop i) =
      prependCode (pairWord u i) (pairWord v i)
        (orderCode ((pairBody u).drop (i+1)) ((pairBody v).drop (i+1))) := by
  by_cases h : i<order u
  · have hu : i<(pairBody u).length := by simpa using h
    have hv : i<(pairBody v).length := by simpa [← ho] using h
    rw [List.drop_eq_getElem_cons hu,List.drop_eq_getElem_cons hv,orderCode_cons]
    simp [pairBody]
  · have hu : order u≤ i := Nat.le_of_not_gt h
    have hv : order v≤ i := ho ▸ hu
    simp [List.drop_eq_nil_of_le,hu,hv,hu.trans (Nat.le_succ _),hv.trans (Nat.le_succ _),
      pairWord_pad _ hu,pairWord_pad _ hv,prependCode]

/-- The two header words select the matrix and minor order before the sequence of paired positions. -/
theorem finishCode {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
    (y q : NonzeroPairMinor D E) (suffix : ℕ)
    (h : order y.val = order q.val → suffix=orderCode (pairBody y.val) (pairBody q.val)) :
    prependCode (tag y.val) (tag q.val) (prependCode (order y.val) (order q.val) suffix) =
      orderCode y q := by
  have hcode : orderCode y q = orderCode (pairMinorKey y.val) (pairMinorKey q.val) := by
    have he : pairMinorKey y.val = pairMinorKey q.val ↔ y=q :=
      (pairMinorKey_injective.comp Subtype.val_injective).eq_iff
    have hl : y<q ↔ pairMinorKey y.val < pairMinorKey q.val := Iff.rfl
    by_cases hlt : y<q
    · simp [orderCode,hlt,hl.mp hlt]
    · by_cases heq : y=q
      · subst q; simp [orderCode]
      · simp [orderCode,hlt,mt hl.mpr hlt,heq,mt he.mp heq]
  rw [hcode,pairMinorKey_words,pairMinorKey_words,orderCode_cons,orderCode_cons]
  by_cases ho : order y.val = order q.val
  · rw [h ho]
    rfl
  · rcases lt_or_gt_of_ne ho with hl|hl <;> simp [prependCode,hl,not_lt_of_gt hl]

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
