import OAI.Combinatorics.Sunflower.Basic
import OAI.Combinatorics.Sunflower.Binary

/-! # Transporting an arbitrary finite alphabet to binary words -/

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {I α β : Type*}

/-- Relabel all coordinates of a word by the same alphabet embedding. -/
def wordEmbedding (e : α ↪ β) : (I → α) ↪ (I → β) where
  toFun w c := e (w c)
  inj' _ _ h := funext fun c => e.injective (congrFun h c)

theorem admissible_relabel_iff {ι : Type*} (e : α ↪ β) {f : ι → α} :
    Admissible (fun i => e (f i)) ↔ Admissible f := by
  constructor
  · rintro (h | h)
    · exact Or.inl fun i j => e.injective (h i j)
    · exact Or.inr fun _ _ he => h (congrArg e he)
  · rintro (h | h)
    · exact Or.inl fun i j => congrArg e (h i j)
    · exact Or.inr (e.injective.comp h)

theorem wordFree_map_iff {r : ℕ} (e : α ↪ β) (W : Finset (I → α)) :
    WordFree r (W.map (wordEmbedding e)) ↔ WordFree r W := by
  constructor
  · intro h w hw hadm i j
    apply (wordEmbedding e).injective
    apply h (fun t => wordEmbedding e (w t))
    · exact fun t => Finset.mem_map.mpr ⟨_, hw t, rfl⟩
    · exact fun c => (admissible_relabel_iff e).mpr (hadm c)
  · intro h w hw hadm i j
    choose v hv heq using fun t => Finset.mem_map.mp (hw t)
    have hword : WordAdmissible v := by
      intro c
      apply (admissible_relabel_iff e).mp
      change Admissible (fun i => wordEmbedding e (v i) c)
      simpa only [heq] using hadm c
    rw [← heq i, ← heq j, h v hv hword i j]

/-- A one-hot encoding into `n` bits works for every cardinal, including zero. -/
def Binary.alphabetEmbedding (n : ℕ) : Fin n ↪ Binary.Word n where
  toFun x i := if x = i then 1 else 0
  inj' x y h := by
    by_contra hne
    exact hne (show y = x by simpa using congrFun h x).symm

/-- Passing to a binary-word alphabet preserves both the cardinality and sunflower-freeness. -/
theorem exists_binary_word_family {r n : ℕ} {W : Finset (I → Fin n)} (h : WordFree r W) :
    ∃ B : Finset (I → Binary.Word n), B.card = W.card ∧ WordFree r B :=
  ⟨_, Finset.card_map _, (wordFree_map_iff (Binary.alphabetEmbedding n) W).mpr h⟩

end Sunflower
end Combinatorics
end OAI
