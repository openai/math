import OAI.Computability.NearSquareRoot.InterchangeRequestBody
import OAI.Computability.NearSquareRoot.InterchangePayloadBank
import OAI.Computability.NearSquareRoot.InterchangeBatchFrame

/-! # Recursive requests over the same packed alphabet at every level -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom NearSquareRoot.InterchangeFrame
  NearSquareRoot.InterchangePayloadBank

variable {I F : Type} {b : ℕ}

/-- A record contains exactly the declared number of symbols, in tape order. -/
def record (digit : F → Tree) (w : ℕ) (t : Tree) : Prop :=
  ∃ v : Fin w → F, t = stripe (Series.natural w) (digit ∘ v)

/-- The uniform domain of positive-width calls, before any padding threshold is chosen. -/
def Packed (digit : F → Tree) (a : Request b) : Prop :=
  Admissible a ∧ 0 < a.width ∧ ∀ k, record digit a.recordWidth (a.contents k)

theorem packed_manifest [Finite F] (digit : F → Tree) (xs : I → Request b)
    (hs : ∀ i, Packed digit (xs i)) :
    Manifest _ (fun i => (xs i).recordWidth) (fun i => (xs i).contents) := by
  obtain ⟨C,hC⟩ := (Set.finite_range (fun v : F => (digit v).count)).bddAbove
  refine ⟨C+2,fun i a => ?_⟩
  obtain ⟨v, eq⟩ := (hs i).2.2 a
  rw [eq]
  have z := stripe_size (Series.natural (xs i).recordWidth) (digit ∘ v) C
    (fun d => hC (Set.mem_range_self _))
  rw [Series.count_natural] at z
  nlinarith

/-- The precise fields needed for recursion follow from the generated
address request, including the representation of each transported record. -/
theorem packed_child (hb : 2 ≤ b) {P G B : Dims.Tape} {N w l : ℕ} (hw : 0 < w)
    (ht : ∀ d ∈ P ++ G ++ B, 2 ≤ d ∧ d ≤ b) (digit : F → Tree) (a : Request b)
    (h : ((a.width = w ∧ a.rows.count = N ∧ a.recordWidth = l) ∧
      ∀ k, record digit l (a.contents k)) ∧ inherited b P G B a) :
    (Packed digit a ∧ a.width = w ∧ a.recordWidth = l) ∧ a.rows.count = N := by
  obtain ⟨⟨⟨e,Nv,Lv⟩,data⟩,dims⟩ := h
  exact ⟨⟨⟨admissible_inherited hb ht dims,e.symm ▸ hw,Lv.symm ▸ data⟩,e,Lv⟩,Nv⟩

/-- Replacing the occupied leading digit by its batch quotient produces
another bounded-radix spectator and preserves the recursive dimension bounds. -/
theorem packed_dimensions (hb : 2 ≤ b) (W : ℕ) (hW : 0 < W) (hl : W < b)
    (a : Request b) (n : ℕ) (h : Admissible a) :
    ∀ d ∈ (a.before ++ [BatchRows.groups b W]) ++
      gap b 1 (tail n a.width) a.between ++ post b (tail n a.width) a.after_,
      2 ≤ d ∧ d ≤ b := by
  have ok := admissible_center 1 (tail n a.width) hb h
  have group := BatchFrame.groups_bounds hW hl
  intro d hd
  simp only [List.mem_append,List.mem_singleton] at hd
  rcases hd with ((hp|rfl)|hg)|hz
  · exact ok d (by simp [pre,hp])
  · exact group
  · exact ok d (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr (by simpa only [gap,List.mem_append] using hg)))))
  · exact ok d (by simp [hz])

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
