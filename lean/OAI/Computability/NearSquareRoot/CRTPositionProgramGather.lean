import OAI.Computability.NearSquareRoot.CRTPositionProgramGates

/-! # Moving the two named chunk rows to the physical instruction positions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication.Code PositionPreparation

private def reindex {k : ℕ} (p : Equiv.Perm (Fin 3)) (w : Fin k → Bool) (x : Fin k) : Bool :=
  let e := threeChunksWithTail k
  match e x with
  | .inl (c,j) => w (e.symm (.inl (p c,j)))
  | .inr _ => w x

def swapWord {k : ℕ} (q : Fin 3 × Fin 3) (w : Fin k → Bool) := reindex (Equiv.swap q.1 q.2) w

@[simp] theorem swapWord_bulk {k : ℕ} (q : Fin 3 × Fin 3) (w : Fin k → Bool)
    (c : Fin 3) (i : Fin (k/3)) :
    swapWord q w ((threeChunksWithTail k).symm (.inl (c,i))) =
      w ((threeChunksWithTail k).symm (.inl (Equiv.swap q.1 q.2 c,i))) := by
  simp only [swapWord,reindex,Equiv.apply_symm_apply]

@[simp] theorem swapWord_tail {k : ℕ} (q : Fin 3 × Fin 3) (w : Fin k → Bool) (i : Fin (k%3)) :
    swapWord q w ((threeChunksWithTail k).symm (.inr i)) = w ((threeChunksWithTail k).symm (.inr i)) := by
  simp only [swapWord,reindex,Equiv.apply_symm_apply]

theorem swapWord_twice {k : ℕ} (q : Fin 3 × Fin 3) (w : Fin k → Bool) : swapWord q (swapWord q w) = w := by
  funext x
  obtain ⟨a,rfl⟩ := (threeChunksWithTail k).symm.surjective x
  rcases a with ⟨c,j⟩ | j <;> simp

/-- Put the source at the most significant chunk and the target in the middle. -/
def gather (s d : Fin 3) : List (Fin 3 × Fin 3) :=
  (if s = 2 then [] else [(s,2)]) ++
    (let d' := Equiv.swap s 2 d; if d' = 1 then [] else [(d',1)])

theorem gather_poly : Poly (fun q : Fin 3 × Fin 3 => gather q.1 q.2) := (Easy.finite _).poly

theorem gather_length (s d : Fin 3) : (gather s d).length ≤ 2 := by decide +revert

theorem gather_distinct (s d : Fin 3) (q : Fin 3 × Fin 3) (h : q ∈ gather s d) : q.1 ≠ q.2 := by
  decide +revert

private def layout : List (Fin 3 × Fin 3) → Equiv.Perm (Fin 3)
  | [] => Equiv.refl _
  | a :: t => (layout t).trans (Equiv.swap a.1 a.2)

private theorem reindex_trans {k : ℕ} (p q : Equiv.Perm (Fin 3)) (w : Fin k → Bool) :
    reindex p (reindex q w) = reindex (p.trans q) w := by
  funext x
  obtain ⟨v,rfl⟩ := (threeChunksWithTail k).symm.surjective x
  cases v with
  | inl cj => obtain ⟨c,j⟩ := cj; simp [reindex]
  | inr j => simp [reindex]

private theorem reindex_id {k : ℕ} (w : Fin k → Bool) : reindex (Equiv.refl _) w = w := by
  funext x
  obtain ⟨v,rfl⟩ := (threeChunksWithTail k).symm.surjective x
  cases v with
  | inl cj => obtain ⟨c,j⟩ := cj; simp [reindex]
  | inr j => simp [reindex]

private theorem swapFold {k : ℕ} (l : List (Fin 3 × Fin 3)) (w : Fin k → Bool) :
    l.foldl (fun z q => swapWord q z) w = reindex (layout l) w := by
  induction l generalizing w with
  | nil => exact (reindex_id w).symm
  | cons a t ih => exact (ih _).trans (reindex_trans ..)

private theorem reindex_chunk {k : ℕ} (p : Equiv.Perm (Fin 3)) (w : Fin k → Bool) (c : Fin 3) :
    chunkWord (reindex p w) c = chunkWord w (p c) := by
  funext i
  simp [chunkWord,reindex]

private theorem directed_reindex {k : ℕ} (p : Equiv.Perm (Fin 3)) (s d : Fin 3) (t : ReadTable)
    (w : Fin k → Bool) :
    directed (s,d,t) (reindex p w) = reindex p (directed (p s,p d,t) w) := by
  funext x
  obtain ⟨v,rfl⟩ := (threeChunksWithTail k).symm.surjective x
  cases v with
  | inl cj =>
    obtain ⟨c,j⟩ := cj
    by_cases h : c = d <;> simp [directed,reindex_chunk,reindex,h]
  | inr j => simp [directed,reindex]

theorem gather_correct {k : ℕ} (s d : Fin 3) (h : s ≠ d) (t : ReadTable) (w : Fin k → Bool) :
    (gather s d).reverse.foldl (fun z q => swapWord q z)
      (directed (2,1,t) ((gather s d).foldl (fun z q => swapWord q z) w)) = directed (s,d,t) w := by
  have fixed : layout (gather s d) 2 = s ∧ layout (gather s d) 1 = d := by decide +revert
  have eq : (layout (gather s d).reverse).trans (layout (gather s d)) = Equiv.refl _ := by
    ext c
    revert c
    decide +revert
  rw [swapFold,swapFold,directed_reindex,reindex_trans,eq,reindex_id,fixed.1,fixed.2]

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
