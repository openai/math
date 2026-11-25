import OAI.Computability.NearSquareRoot.CommonAlphabetSweep

/-! # Reading a fixed-width code block

Each physical transition reads one cell on every tape, stores that column in
the finite control, and moves right. After exactly one block, decoding the
buffer supplies all symbols under the source heads. The entire sweep leaves
the tape contents unchanged.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet
open IntegerMultiplication
variable {A Q I : Type} (c : Code A)

/-- Contents of the finite buffer after reading the first `k` columns. -/
private def bufferAt (T : I → TM.Tape A) (k : ℕ) : I → Letters c.width :=
  fun i d => if d.val < k then c.enc ((T i).view 0) d else none

private theorem stash_bufferAt (T : I → TM.Tape A) (j : Fin c.width) (bits : I → Option Bool)
    (h : ∀ i, bits i = c.enc ((T i).view 0) j) :
    stash (bufferAt c T j.val) j bits = bufferAt c T (j.val+1) := by
  funext i d
  by_cases hd : d = j
  · subst d
    simp [stash, bufferAt, h]
  · have hval : d.val ≠ j.val := fun hh => hd (Fin.ext hh)
    have he : d.val < j.val + 1 ↔ d.val < j.val := by omega
    simp [stash, bufferAt, Function.update_of_ne hd, he]

private theorem decode_full (T : I → TM.Tape A) :
    (fun i => c.dec (bufferAt c T c.width i)) = fun i => (T i).view 0 := by
  funext i
  have hf : bufferAt c T c.width i = c.enc ((T i).view 0) := by
    funext d
    simp [bufferAt, d.isLt]
  rw [hf, c.decode_encode]

/-- Read the aligned source symbols in exactly one block of physical steps. -/
theorem readSweep (m : TM.Rule A Q I) (q : Q)
    (S : I → TM.Tape (Option Bool)) (T : I → TM.Tape A) (h : ∀ i, Represents c (S i) (T i)) :
    ∃ U, Trace (TM.advance (rule c m)) ⟨readStart c q,S⟩ c.width
        ⟨.rewind q (fun i => (T i).view 0) (first c),U⟩ ∧
      (∀ i, SameCells c (U i) (T i)) ∧
      (∀ i, (U i).pos = (T i).pos * c.width + c.width) ∧
      (∀ i, (U i).absolute = (S i).absolute) := by
  let stage (j : Fin c.width) : PC A Q I c.width := .readBlock q (bufferAt c T j.val) j
  let done : PC A Q I c.width := .rewind q (fun i => (T i).view 0) (first c)
  let Inv (j : ℕ) (U : I → TM.Tape (Option Bool)) :=
    (∀ i, (U i).pos = (T i).pos * c.width + j) ∧ (∀ i, (U i).absolute = (S i).absolute)
  have init : Inv 0 S := ⟨fun i => by simpa using (h i).1, fun _ => rfl⟩
  have step (j : Fin c.width) (U) (hj : Inv j.val U) :
      ∃ U', TM.advance (rule c m) ⟨stage j,U⟩ =
        some ⟨atIndex c.width stage done (j.val+1),U'⟩ ∧ Inv (j.val+1) U' := by
    let rd (i : I) := (U i).view 0
    let U' (i : I) := (U i).apply (rd i, .right)
    have read (i : I) : rd i = c.enc ((T i).view 0) j := by
      change (U i).view 0 = _
      rw [← tape_read (U i), hj.1 i, hj.2 i, (h i).2 (T i).pos j, tape_read]
    have buf := stash_bufferAt c T j rd read
    have targets :
        atIndex c.width (.readBlock q (bufferAt c T (j.val+1)))
          (.rewind q (fun i => c.dec (bufferAt c T (j.val+1) i)) (first c)) (j.val+1) =
            atIndex c.width stage done (j.val+1) := by
      by_cases hn : j.val + 1 < c.width
      · simp [atIndex, stage, hn]
      · have hw : j.val + 1 = c.width := by have := j.isLt; omega
        simp [atIndex, hw, done, decode_full c T]
    refine ⟨U', ?_, ?_, ?_⟩
    · change some (TM.Config.mk
        (atIndex (R := PC A Q I c.width) c.width
          (.readBlock q (stash (bufferAt c T j.val) j rd))
          (.rewind q (fun i => c.dec (stash (bufferAt c T j.val) j rd i)) (first c))
          (j.val + 1)) U') = _
      rw [buf, targets]
    · intro i
      change (U i).pos + 1 = _
      rw [hj.1 i, Nat.cast_add_one, add_assoc]
    · intro i
      funext z
      exact (idleWrite (U i) .right z).trans (congrFun (hj.2 i) z)
  obtain ⟨U, run, hu⟩ := sweepAt c.pos (rule c m) stage done Inv S init step
  have hs : stage ⟨0,c.pos⟩ = readStart c q := by
    have e : bufferAt c T 0 = emptyBuffer (I := I) c := by funext i d; simp [bufferAt,emptyBuffer]
    simp [stage, readStart, first, e]
  refine ⟨U, hs ▸ run, ?_, hu.1, hu.2⟩
  intro i p d
  rw [hu.2 i]
  exact (h i).2 p d

end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
