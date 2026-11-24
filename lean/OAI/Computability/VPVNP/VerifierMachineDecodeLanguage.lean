import OAI.Computability.VPVNP.VerifierMachineDecodeRows
import OAI.Computability.VPVNP.VerifierMachineDecodeWire

/-!
# A dynamic program for reading the table

Fix the declared table length and the number of running states. After reading each row,
the parser marks the offsets at which the first rows could have ended. A requested slot
constrains just the indexed row. After the prescribed number of rows the marks stay fixed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace VerifierMachineDecode

open UniversalMachine

/-- Bits preceding the rows of a nonempty table, or the length field for an empty one. -/
def header (len extra : ℕ) : Word :=
  unary len ++ if extra = 0 then [] else unary (extra - 1)

theorem header_length (len extra : ℕ) : (header len extra).length = len + 1 + extra := by
  cases extra <;> simp [header, unary, Nat.add_assoc]
  omega

private theorem rowsKeep_snoc {n extra : ℕ} (q : DecoderWire n)
    (rows : List (Branches extra)) (b : Branches extra) :
    RowsKeep q (rows ++ [b]) ↔ RowsKeep q rows ∧ keepRow q rows.length b = true := by
  constructor
  · intro h
    refine ⟨?_, h rows.length b (by simp)⟩
    intro i b' hi
    exact h i b' (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1, hi])
  · rintro ⟨h, hlast⟩ i b' hi
    by_cases hlt : i < rows.length
    · exact h i b' (by rwa [List.getElem?_append_left hlt] at hi)
    · have hib := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_append, List.length_singleton] at hib
      have heq : i = rows.length := by omega
      subst i
      simp only [List.getElem?_concat_length, Option.some.injEq] at hi
      exact hi ▸ hlast

/-- Position reached by the first `min t (9*extra)` rows, when their bits agree with the input. -/
def Reach {n : ℕ} (input : Word) (q : DecoderWire n) (len extra t pos : ℕ) : Prop :=
  ∃ rows : List (Branches extra), rows.length = min t (9 * extra) ∧ RowsKeep q rows ∧
    pos = (header len extra ++ rows.flatMap rowBits).length ∧
    MatchAt input 0 (header len extra ++ rows.flatMap rowBits)

theorem Reach_zero {n : ℕ} {input : Word} (q : DecoderWire n) (len extra pos : ℕ) :
    Reach input q len extra 0 pos ↔
      pos = (header len extra).length ∧ MatchAt input 0 (header len extra) := by
  simp [Reach, RowsKeep]

theorem Reach_succ_of_le {n : ℕ} {input : Word} (q : DecoderWire n) (len extra t pos : ℕ)
    (h : 9 * extra ≤ t) :
    Reach input q len extra (t+1) pos ↔ Reach input q len extra t pos := by
  simp only [Reach, min_eq_right h, min_eq_right (Nat.le_succ_of_le h)]

theorem Reach_succ_of_lt {n : ℕ} {input : Word} (q : DecoderWire n) (len extra t pos : ℕ)
    (h : t < 9 * extra) :
    Reach input q len extra (t+1) pos ↔
      ∃ (b : Branches extra) (i : Fin (input.length+1)),
        keepRow q t b = true ∧ Reach input q len extra t i.val ∧
          i.val + (rowBits b).length = pos ∧ MatchAt input i.val (rowBits b) := by
  simp only [Reach, min_eq_left (Nat.succ_le_of_lt h), min_eq_left h.le]
  constructor
  · rintro ⟨allRows, hlen, hkeep, hpos, hword⟩
    obtain rfl | ⟨rows, b, rfl⟩ := List.eq_nil_or_concat' allRows
    · simp at hlen
    simp only [List.length_append, List.length_singleton] at hlen
    have hlen : rows.length = t := by omega
    obtain ⟨hrows, hb⟩ := (rowsKeep_snoc q rows b).mp hkeep
    let prefixWord := header len extra ++ rows.flatMap rowBits
    have he : header len extra ++ (rows ++ [b]).flatMap rowBits = prefixWord ++ rowBits b := by
      simp [prefixWord, List.flatMap_append, List.append_assoc]
    rw [he] at hpos hword
    obtain ⟨hp, hm⟩ := (matchAt_append_iff input 0 prefixWord (rowBits b)).mp hword
    have hbound := hp.end_le
    exact ⟨b, ⟨prefixWord.length, by omega⟩, hlen ▸ hb, ⟨rows, hlen, hrows, rfl, hp⟩,
      by simpa using hpos.symm, by simpa using hm⟩
  · rintro ⟨b, i, hb, ⟨rows, hlen, hrows, hi, hp⟩, hpos, hm⟩
    let prefixWord := header len extra ++ rows.flatMap rowBits
    have he : header len extra ++ (rows ++ [b]).flatMap rowBits = prefixWord ++ rowBits b := by
      simp [prefixWord, List.flatMap_append, List.append_assoc]
    refine ⟨rows ++ [b], by simp [hlen], (rowsKeep_snoc q rows b).mpr ⟨hrows, hlen ▸ hb⟩, ?_, ?_⟩
    · rw [he, List.length_append, ← hpos, hi]
    · apply (he ▸ (matchAt_append_iff input 0 prefixWord (rowBits b))).mpr
      exact ⟨hp, by simpa [hi, prefixWord] using hm⟩

end VerifierMachineDecode

end VPVNP
end Computability
end OAI
