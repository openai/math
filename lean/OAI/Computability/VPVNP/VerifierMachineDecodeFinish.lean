import OAI.Computability.VPVNP.VerifierMachineDecodeLanguage
import OAI.Computability.VPVNP.VerifierMachineDecodeCanonical

/-!
# Correctness of the completed row scan

The final endpoint has to agree with both the number of bits actually scanned and the outer
unary length. Together these checks identify exactly the canonical prefix of a valid machine.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace VerifierMachineDecode

open UniversalMachine

private theorem header_rows (len : ℕ) (p : Program) :
    header len p.extra ++ p.rows.flatMap rowBits = unary len ++ tableBits p := by
  by_cases h : p.extra = 0
  · have hrows : p.rows = [] := List.length_eq_zero_iff.mp (by simp [p.rows_length, h])
    simp [header, h, hrows, tableBits]
  · simp [header, h, tableBits_rows p h, List.append_assoc]

private theorem length_programPrefix (p : Program) :
    (programPrefix p).length = 2 * (tableBits p).length + 1 := by
  simp [programPrefix, unary]
  omega

/-- Finishing at the end of the announced table length is equivalent to successful decoding
of a program satisfying the requested wire. -/
theorem finished_iff {n : ℕ} (x : Fin n → Bool) (q : DecoderWire n) :
    (∃ len extra : Fin (n + 1), queryAllowed q extra ∧ ∃ pos : Fin (n + 1),
      pos.val = 2 * len.val + 1 ∧ Reach (List.ofFn x) q len extra (9 * n) pos) ↔
      ∃ p, decode (List.ofFn x) = some p ∧ wireHolds p q := by
  constructor
  · rintro ⟨len, extra, hq, pos, hend, rows, hcount, hkeep, hpos, hmatch⟩
    have he : extra.val ≤ n := Nat.lt_succ_iff.mp extra.isLt
    have hr : rows.length = extra.val * 9 := by
      rw [hcount, min_eq_right (Nat.mul_le_mul_left 9 he), Nat.mul_comm]
    let p : Program := ⟨extra.val, rows, hr⟩
    have hword : header len extra ++ rows.flatMap rowBits = unary len ++ tableBits p :=
      header_rows len p
    rw [hword, List.length_append] at hpos
    have hul : (unary len).length = len.val + 1 := by simp [unary]
    have hlen : len.val = (tableBits p).length := by omega
    rw [hword, hlen] at hmatch
    obtain ⟨_, payload, hp⟩ := (matchAt_iff_drop _ _ _).mp hmatch
    exact ⟨p, decode_eq_some_iff.mpr ⟨payload, by simpa [programPrefix] using hp⟩,
      (query_iff q p).mpr ⟨hq, hkeep⟩⟩
  · rintro ⟨p, hd, hq⟩
    obtain ⟨payload, hinput⟩ := decode_eq_some_iff.mp hd
    have hprefix : (programPrefix p).length ≤ n := by
      have h := congrArg List.length hinput
      simp only [List.length_ofFn, List.length_append] at h
      omega
    have hbits : (tableBits p).length ≤ n := by rw [length_programPrefix] at hprefix; omega
    have he : p.extra ≤ n := by simpa using decoded_extra_le_length hd
    obtain ⟨hallowed, hkeep⟩ := (query_iff q p).mp hq
    refine ⟨⟨_, Nat.lt_succ_of_le hbits⟩, ⟨_, Nat.lt_succ_of_le he⟩, hallowed,
      ⟨_, Nat.lt_succ_of_le hprefix⟩, length_programPrefix p, p.rows, ?_, hkeep, ?_, ?_⟩
    · rw [p.rows_length, min_eq_right (Nat.mul_le_mul_left 9 he), Nat.mul_comm]
    · rw [header_rows]
      rfl
    · rw [header_rows]
      exact ⟨[], payload, hinput, rfl⟩

end VerifierMachineDecode

end VPVNP
end Computability
end OAI
