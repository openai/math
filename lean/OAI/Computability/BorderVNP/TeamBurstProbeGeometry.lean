import OAI.Computability.BorderVNP.TeamBurstProbeControl
import OAI.Computability.VPVNP.LiveHeaderBits

/-! # The consecutive memory and private-input fields of a team burst

The endpoint of the half-open interval may be exactly the word modulus. Every emitted
record still has its natural address and global tick. The wrap of the final cursor takes
place after the last probe. The bits delivered to the private machine are its actual input.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamBurstProbe

open VPVNP BurstRAM RAMSerialization
open TeamBurstProbeStep (next)
variable {w : ℕ}

/-- The low-bit-first physical private argument has the encoding read by the native call. -/
theorem bytes_eq_inputBits (vs : List (Word w)) : bytes vs = TeamPrivateCall.inputBits vs := by
  simp only [bytes, TeamPrivateCall.inputBits, LiveHeader.testBit_wordBits]
  rfl

/-- Physical address and tick counters advance modulo the full word range. -/
theorem advance_val (k : ℕ) (a : Word w) : (advance k a).val = (a.val+k) % 2^w := by
  induction k with
  | zero => exact (Nat.mod_eq_of_lt a.isLt).symm
  | succ k ih =>
    change ((advance k a).val+1) % 2^w = (a.val+(k+1)) % 2^w
    rw [ih,Nat.mod_add_mod, Nat.add_assoc]

/-- Before the endpoint every physical counter agrees with its natural offset. -/
theorem advance_val_of_lt (a : Word w) (k : ℕ) (h : a.val+k < 2^w) :
    (advance k a).val = a.val+k := (advance_val k a).trans (Nat.mod_eq_of_lt h)

/-- The logical four-field reads emitted by a burst with the indicated old-word choices. -/
def claimed (address tick : ℕ) : List (Word w) → List (TeamRecords.Record (Word w))
  | [] => []
  | v :: vs => ⟨address,tick,v,v⟩ :: claimed (address+1) (tick+1) vs

/-- The old words are exactly the free fields of the paper's consecutive read accesses. -/
theorem claimed_matches (a t : ℕ) (vs : List (Word w)) :
    TeamRecords.Matches (TeamRecords.readBurst a t vs.length) (claimed a t vs) := by
  induction vs generalizing a t with
  | nil => exact .nil
  | cons _ vs ih => exact .cons rfl (ih _ _)

/-- Decoding every physical slot yields precisely the canonical widened pair expansion
of the paper's read records, even when the last read is at the greatest word address. -/
theorem records_decode (a t : Word w) (vs : List (Word w))
    (ha : a.val+vs.length ≤ 2^w) (ht : t.val+vs.length ≤ 2^w) :
    (records a t vs).map WordRecord.record =
      ((claimed a.val t.val vs).map TeamProbeEmit.widenRecord).flatMap TeamRecords.pair := by
  induction vs generalizing a t with
  | nil => rfl
  | cons v vs ih =>
    have first : (TeamBurstProbeStep.pair a t v).map WordRecord.record =
        TeamRecords.pair (TeamProbeEmit.widenRecord ⟨a.val,t.val,v,v⟩) := rfl
    simp only [records, List.map_append, claimed, List.map_cons, List.flatMap_cons, first]
    congr 1
    by_cases e : vs = []
    · subst vs; rfl
    have pos := List.length_pos_iff.mpr e
    simp only [List.length_cons] at ha ht
    have a' : (next a).val = a.val+1 := Nat.mod_eq_of_lt (by omega)
    have t' : (next t).val = t.val+1 := Nat.mod_eq_of_lt (by omega)
    have rest := ih (next a) (next t) (by rw [a']; omega) (by rw [t']; omega)
    simpa only [a',t'] using rest

/-- Replacing the guesses with actual memory yields the canonical shared-memory transcript. -/
theorem claimed_true (m : ℕ → Word w) (a t q : ℕ) :
    claimed a t (List.ofFn fun i : Fin q => m (a+i.val)) =
      TeamRecords.transcript m (TeamRecords.readBurst a t q) := by
  rw [← List.append_nil (TeamRecords.readBurst (Word := Word w) a t q),
    TeamRecords.transcript_readBurst]
  simp only [TeamRecords.transcript,List.append_nil]
  induction q generalizing a t with
  | zero => rfl
  | succ q ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [claimed,Fin.val_zero,Nat.add_zero,Fin.val_succ,List.cons.injEq,true_and]
    simpa only [Nat.add_assoc,Nat.add_comm 1] using ih (a+1) (t+1)

end TeamBurstProbe

end BorderVNP
end Computability
end OAI
