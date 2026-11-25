import OAI.Computability.BorderVNP.PackedTerminalScheduledSourceRate
import OAI.Computability.BorderVNP.PackedTerminalPacketRate
import OAI.Computability.BorderVNP.DiagonalJointWords

/-! # Hardware index limits of the two retained signed packet tapes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Filter TeamScales Diagonal Packing Packing.Inherited.FrozenTape CellPacketGeometry CellPacketGeometry.History
open CellPacketGeometry.LiveWords Shortening.PublicCapacity TerminalCells CellSparse.Packet
open scoped Classical

/-- The row and factor counts of the terminal directory are independent of its
final binding-word width. Early geometry words can stay short when the signed
report and final bindings use the full hardware word. -/
theorem signedSource_width_irrel {R B Orig E : Type} [Fintype E]
    {s C m n : ℕ} (S : Schema R B) (boxes : Fin s → List (Source.Box Orig))
    (rep : Fin (C+1) → List (List E)) (u v : ℕ) :
    sourceVolume S (Inherited.FinalTies.tieSchema m n u) boxes rep =
    sourceVolume S (Inherited.FinalTies.tieSchema m n v) boxes rep := rfl

/-- A fixed number of times any polynomial in the logarithmic report width
and the signed rectangle fits an actual native word. The threshold is uniform
in the batch count, including one. -/
theorem eventually_signed_packet_room (A degree E : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → ∀ rows vol : ℕ, rows ≤ r*n →
      vol ≤ A*rows*(logWidth r n)^degree →
      256*vol+2*rows+1 < 2^((logWidth r n)^(E+2)) := by
  filter_upwards [eventually_polynomial_words (256*A+3) (degree+1) E] with n all
  intro r hr rows vol rowCap cap
  let z := r*n+1
  have logFit : logWidth r n ≤ z := by
    rw [public_logWidth]
    apply Nat.clog_le_of_le_pow
    change 2*n*r ≤ 2^(r*n+1)
    rw [pow_succ]
    have h := Nat.mul_le_mul_right 2 (Nat.lt_two_pow_self (n := r*n)).le
    simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h
  have room : rows ≤ z := rowCap.trans (Nat.le_succ _)
  have zpos : 1 ≤ z := Nat.succ_pos _
  have grow : z ≤ z^(degree+1) := (Nat.le_mul_of_pos_left _ (Nat.pow_pos zpos)).trans_eq (pow_succ ..).symm
  have volBound : vol ≤ A*z^(degree+1) := cap.trans ((Nat.mul_le_mul (Nat.mul_le_mul_left _ room)
    (Nat.pow_le_pow_left logFit degree)).trans_eq (by rw [pow_succ]; ring))
  apply lt_of_le_of_lt _ (all r hr)
  change 256*vol+2*rows+1 ≤ (256*A+3)*z^(degree+1)
  have scaled := Nat.mul_le_mul_left 256 volBound
  have remaining := room.trans grow
  have pos := zpos.trans grow
  simp only [Nat.add_mul,Nat.mul_assoc] at scaled ⊢
  omega

/-- The common sparse volume gives all five ordered packet sort depths and
the strict site and row bounds used by the signed index encoders. -/
theorem signedPacket_depths {Row B U V E Orig : Type} [Fintype E] {s C cap W : ℕ}
    (S : Schema Row B) (T : Schema U V) (boxes : Fin s → List (Source.Box Orig))
    (sh : ∀ r, (S.tags r).length ≤ cap) (th : ∀ r, (T.tags r).length ≤ cap)
    (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E))
    (room : 256*sourceVolume S T boxes rep < 2^W) :
    let tpl := template S T boxes sh th priv rep
    let l := (roster s S T).length
    s < 2^W ∧ C < 2^W ∧ l < 2^W ∧
    tpl.publicDepth ≤ W ∧ tpl.chunkDepth ≤ W ∧ tpl.recordDepth ≤ W ∧
    Nat.clog 2 (l+(C+1)) ≤ W ∧ Nat.clog 2 ((s+1)+l) ≤ W := by
  intro tpl l
  let volume := sourceVolume S T boxes rep
  have pay : 4*tpl.publicVolume ≤ 2^W := (Nat.mul_le_mul_left 4
    (publicVolume_le_source S T boxes sh th priv rep)).trans (by
      change 4*(64*volume) ≤ 2^W
      change 256*volume < 2^W at room
      omega)
  obtain ⟨pub,chunk,recDepth,clog⟩ := packet_depths tpl pay
  have rows : (s+1)+l ≤ 3*volume ∧ C ≤ volume := by
    dsimp only [l,volume,sourceVolume,roster]
    simp only [List.length_append,List.length_map,List.length_cons,List.length_nil,List.length_finRange]
    omega
  change 256*volume < 2^W at room
  exact ⟨by omega,by omega,by omega,pub,chunk,recDepth,clog,Nat.clog_le_of_le_pow (by omega)⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
