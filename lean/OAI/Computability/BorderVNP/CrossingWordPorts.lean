import OAI.Computability.BorderVNP.CrossingPaddedModes
import OAI.Computability.BorderVNP.CrossingSignedLookup
import OAI.Computability.VPVNP.JointScalarCore

/-! # Boolean input ports and erasure transitions for the signed field-word verifier -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed.WordFrame

open Lemmata.FockCircuits.FiniteIdentity (Index)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierNetwork (Frame)

/-- The source, output and input occupation-mask ports. -/
abbrev Masks (L : ℕ) := Fin L ⊕ Fin L ⊕ Fin L
/-- The deletion bit and two binary guesses for one derivative row. -/
abbrev Fields (L : ℕ) := Unit ⊕ Fin (Padded.width L) ⊕ Fin (Padded.width L)
/-- The complete fixed-width signed witness. -/
abbrev Witnesses (L : ℕ) := Fin L × Fields L
/-- All free wires of the field-word verifier. -/
abbrev Inputs (L : ℕ) := Masks L ⊕ Witnesses L

/-- All source, requested-output and initial-input occupation bits, followed by the packets. -/
def pack {L : ℕ} (A I J : Finset ℕ) (x : Witnesses L → Bool) : Inputs L → Bool :=
  Sum.elim (Sum.elim (fun i => decide (i.val ∈ A))
    (Sum.elim (fun i => decide (i.val ∈ I)) (fun i => decide (i.val ∈ J)))) x

/-- Address of the creation/deletion selector. -/
def delPort {L : ℕ} (m : Fin L) : Inputs L := .inr (m,.inl ())
/-- Address of a bit of the guessed mode. -/
def modePort {L : ℕ} (m : Fin L) (i : Fin (Padded.width L)) : Inputs L := .inr (m,.inr (.inl i))
/-- Address of a bit of the guessed multiplicity. -/
def weightPort {L : ℕ} (m : Fin L) (i : Fin (Padded.width L)) : Inputs L := .inr (m,.inr (.inr i))

/-- Decode the Boolean fields of a packet into finite binary numbers. -/
def packet {L : ℕ} (x : Witnesses L → Bool) (m : Fin L) : Padded.Packet L :=
  (x (m, .inl ()), Lookup.number _ (fun i => x (m,.inr (.inl i))),
    Lookup.number _ (fun i => x (m,.inr (.inr i))))

/-- Each bit assignment encodes one packet tuple and each packet tuple has one encoding. -/
def packetEquiv (L : ℕ) : (Witnesses L → Bool) ≃ (Fin L → Padded.Packet L) where
  toFun := packet
  invFun p a := a.2.elim (fun _ => (p a.1).1)
    (Sum.elim ((Lookup.number _).symm (p a.1).2.1) ((Lookup.number _).symm (p a.1).2.2))
  left_inv x := by
    funext ⟨m,f⟩
    rcases f with u | k | k
    · cases u; rfl
    · simp [packet]
    · simp [packet]
  right_inv p := by funext m; simp [packet]

/-- Boolean equality test for the mode code and a fixed natural value. -/
def isMode {L : ℕ} (m : Fin L) (k : ℕ) : Expr (Inputs L) :=
  .and (Lookup.less _ (modePort m) (k+1)) (.not (Lookup.less _ (modePort m) k))

theorem isMode_eval {L : ℕ} (m : Fin L) (k : ℕ) (A I J : Finset ℕ) (x : Witnesses L → Bool) :
    (isMode m k).eval (pack A I J x) = decide ((packet x m).2.1.val = k) := by
  rw [isMode, Expr.eval, Expr.eval, Lookup.less_eval, Lookup.less_eval]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  dsimp [packet, modePort, pack, Function.comp_def]
  omega

theorem isMode_size {L : ℕ} (m : Fin L) (k : ℕ) :
    (isMode m k).size ≤ 6 * Padded.width L + 4 := by
  simp only [isMode, Expr.size]
  have := Lookup.less_size _ (modePort m) (k+1)
  have := Lookup.less_size _ (modePort m) k
  omega

/-- Propagate all ports while erasing the chosen mode from the active endpoint. -/
def afterExpr {L : ℕ} (m : Fin L) : Inputs L → Expr (Inputs L)
  | .inl (.inr (.inl k)) =>
    .and (.input (.inl (.inr (.inl k)))) (.not (.and (.input (.inl (.inl m)))
      (.and (.not (.input (delPort m))) (isMode m k))))
  | .inl (.inr (.inr k)) =>
    .and (.input (.inl (.inr (.inr k)))) (.not (.and (.input (.inl (.inl m)))
      (.and (.input (delPort m)) (isMode m k))))
  | p => .input p

/-- Gate frame updating the live masks for the next derivative. -/
noncomputable def after {L : ℕ} (m : Fin L) : Frame (Inputs L) (Inputs L) :=
  (Frame.initial id).step (afterExpr m)

theorem after_eval {L : ℕ} (m : Fin L) (A I J : Finset ℕ) (x : Witnesses L → Bool) :
    (after m).eval (pack A I J x) =
      let ij := Padded.next (decide (m.val ∈ A)) (packet x m) I J
      pack A ij.1 ij.2 x := by
  funext p
  have h : (Frame.initial (id : Inputs L → Inputs L)).eval (pack A I J x) = pack A I J x := by ext; simp
  rw [after, Frame.step_eval, h]
  rcases p with (k | k | k) | w
  · rfl
  · simp only [afterExpr, Expr.eval, isMode_eval]
    by_cases hm : m.val ∈ A <;> cases hd : x (m,.inl ()) <;>
      simp [Padded.next, hm, hd, pack, packet, delPort, Finset.mem_erase, eq_comm, and_comm]
  · simp only [afterExpr, Expr.eval, isMode_eval]
    by_cases hm : m.val ∈ A <;> cases hd : x (m,.inl ()) <;>
      simp [Padded.next, hm, hd, pack, packet, delPort, Finset.mem_erase, eq_comm, and_comm]
  · rfl

theorem after_size {L : ℕ} (m : Fin L) :
    (after m).size ≤ Fintype.card (Inputs L) * (6 * Padded.width L + 14) := by
  apply (Frame.step_size_le (Frame.initial id) (afterExpr m) (6 * Padded.width L + 14) ?_).trans (by simp)
  intro p
  rcases p with (k | k | k) | w
  · change 1 ≤ _; omega
  · simp only [afterExpr, Expr.size]; have := isMode_size m k; omega
  · simp only [afterExpr, Expr.size]; have := isMode_size m k; omega
  · change 1 ≤ _; omega

/-- Sign-selecting circuit outputs. The zero value sets both outputs to false. -/
def flag (z : ℤ) (neg : Bool) : Bool := if neg then decide (z < 0) else decide (0 < z)

end Crossing.Signed.WordFrame

end BorderVNP
end Computability
end OAI
