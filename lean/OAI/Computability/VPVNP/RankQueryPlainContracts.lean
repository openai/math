import OAI.Computability.VPVNP.RankQueryPlainScalar
import OAI.Computability.VPVNP.RankQueryDescribeSpace
import OAI.Computability.VPVNP.RegisterTable

/-! # Signed scalar contracts for the Cramer minor reader -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.PlainScalar

open RAMTape BurstRAM Dispatch

variable {K : Type} [DecidableEq K] {w v p e n d B S A : ℕ}
  [Fact p.Prime] [NeZero e] {c : SliceArithmetic.Vector p e}

/-- The constant-polynomial entry call can be installed in the same Schur
dispatcher as a weighted Gram entry. -/
theorem callSpace (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin n) (Scalar c))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v) (hw₁ : 1 ≤ w) :
    DescribeAdapter.CallSpace (machine read) (entry M) w v n d (clock w v e B)
      (fun a => space w v e a S) ready :=
  fun i j z neg persist rs _ hr aux hs start => machine_bounded read M hc hw hw₁ i j z neg persist rs hr aux hs start

theorem callRuns (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin n) (Scalar c))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (haux : ∀ s, ready s → ∀ i, (s i).length ≤ A)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v) (hw₁ : 1 ≤ w) :
    DescribeAdapter.CallRuns (machine read) (entry M) w v n d (clock w v e B) ready := by
  intro i j z neg persist rs he hr aux hs
  have hstart (k : GramScalar.Port K) : (GramScalar.bank (GramScalar.wordBank persist rs)
      (GramRead.arithmeticBank v c [] []) aux k).length ≤ w+v+e+e*v+A := by
    cases k with
    | words i => exact (RegisterTable.bank_length_le Fin.elim0 persist rs i).trans (by omega)
    | aux i => exact (haux _ hs i).trans (by omega)
    | mul i =>
      rcases i with i | i
      · exact Nat.zero_le _
      · cases i <;> simp [GramScalar.bank,GramRead.arithmeticBank,SliceArithmetic.MultiplyCall.clean,
          SliceArithmetic.MultiplyCall.external] <;> omega
    | _ => exact Nat.zero_le _
  obtain ⟨t,ht,out,aux',hs',hout,hrun⟩ := callSpace (d := d) read M hc hw hw₁ i j z neg persist rs he hr aux hs hstart
  exact ⟨t,ht,out,aux',hs',hout,hrun.runs⟩

end RankQuery.Stack.PlainScalar

end VPVNP
end Computability
end OAI
