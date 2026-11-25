import OAI.Hierarchy.ProtocolRAMAttemptGate
import OAI.Hierarchy.ProtocolRAMSumScoresCheap

namespace OAI
/-! # Computing the three phase tests together from live row scores -/

namespace Hierarchy.ProtocolRAM.AttemptGate
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing

structure Check where
  out : ℕ
  rows : ℕ
  bound : ℕ
  term : Expr

def Check.score {w : ℕ} (z : Check) (m : Memory w) (i : Fin z.rows) :=
  (z.term.eval m (i.val:Word w)).val

def Check.high {w : ℕ} (z : Check) (m : Memory w) := decide (z.bound ≤ ∑i,z.score m i)

def Check.bank (z : Check) : Bank := ⟨z.out+z.rows,0⟩

def Check.code (w : ℕ) (z : Check) :=
  SumScores.procedure w z.out z.rows z.bound z.term

def Check.after {w : ℕ} (z : Check) (m : Memory w) :=
  fillSegment z.out (z.rows+1) (SumScores.word z.out z.bound (z.score m)) m

def Check.ticks (z : Check) := 4+(z.rows+1)*(42+2*z.term.work)

def Check.Ready {w : ℕ} (z : Check) (m : Memory w) : Prop :=
  z.term.Fits w z.out ∧ z.out+(z.rows+1)<2^w ∧ z.bound<2^w ∧ (∑i,z.score m i)<2^w

/-- The global sum needs only the sum of row-address and local-score bit widths,
plus one sentinel bit. This lets 2^h rows use O(h)-bit CPU and memory words. -/
theorem sum_room {n bitsL bitsV w : ℕ} (x : Fin n → ℕ) (rows : n≤2^bitsL)
    (values : ∀ i,x i≤2^bitsV) (wordBits : bitsL+bitsV+1≤w) : ∑ i,x i<2^w := by
  have bound := (Finset.sum_le_sum (s:=Finset.univ) fun i _=>values i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at bound
  have low : ∑i,x i ≤ 2^(bitsL+bitsV) := by
    rw [pow_add]
    exact bound.trans (Nat.mul_le_mul_right _ rows)
  exact (low.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))).trans_le
    (Nat.pow_le_pow_right (by decide) wordBits)

theorem Check.exec {w : ℕ} (z : Check) (m : Memory w) (ready : z.Ready m) :
    (z.code w).Exec m (z.after m) z.ticks := by
  have spec : (z.code w).Spec (fun a=>SumScores.Reads a z.term (z.score m))
      (fun a b=>b=fillSegment z.out (z.rows+1) (SumScores.word z.out z.bound (z.score m)) a) z.ticks :=
    SumScores.run z.out z.bound z.term (z.score m) ready.1 ready.2.1 ready.2.2.1 ready.2.2.2
  intro P R K M pc reg pub exit rom data cfg mem entry same
  subst mem
  exact spec M pc reg pub exit rom data cfg m entry (fun i=>by simp [score])

theorem Check.frame {w : ℕ} (z : Check) (m : Memory w) (a : ℕ) (lo : a<z.out) :
    z.after m a=m a := by simp [after,fillSegment,not_le.mpr lo]

theorem Check.flag {w : ℕ} (z : Check) (m : Memory w) (wide : 0<w) : bit z.bank (z.after m)=z.high m :=
  threshold_bit z.out z.bound (z.score m) m wide

structure TestBoard where
  stop : Bank
  excess : Check
  payload : Check
  discrepancy : Check
  injection : Bool
  reserve : Bool

def TestBoard.inputs (b : TestBoard) : Inputs :=
  ⟨b.stop,b.excess.bank,b.payload.bank,b.discrepancy.bank,b.injection,b.reserve⟩

def TestBoard.code (b : TestBoard) (w : ℕ) :=
  ((b.excess.code w).seq (b.payload.code w)).seq (b.discrepancy.code w)

def TestBoard.after {w : ℕ} (b : TestBoard) (m : Memory w) :=
  b.discrepancy.after (b.payload.after (b.excess.after m))

def TestBoard.ticks (b : TestBoard) := b.excess.ticks+b.payload.ticks+b.discrepancy.ticks

theorem TestBoard.exec {w : ℕ} (b : TestBoard) (m : Memory w) (e : b.excess.Ready m)
    (p : b.payload.Ready (b.excess.after m)) (d : b.discrepancy.Ready (b.payload.after (b.excess.after m))) :
    (b.code w).Exec m (b.after m) b.ticks := by
  apply Procedure.Exec.then (Procedure.Exec.then (b.excess.exec m e) (b.payload.exec _ p))
  intro P R K M pc reg pub exit rom data cfg start entry same
  exact b.discrepancy.exec _ d M pc reg pub exit rom data cfg start entry same

section
attribute [local irreducible] CheapCode

theorem Check.cheap (z : Check) (w : ℕ) : CheapCode (z.code w) := by
  unfold Check.code
  exact @PruneFlag.cheap w z.out z.rows z.bound z.term

theorem TestBoard.cheap (b : TestBoard) (w : ℕ) : CheapCode (b.code w) := by
  unfold TestBoard.code
  exact @cheap_seq w ((b.excess.code w).seq (b.payload.code w)) (b.discrepancy.code w)
    (@cheap_seq w (b.excess.code w) (b.payload.code w) (b.excess.cheap w) (b.payload.cheap w))
    (b.discrepancy.cheap w)

end

private theorem bit_frame {w : ℕ} (z : Check) (m : Memory w) (b : Bank) (lo : b.base<z.out) :
    bit b (z.after m)=bit b m := by
  simp [bit,Bank.read,z.frame m _ lo]

theorem TestBoard.mode {w : ℕ} (b : TestBoard) (m : Memory w) (r : Word w) (wide : 0<w)
    (stopLo : b.stop.base<b.excess.out)
    (xlo : b.excess.out+b.excess.rows<b.payload.out)
    (plo : b.payload.out+b.payload.rows<b.discrepancy.out) :
    (AttemptGate.mode b.inputs).eval (b.after m) r =
    (selectMode b.injection b.reserve (bit b.stop m) (b.excess.high m)
      (b.payload.high (b.excess.after m)) (b.discrepancy.high (b.payload.after (b.excess.after m))) : Word w) := by
  have excessBelow : b.excess.bank.base < b.discrepancy.out := by
    change b.excess.out + b.excess.rows < b.discrepancy.out
    omega
  rw [mode_eval]
  unfold actual inputs
  simp only [after,bit_frame _ _ _ (by omega : b.stop.base<b.discrepancy.out),
    bit_frame _ _ _ (by omega : b.stop.base<b.payload.out),bit_frame _ _ _ stopLo,
    bit_frame b.discrepancy _ b.excess.bank excessBelow,
    bit_frame _ _ _ (show b.excess.bank.base<b.payload.out from xlo),
    bit_frame _ _ _ (show b.payload.bank.base<b.discrepancy.out from plo),Check.flag _ _ wide]

/-- Strict separation from every output bank makes all three checks read the same
input snapshot, regardless of the earlier prefix sums already stored. -/
theorem same_scores {w : ℕ} (x y : Check) (m : Memory w) (early : y.term.Fits w x.out) :
    y.score (x.after m)=y.score m := by
  funext i
  exact congrArg Fin.val (eval_below y.term (i.val:Word w) m (x.after m) early (x.frame m))

end Hierarchy.ProtocolRAM.AttemptGate

end OAI
