import OAI.Optimization.LinearProgramming.Compression.ServiceResources
import OAI.Optimization.LinearProgramming.Compression.ServicePrepare
import OAI.Optimization.LinearProgramming.Compression.ServiceInvoke
import OAI.Optimization.LinearProgramming.Compression.BinaryFramedReturn
import OAI.Optimization.LinearProgramming.Compression.PhysicalRestart

/-! Restore the publicly observable result of the inner numerical ROM and the correct
persistent generator state. All address-bit positions are obtained from the returned
canonical numerator and denominator. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServicePost
open RAM OracleSpec.MinorLog GeneratorTable ServiceBudget ServicePrepare

variable {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
variable {J : Finset (NonzeroPairMinor D E)} {u : NonzeroPairMinor D E}

theorem arm {cap : ℕ} {s x : Memory ℚ} (h : Ready D E J u cap s x) :
    Ready D E J u cap s (x.putIndex 15 1) := by
  refine ⟨h.evenScalar,?_,?_,h.oddScalar,?_,?_,?_⟩
  · intro i hi; simpa [show 2*i ≠ 15 by omega] using h.evenAddress i hi
  · intro i hi
    by_cases q : 2*i+1=15
    · simp [q,ServiceFill.oddAddressBudget]
    · simpa [q] using h.oddBound i hi
  · simpa using h.length
  · simpa using h.position
  · exact ⟨by simpa using h.table.baseWord,by simpa using h.table.strideWord,
      by simpa using h.table.stopWord,by simpa using h.table.nextWord⟩

theorem restartSource {cap tag : ℕ} {old p last x : Memory ℚ} (h : Ready D E J u cap old p)
    (r : ServiceInvoke.Returned p last x cap tag) : RestartSource J u old x (live n J.card) :=
  RestartSource.of_prefix
    ((r.oddAddress 0 (by decide)).trans h.length) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _))
    ((r.oddAddress 1 (by decide)).trans h.position)
    ((r.oddAddress 46 (by decide)).trans h.table.baseWord)
    ((r.oddAddress 47 (by decide)).trans h.table.strideWord)
    ((r.oddAddress 48 (by decide)).trans h.table.stopWord)
    ((r.oddAddress 49 (by decide)).trans h.table.nextWord)
    (fun i lo hi i5 i6 => (r.oddScalar i).trans (h.oddScalar i lo hi i5 i6))

theorem sumWidths_le (q : ℚ) : width q.num.natAbs+width q.den ≤ ratBits q := by
  unfold width ratBits
  omega

/-- The physical return tag occupies an odd address, so every even digit in the sealed
callee output is available without modifying the canonical representation. -/
theorem doubled_output {p x : Memory ℚ} {last : State ℚ} {cap tag : ℕ} {q : ℚ}
    (r : ServiceInvoke.Returned p last.memory x cap tag) (out : explicitValue last q)
    (room : 2*(ratBits q+2) ≤ cap) :
    x.data 0=q ∧ DoubledPacket x (width q.num.natAbs) (width q.den) (decide (q.num<0)).toNat (publicDigit q) := by
  obtain ⟨h0,hn,hd,hs,nw,dw⟩ := out
  have fit := packet_room room
  refine ⟨(r.scalar 0 (by omega)).trans h0,?_,?_,?_,?_⟩
  · exact (r.address 0 (by omega)).trans (congrArg (2*·) hn)
  · exact (r.address 1 (by omega)).trans (congrArg (2*·) hd)
  · exact (r.address 2 (by omega)).trans (congrArg (2*·) hs)
  · intro i hi
    have read := r.address (3+i) (by omega)
    have addr : 2*(3+i)=6+2*i := by omega
    rw [addr] at read
    refine read.trans (congrArg (2*·) ?_)
    change last.index (3+i)=publicDigit q i
    by_cases low : i<width q.num.natAbs
    · simpa [publicDigit,low] using nw i low
    · have j := dw (i-width q.num.natAbs) (by omega)
      simpa only [publicDigit,ite_eq_right low,show 3+width q.num.natAbs+(i-width q.num.natAbs)=3+i by omega] using j

theorem accept {cap H : ℕ} {old p x : Memory ℚ} {last : State ℚ} {q : ℚ}
    (src : Persistent D E J H old) (ready : Ready D E J u cap old p)
    (r : ServiceInvoke.Returned p last.memory x cap 0) (out : explicitValue last q)
    (safe : ∀ i, ratBits (x.data i) ≤ H) (room : 2*(ratBits q+2) ≤ cap)
    (small : ∀ j ≤ ratBits q,ratBits (j:ℚ) ≤ H) :
    ∃ z, Block.Eval (Memory.AllData (fun y => ratBits y ≤ H)) restorePublishedReply x
        (7*(live n J.card-1)+19*(width q.num.natAbs+width q.den)+27) z ∧
      explicitValue (z.atPC 0) q ∧ Persistent D E J H z := by
  obtain ⟨value,bits⟩ := doubled_output r out room
  have hlen := (r.oddAddress 0 (by decide)).trans ready.length
  obtain ⟨z,run,reply,restore⟩ := restorePublishedReply_from_physical
    (P := fun y : ℚ => ratBits y ≤ H) x (live n J.card) q safe hlen value bits
    (fun i hi => small i (hi.trans (sumWidths_le q)))
  refine ⟨z,run,reply,src.keep_prefix ?_ run.safe_end⟩
  intro i hi i0 i5 i6
  have grow : slotBase n J.card ≤ slotBase n (J.card+2) :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : J.card ≤ J.card+2)) _
  have lim : i < live n J.card := by unfold live; omega
  exact (restore i (by omega) lim i5 i6).trans
    ((r.oddScalar i).trans (ready.oddScalar i (by omega) lim i5 i6))

end ServicePost
end Compression
end LinearProgramming
end Optimization
end OAI
