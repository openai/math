import OAI.Optimization.LinearProgramming.Compression.BinaryRestoreFrame
import OAI.Optimization.LinearProgramming.Compression.BinaryUnpackHeader
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec.MinorLog

def publicDigit (q : ℚ) (i : ℕ) : ℕ :=
  if i < width q.num.natAbs then (q.num.natAbs.testBit i).toNat else (q.den.testBit (i-width q.num.natAbs)).toNat

private theorem boolToNatBound (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

theorem publicDigit_le_one (q : ℚ) (i : ℕ) : publicDigit q i ≤ 1 := by
  unfold publicDigit
  split <;> exact boolToNatBound _

/-- First restore the saved caller's scalar bank; then expose the virtual address packet
at its unscaled public addresses. The two phases share only scratch scalars 5 and 6. -/
def restorePublishedReply : Block := .seq restoreScalarFrameBlock unpackAddressPacket

/-- Only the finite even packet and the saved odd scalar cells are read on return.
All other physical address cells may contain arbitrary caller data. -/
theorem restorePublishedReply_from_physical (m : Memory ℚ) (live : ℕ) (q : ℚ) {P : ℚ → Prop}
    (safe : m.AllData P) (liveSize : m.index 1=live) (value : m.data 0=q)
    (source : DoubledPacket m (width q.num.natAbs) (width q.den) (decide (q.num < 0)).toNat (publicDigit q))
    (small : ∀ i : ℕ, i ≤ width q.num.natAbs + width q.den → P (i:ℚ)) :
    ∃ z, Block.Eval (Memory.AllData P) restorePublishedReply m
      (7*(live-1)+19*(width q.num.natAbs+width q.den)+27) z ∧ explicitValue (z.atPC 0) q ∧
      ∀ i, 1 ≤ i → i < live → i ≠ 5 → i ≠ 6 → z.data i=m.data (2*i+1) := by
  let N := width q.num.natAbs
  let D := width q.den
  let sg := (decide (q.num < 0)).toNat
  have npos : 0 < N := Nat.zero_lt_succ _
  have dpos : 0 < D := Nat.zero_lt_succ _
  have sgl : sg ≤ 1 := boolToNatBound _
  obtain ⟨u,restore,uv,uf,_,ui⟩ := restoreScalarFrameBlock_on m live safe liveSize
  have packed : DoubledPacket u N D sg (publicDigit q) :=
    ⟨(ui 0 (by decide) (by decide)).trans source.numeratorWidth,
     (ui 2 (by decide) (by decide)).trans source.denominatorWidth,
     (ui 4 (by decide) (by decide)).trans source.negative,
     fun i hi => (ui (6+2*i) (by omega) (by omega)).trans (source.words i hi)⟩
  obtain ⟨z,finish,out,fd⟩ := unpackAddressPacket_spec u N D sg (publicDigit q) restore.safe_end packed
    (by omega) sgl (fun i _ => publicDigit_le_one q i) small
  refine ⟨z,?_,⟨(fd 0 (by decide) (by decide)).trans (uv.trans value),out.numeratorWidth,out.denominatorWidth,out.negative,?_,?_⟩,?_⟩
  · simpa only [restorePublishedReply,N,D,show 7*(live-1)+3+(19*(N+D)+24)=7*(live-1)+19*(N+D)+27 by omega] using restore.seq finish
  · intro i hi
    exact (out.words i (by omega)).trans (by simp [publicDigit,hi])
  · intro i hi
    have eq : 3+N+i=3+(N+i) := by omega
    change z.index (3+N+i)=_
    rw [eq,out.words (N+i) (by omega)]
    have range : ¬N+i < width q.num.natAbs := by change ¬N+i < N; omega
    have sub : N+i-width q.num.natAbs=i := by change N+i-N=i; omega
    simp only [publicDigit,range,ite_false,sub]
  · intro i lo hi i5 i6
    exact (fd i i5 i6).trans (uf i lo hi i6)

theorem restorePublishedReply_spec (callee frame : Memory ℚ) (live : ℕ) (q : ℚ) {P : ℚ → Prop}
    (safe : (Call.pack callee frame).AllData P) (liveSize : frame.index 0=live)
    (inside : explicitValue (callee.atPC 0) q)
    (small : ∀ i : ℕ, i ≤ width q.num.natAbs + width q.den → P (i:ℚ)) :
    ∃ z, Block.Eval (Memory.AllData P) restorePublishedReply (Call.pack callee frame)
      (7*(live-1)+19*(width q.num.natAbs+width q.den)+27) z ∧ explicitValue (z.atPC 0) q ∧
      ∀ i, 1 ≤ i → i < live → i ≠ 5 → i ≠ 6 → z.data i=frame.data i := by
  let N := width q.num.natAbs
  let D := width q.den
  let sg := (decide (q.num < 0)).toNat
  obtain ⟨v,n,d,s,b,c⟩ := inside
  have even (i : ℕ) : (Call.pack callee frame).index (2*i)=2*callee.index i := Call.index_even ..
  have packed : DoubledPacket (Call.pack callee frame) N D sg (publicDigit q) := by
    refine ⟨(even 0).trans (congrArg (2*·) n),(even 1).trans (congrArg (2*·) d),
      (even 2).trans (congrArg (2*·) s),?_⟩
    intro i hi
    rw [← show 2*(3+i)=6+2*i by omega,even]
    by_cases hn : i < N
    · have hbit : publicDigit q i = (q.num.natAbs.testBit i).toNat := by simp [publicDigit,show i < width q.num.natAbs from hn]
      exact congrArg (2*·) ((b i hn).trans hbit.symm)
    · have j : i-N < D := by omega
      have pos : 3+i=3+N+(i-N) := by omega
      rw [pos,show callee.index (3+N+(i-N)) = (q.den.testBit (i-N)).toNat from c _ j]
      simp [publicDigit,show ¬i < width q.num.natAbs from hn,N]
  obtain ⟨z,run,output,saved⟩ := restorePublishedReply_from_physical (Call.pack callee frame) live q safe
    ((Call.index_odd callee frame 0).trans liveSize) ((Call.data_even callee frame 0).trans v) packed small
  exact ⟨z,run,output,fun i hi hu i5 i6 => (saved i hi hu i5 i6).trans (Call.data_odd callee frame i)⟩

/-- Precisely the active scalar storage of the persistent compression service. -/
def replyFrameExtent (n g : ℕ) := 7+n*n+(2*n+3)*g

theorem protectedReplyCoordinates (m f : Memory ℚ) (n g : ℕ)
    (frame : ∀ i, 1 ≤ i → i < replyFrameExtent n g → i ≠ 5 → i ≠ 6 → m.data i=f.data i) :
    (∀ i, 1 ≤ i → i ≤ 4 → m.data i=f.data i) ∧ (∀ i < n*n, m.data (7+i)=f.data (7+i)) ∧
    ∀ j < g, ∀ r < 2*n+3, m.data (7+n*n+(2*n+3)*j+r)=f.data (7+n*n+(2*n+3)*j+r) := by
  unfold replyFrameExtent at frame
  refine ⟨fun i hi h => frame i hi (by omega) (by omega) (by omega),
    fun i hi => frame _ (by omega) (by omega) (by omega) (by omega),?_⟩
  intro j hj r hr
  have l : (2*n+3)*j+r < (2*n+3)*(j+1) := by rw [Nat.mul_succ]; omega
  have inside : (2*n+3)*j+r < (2*n+3)*g :=
    l.trans_le (Nat.mul_le_mul_left (2*n+3) hj)
  have upper := Nat.add_lt_add_left inside (7+n*n)
  exact frame _ (by omega) (by simpa only [Nat.add_assoc] using upper) (by omega) (by omega)

end Compression
end LinearProgramming
end Optimization
end OAI
