import OAI.Computability.NearSquareRoot.ScheduleChunkIteration
import OAI.Computability.NearSquareRoot.ScheduleChunkLoop
import OAI.Computability.NearSquareRoot.ScheduleChunkWidth

/-! # A single costed program for variable dyadic splits -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkTask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open ChunkLoop

/-- A pair of raw MSF operands and a permissible split exponent. The proofs are
ghost parameters of the costed specification and have no runtime encoding. -/
structure Input where
  x : Word
  y : Word
  k : ℕ
  same : y.length = x.length
  fits : 2^k ≤ x.length

namespace Input

abbrev n (p : Input) := p.x.length
abbrev r (p : Input) := 2 ^ p.k
abbrev u (p : Input) := Uniform.chunkWidth p.n p.r
abbrev operands (p : Input) : Operands := (p.x.reverse, p.y.reverse)
abbrev count (p : Input) := p.r * p.r

theorem positive (p : Input) : 0 < p.r := by dsimp [r]; positivity

theorem width_pos (p : Input) : 0 < p.u := by
  have hn : 0 < p.n := p.positive.trans_le p.fits
  have h : p.n ≤ p.r * p.u := (Uniform.chunkWidth_bounds p.positive).1
  by_contra! hz
  rw [Nat.eq_zero_of_le_zero hz, Nat.mul_zero] at h
  omega

theorem width_le (p : Input) : p.u ≤ p.n := by
  apply (ceilDiv_le_iff_le_mul p.positive).2
  exact Nat.le_mul_of_pos_left _ p.positive

def state (p : Input) (m : Operands → Word) (t : ℕ) : ChunkLoop.State :=
  (step m p.operands)^[t] (ChunkCursor.atPair p.r p.u 0 0, List.replicate (2*p.n) false)

abbrev bundle (p : Input) (m : Operands → Word) (t : ℕ) := (p.operands, p.state m t)

theorem done_test (p : Input) (m : Operands → Word) (t : ℕ) (ht : t ≤ p.count) :
    ChunkCursor.exhausted (p.state m t).1 = decide (t = p.count) :=
  exhausted_iterate m p.operands p.positive p.u t ht _

theorem bundle_size (p : Input) (m : Operands → Word) (t : ℕ) (ht : t ≤ p.count) :
    size (p.bundle m t) ≤ 24*p.n+17 := by
  have h : size (p.state m t) ≤ 20*p.n+13 :=
    size_iterate m p.operands p.positive p.fits ht _ (by simp)
  change size (p.operands, p.state m t) ≤ _
  rw [size_prod, size_prod p.operands, size_word, size_word]
  simp only [List.length_reverse, p.same, n] at *
  omega

theorem query_width (p : Input) (m : Operands → Word) (t : ℕ) :
    (query (p.bundle m t)).1.length = p.u ∧ (query (p.bundle m t)).2.length = p.u := by
  have hc : (p.state m t).1 = _ := cursor_at_step m p.operands p.positive p.u t _
  simp [query,hc,ChunkCursor.atPair,ChunkArithmetic.extract_length]

end Input

/-- A short-call program is required only on positive equal-width operand pairs. -/
abbrev EqualWords := {w : Operands // w.1.length = w.2.length ∧ 0 < w.1.length}

private abbrev Bundle := Operands × ChunkLoop.State

private def post (v : Word × Bundle) : Bundle := (v.2.1, update (v.2.2, v.1))

private theorem easy_post : Easy post := by
  exact (show Easy (fun v : Word × Bundle => v.2.1) by fun_prop).pair
    ((show Easy (fun v : Word × Bundle => (v.2.2, v.1)) by fun_prop).compose easy_update)

private abbrev allowance (T : ℕ → ℕ) (p : Input) := 60*(p.n+1)+T p.u

/-- A single digit pass parks its source/accumulator record while the callee
operates on its extracted arguments. Only one short product is charged. -/
private theorem pass (m : Operands → Word) (T : ℕ → ℕ)
    (callee : Task (fun q : EqualWords => T q.val.1.length)
      (fun q => send q.val) (fun q => send (m q.val)))
    (width : ∀ q : EqualWords, (m q.val).length = 2*q.val.1.length) :
    Task (fun v : (p : Input) × Fin p.count => allowance T v.1)
      (fun v => send (v.1.bundle m v.2.val)) (fun v => send (v.1.bundle m (v.2.val+1))) := by
  let P := (p : Input) × Fin p.count
  let b (v : P) := v.1.bundle m v.2.val
  let q (v : P) : EqualWords := ⟨query (b v),
    ⟨(v.1.query_width m v.2.val).1.trans (v.1.query_width m v.2.val).2.symm,
    (v.1.query_width m v.2.val).1.symm ▸ v.1.width_pos⟩⟩
  have pre := (easy_query.pair Easy.identity).on b
  have call := (callee.on q).left (fun v => send (b v))
  have release := easy_post.on (fun v => (m (q v).val,b v))
  have run := (pre.compose call).compose release
  refine (run.mono (fun v => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun v => ?_)
  · have hs := v.1.bundle_size m v.2.val v.2.isLt.le
    have hq := (v.1.query_width m v.2.val).1
    have hz := width (q v)
    change (q v).val.1.length = v.1.u at hq
    change size (b v) ≤ _ at hs
    change size (b v) + T (q v).val.1.length + size (m (q v).val, b v) ≤ allowance T v.1
    rw [size_prod (m (q v).val, b v), size_word, hz, hq]
    dsimp only [allowance]
    have := v.1.width_le
    omega
  · change send (v.1.operands,step m v.1.operands (v.1.state m v.2.val)) = _
    simp only [Input.bundle,Input.state, Function.iterate_succ_apply']

/-- The runtime stopping test is exhaustion of the row cursor. -/
theorem loop (m : Operands → Word) (T : ℕ → ℕ)
    (callee : Task (fun q : EqualWords => T q.val.1.length)
      (fun q => send q.val) (fun q => send (m q.val)))
    (width : ∀ q : EqualWords, (m q.val).length = 2*q.val.1.length) :
    Task (fun p : Input => (p.count+1)*(2*allowance T p+1))
      (fun p => send (p.bundle m 0)) (fun p => send (p.bundle m p.count)) := by
  apply ChunkIteration.task (P := Input) (S := Bundle) (length := Input.count) (allowance := allowance T)
    (state := fun p t => p.bundle m t)
    (fun s : Bundle => ChunkCursor.exhausted s.2.1)
    ((show Easy (fun s : Bundle => s.2.1) by fun_prop).compose ChunkCursor.easy_exhausted)
  · exact fun p t ht => p.done_test m t ht
  · intro p t ht
    have := p.bundle_size m t ht
    dsimp only [allowance]
    omega
  · exact pass m T callee width

end ChunkTask

end NearSquareRoot
end Computability
end OAI
