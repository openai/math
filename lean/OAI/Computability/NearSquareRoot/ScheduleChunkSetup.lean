import OAI.Computability.NearSquareRoot.ScheduleChunkTask

/-!
# External encodings of the fenced digit-product loop

The preparation command reverses both MSF words, checks and computes a dyadic
split, allocates a zero accumulator, and buildCursors the two cursors. On return
the used state is discarded and the accumulator is reversed to MSF order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkTask
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits ChunkLoop

private abbrev RawInput := Tally × Operands
private abbrev Working := Operands × Word
private abbrev Descriptor := Tally × Tally

private def prepare (x : RawInput) : Option Descriptor × Working :=
  (Uniform.Dyadic.checked (x.1, ruler x.2.1),
    (x.2.1.reverse, x.2.2.reverse), fill false (ruler (x.2.1 ++ x.2.2)))

private theorem easy_prepare : Easy prepare := by
  apply Easy.pair
  · exact (Easy.fst.pair (Easy.ruler Easy.snd.fstCompose)).compose Uniform.Dyadic.easy_checked
  · apply Easy.pair
    · exact (easy_reverse Easy.snd.fstCompose).pair (easy_reverse Easy.snd.sndCompose)
    · exact easy_fill false (Easy.ruler (easy_append Easy.snd.fstCompose Easy.snd.sndCompose))

/-- The encoded `some descriptor` has the same tree as `(true,descriptor)`
when the length guard succeeds. -/
private def buildCursor (x : (Bool × Descriptor) × Working) : Operands × ChunkLoop.State :=
  (x.2.1, ChunkCursor.initial x.1.2, x.2.2)

private theorem easy_buildCursor : Easy buildCursor :=
  Easy.snd.fstCompose.pair ((Easy.fst.sndCompose.compose ChunkCursor.easy_initial).pair
    Easy.snd.sndCompose)

/-- Prepare a valid dyadic split from the split exponent and the two original
MSF inputs. A single stack command works simultaneously for all inputs. -/
theorem setup (m : Operands → Word) :
    Task (fun p : Input => p.n) (fun p => send (tally p.k,(p.x,p.y)))
      (fun p => send (p.bundle m 0)) := by
  let input (p : Input) : RawInput := (tally p.k,p.x,p.y)
  let record (p : Input) : (Bool × Descriptor) × Working :=
    ((true,tally p.u,tally p.r),p.operands,List.replicate (2*p.n) false)
  have pre := (easy_prepare.on input).conform (fun _ => rfl) (fun _ => rfl)
    (q' := fun p => send (record p)) (fun p => by
      have h := p.fits
      simp only [prepare, input, Uniform.Dyadic.checked, tally_length, ruler_length]
      rw [ite_eq_left h]
      simp only [record, Input.u, Uniform.chunkWidth, Input.operands, Input.r, Input.n,
        send_prod, send_some, show send true = Tree.atom true from rfl, fill_eq, ruler_length, List.length_append, p.same,
        two_mul])
  have run := pre.compose (easy_buildCursor.on record)
  refine (run.bound 42 ?_).conform (fun _ => rfl) (fun _ => rfl) ?_
  · intro p
    have h₁ : p.k ≤ p.n := Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self) p.fits
    have h₂ := p.width_le
    have h₃ : p.r ≤ p.n := p.fits
    simp only [input, record, size_prod, size_tally, size_word, tally_length, List.length_replicate,
      show size true = 1 from rfl, Input.operands, List.length_reverse, p.same]
    change _ ≤ 42 * (p.n+1)
    dsimp only [Input.n] at *
    omega
  · intro p
    simp [buildCursor, record, Input.bundle, Input.state, ChunkCursor.initial_eq]

/-- Release the `2*n` product positions in most-significant-first order. -/
theorem emit (m : Operands → Word) :
    Task (fun p : Input => p.n) (fun p => send (p.bundle m p.count))
      (fun p => send (p.state m p.count).2.reverse) := by
  have h : Easy (fun s : Operands × ChunkLoop.State => s.2.2.reverse) :=
    easy_reverse Easy.snd.sndCompose
  refine (h.on (fun p : Input => p.bundle m p.count)).bound 25 ?_
  intro p
  have := p.bundle_size m p.count le_rfl
  omega

end ChunkTask

end NearSquareRoot
end Computability
end OAI
