import OAI.Computability.VPVNP.RAMTapeDivisionForward
import OAI.Computability.VPVNP.RAMTapeDivisionInit
import OAI.Computability.VPVNP.RAMTapeDivisionRestore

/-!
# Restoring division in quadratic bit-stack time

This fixed finite control computes both outputs of the word RAM's unsigned
division and remainder instructions. It preserves the divisor and leaves all
temporary stacks empty. The separate zero-divisor path also works at zero
width. Every input has exactly one accepting path with the stated clock.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.DivisionStack

open RAMTape

private theorem divideStep_length (d r : List Bool) (b : Bool) (hlen : r.length = d.length) :
    (divideStep d b r).2.length = d.length := by
  have hx : (b :: r).length = (d ++ [false]).length := by simp [hlen]
  unfold divideStep
  dsimp only
  split <;> simp [length_subScan hx, hlen]

/-- One complete quotient-digit loop, including the shift, subtraction and
the restoration of the divisor and selected remainder. -/
theorem digitRun (feed q d r : List Bool) (b : Bool) (hlen : r.length = d.length) :
    let t := divideStep d b r
    Run (10 * d.length + 4) .outer ⟨[], b :: feed, d, r, q, [], [], []⟩
      .outer ⟨[], feed, d, t.2, t.1 :: q, [], [], []⟩ := by
  let candidate := b :: r
  let trial := subScan false candidate (d ++ [false])
  let orig := candidate.take d.length
  let diff := trial.1.take d.length
  let selected := if trial.2 then orig else diff
  have hx : candidate.length = (d ++ [false]).length := by simp [candidate, hlen]
  have ho : orig.length = d.length := by simp [orig, candidate, hlen]
  have ht : diff.length = d.length := by simp [diff, trial, length_subScan hx, candidate, hlen]
  have hstep : divideStep d b r = (!trial.2, selected) := by
    unfold divideStep
    change (if trial.2 then (false, orig) else (true, diff)) = _
    dsimp only [selected]
    cases trial.2 <;> rfl
  have hfinish : Run 1 (.digit trial.2) ⟨[],feed,d,selected,q,[],[],[]⟩
      .outer ⟨[],feed,d,selected,(!trial.2)::q,[],[],[]⟩ :=
    prepend rfl (.nil ..)
  have hbody := ((forwardRun feed q d r b hlen).trans
    (restoreRun feed q d orig diff trial.2 ho ht)).trans hfinish
  dsimp only
  rw [hstep, show 10 * d.length + 4 = ((5*d.length + 1) + (5*d.length + 1) + 1) + 1 by omega]
  exact prepend rfl hbody

private def divideFeed (d : List Bool) : List Bool → List Bool → List Bool → List Bool × List Bool
  | [], q, r => (q, r)
  | b :: feed, q, r =>
    let t := divideStep d b r
    divideFeed d feed (t.1 :: q) t.2

private theorem divideFeed_reverse (d x feed : List Bool) :
    divideFeed d (x.reverse ++ feed) [] (List.replicate d.length false) =
      divideFeed d feed (dividePass d x).1 (dividePass d x).2 := by
  induction x generalizing feed with
  | nil => rfl
  | cons b xs ih =>
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, dividePass, divideFeed]
      using ih (b :: feed)

private theorem outerRun (feed q d r : List Bool) (hlen : r.length = d.length) :
    let out := divideFeed d feed q r
    Run (feed.length * (10*d.length+4) + 1) .outer ⟨[],feed,d,r,q,[],[],[]⟩
      .done ⟨[],[],d,out.2,out.1,[],[],[]⟩ := by
  induction feed generalizing q r with
  | nil =>
    simp only [divideFeed, List.length_nil, Nat.zero_mul, Nat.zero_add]
    exact prepend rfl (.nil ..)
  | cons b feed ih =>
    let t := divideStep d b r
    have hr := ih (t.1 :: q) t.2 (divideStep_length d r b hlen)
    have h := (digitRun feed q d r b hlen).trans hr
    simpa only [t, divideFeed, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_left_comm,
      Nat.add_assoc, Nat.add_comm] using h

/-- Exact running time of the restoring word macro. -/
def ticks (x d : List Bool) : ℕ :=
  2 * x.length + 5 * d.length + 3 +
    if d.any id then x.length * (10 * d.length + 4) + 1 else d.length + 3 * x.length + 2

theorem divideRun (x d : List Bool) :
    let out := divideWords x d
    Run (ticks x d) .reverseInput ⟨x,[],d,[],[],[],[],[]⟩
      .done ⟨[],[],d,out.2,out.1,[],[],[]⟩ := by
  have hi := initRun x d
  cases hz : d.any id with
  | false =>
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hi
    simpa only [divideWords, ticks, hz, Bool.false_eq_true, ↓reduceIte] using
      hi.trans (zeroRun x d)
  | true =>
    simp only [hz, ↓reduceIte] at hi
    have ho := outerRun x.reverse [] d
      (List.replicate d.length false) (by simp)
    have he := divideFeed_reverse d x []
    simp only [List.append_nil, divideFeed] at he
    simp only [he, List.length_reverse] at ho
    simpa only [divideWords, ticks, hz, ↓reduceIte] using hi.trans ho

theorem ticks_le {x d : List Bool} (hlen : x.length = d.length) :
    ticks x d ≤ 12 * (x.length + 1)^2 := by
  unfold ticks
  rw [← hlen]
  split <;> ring_nf <;> omega

open BurstRAM PrivateRAM in
/-- Both RAM opcode results in little-endian bit-stack format. The same fixed
program table applies to every word width. -/
theorem divideWordRun {w : ℕ} (x d : Word w) :
    Run (ticks (wordBits x) (wordBits d)) .reverseInput
      ⟨wordBits x,[],wordBits d,[],[],[],[],[]⟩ .done
      ⟨[],[],wordBits d,wordBits (BinaryOp.mod.eval x d),wordBits (BinaryOp.div.eval x d),[],[],[]⟩ := by
  simpa only [divideWords_wordBits] using divideRun (wordBits x) (wordBits d)

/-- An extra instruction beyond the transition bound visits the accepting
halt. The deterministic division routine has exactly one accepting path. -/
theorem dividePaths {x d : List Bool} (hlen : x.length = d.length) :
    stackPaths code (12 * (x.length + 1)^2 + 1) .reverseInput
      (Data.mk x [] d [] [] [] [] []).stacks = 1 := by
  have hle := ticks_le hlen
  let spare := 12 * (x.length + 1)^2 - ticks x d
  have hfuel : 12 * (x.length + 1)^2 + 1 = (spare + 1) + ticks x d := by
    dsimp [spare]; omega
  rw [hfuel, (divideRun x d).paths (spare + 1)]
  rfl

end TapeWord.DivisionStack

end VPVNP
end Computability
end OAI
