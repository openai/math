import OAI.Optimization.LinearProgramming.Compression.DyadicOracleRAM
import OAI.Optimization.LinearProgramming.Compression.DyadicQueryArrayRAM

/-! ## Calling a sign routine on the bisection's actual integer rows -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace DyadicRAM

open RAM OAI.Optimization.LinearProgramming.Lattice

/-- Entry protocol for the integer left, right and query buffers. -/
structure Buffers {p : ℕ} (a b : Fin p → ℤ) (left right out : ℕ) (m : Memory ℚ) : Prop where
  leftBase : m.index 10 = left
  rightBase : m.index 11 = right
  outBase : m.index 12 = out
  count : m.index 13 = p
  leftValue : ∀ i, m.data (left+i.val) = (a i : ℚ)
  rightValue : ∀ i, m.data (right+i.val) = (b i : ℚ)

theorem Buffers.stable {p left right out : ℕ} (a b : Fin p → ℤ) (hL : 5 < left)
    (hLR : left+p ≤ right) : Stable (Buffers a b left right out) := by
  constructor
  · intro m h r hr v
    refine ⟨h.leftBase,h.rightBase,h.outBase,h.count,?_,?_⟩
    · intro i
      simpa [show left+i.val ≠ r by omega] using h.leftValue i
    · intro i
      simpa [show right+i.val ≠ r by omega] using h.rightValue i
  · intro m h v
    refine ⟨?_,?_,?_,?_,h.leftValue,h.rightValue⟩
    · simpa using h.leftBase
    · simpa using h.rightBase
    · simpa using h.outBase
    · simpa using h.count

theorem Stable.combine {F G : Memory ℚ → Prop} (hF : Stable F) (hG : Stable G) :
    Stable (fun m => F m ∧ G m) :=
  ⟨fun m h r hr v => ⟨hF.scalar m h.1 r hr v,hG.scalar m h.2 r hr v⟩,
   fun m h v => ⟨hF.counter m h.1 v,hG.counter m h.2 v⟩⟩

/-- Caller-owned inputs that survive a complete scan of the two source arrays. -/
def PreservedByQuery {p : ℕ} (a b : Fin p → ℤ) (left right out : ℕ)
    (F : Memory ℚ → Prop) : Prop :=
  ∀ j n m t, F m → QueryPrefix a b j n m left right out p t → F t

/-- A sign subroutine reads any stored integer row, returning the signed answer
in scalar 2 and preserving the two private scalar and address registers. -/
def ReadsSign {p : ℕ} (code : Block) (oracle : (Fin p → ℤ) → Bool) (out bound : ℕ)
    (P : ℚ → Prop) (frame : Memory ℚ → Prop) (allowed : (Fin p → ℤ) → Prop) : Prop :=
  ∀ (row : Fin p → ℤ), allowed row → ∀ m, m.AllData P → frame m →
    (∀ i, m.data (out+i.val) = (row i : ℚ)) →
    ∃ t time, time ≤ bound ∧ Block.Eval (Memory.AllData P) code m time t ∧ frame t ∧
      t.data 0 = m.data 0 ∧ t.data 1 = m.data 1 ∧
      t.index 0 = m.index 0 ∧ t.index 1 = m.index 1 ∧
      t.data 2 = ((if oracle row then 1 else -1 : ℤ) : ℚ)

/-- The concrete query writer produces every signed coordinate for the next test
and preserves all persistent bisection registers and inputs. -/
theorem materialize_row_at {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (k left right out : ℕ) (hL : 5 < left) (hLR : left+p ≤ right) (hRO : right+p ≤ out)
    (P : ℚ → Prop) (W : ℤ) (hW : 0 ≤ W) (ha : ∀ i, |a i| ≤ W) (hb : ∀ i, |b i| ≤ W)
    (hP : ∀ n : ℤ, |n| ≤ (2:ℤ)^k * (2*W+1) → P n)
    (F : Memory ℚ → Prop) (hF : PreservedByQuery a b left right out F)
    (j : ℕ) (hj : j<k) (m : Memory ℚ)
    (h : At oracle a b k P (fun z => Buffers a b left right out z ∧ F z) j m) :
    ∃ u, Block.Eval (Memory.AllData P) queryArrayBlock m (12*p+5) u ∧
      At oracle a b k P (fun z => Buffers a b left right out z ∧ F z) j u ∧
      ∀ i : Fin p, u.data (out+i.val) =
        (dyadicQuery a b j (dyadicSearch oracle a b j).numerator i : ℚ) := by
  let n := (dyadicSearch oracle a b j).numerator
  let q := dyadicQuery a b j n
  have hpow : (2:ℤ)^j ≤ 2^k := pow_le_pow_right₀ (by decide) hj.le
  have hn : |n| ≤ 2^k := (dyadicSearch_numerator_lt oracle a b j).le.trans hpow
  have hmag : (2:ℤ)^k*W ≤ (2:ℤ)^k*(2*W+1) :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  have hsa (i : Fin p) : P (((2:ℤ)^j*a i : ℤ) : ℚ) := by
    apply hP
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by decide) _)]
    exact (mul_le_mul hpow (ha i) (abs_nonneg _) (by positivity)).trans hmag
  have hsb (i : Fin p) : P ((n*b i : ℤ) : ℚ) := by
    apply hP
    rw [abs_mul]
    exact (mul_le_mul hn (hb i) (abs_nonneg _) (by positivity)).trans hmag
  have hsq (i : Fin p) : P (q i : ℚ) := by
    apply hP
    exact (dyadicQuery_coeff_le a b j n (dyadicSearch_numerator_lt oracle a b j).le i).trans
      (mul_le_mul hpow (by linarith [ha i,hb i]) (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity))
  obtain ⟨u,eu,doneRows⟩ := queryArrayBlock_spec a b j n P m h.safe left right out hL hLR hRO
    h.inputs.1.leftBase h.inputs.1.rightBase h.inputs.1.outBase h.inputs.1.count h.numerator h.denominator
    h.inputs.1.leftValue h.inputs.1.rightValue hsa hsb hsq
  have f : Buffers a b left right out u := by
    refine ⟨(doneRows.indexFrame 10 (by omega)).trans h.inputs.1.leftBase,
      (doneRows.indexFrame 11 (by omega)).trans h.inputs.1.rightBase,
      (doneRows.indexFrame 12 (by omega)).trans h.inputs.1.outBase,
      (doneRows.indexFrame 13 (by omega)).trans h.inputs.1.count,?_,?_⟩
    · intro i
      exact (doneRows.dataFrame _ (by omega) (by have := i.isLt; omega)).trans (h.inputs.1.leftValue i)
    · intro i
      exact (doneRows.dataFrame _ (by omega) (by have := i.isLt; omega)).trans (h.inputs.1.rightValue i)
  refine ⟨u,eu,?_,fun i => doneRows.result i i.isLt⟩
  exact ⟨eu.safe_end,⟨f,hF j n m u h.inputs.2 doneRows⟩,
    (doneRows.indexFrame 0 (by omega)).trans h.limit,
    (doneRows.indexFrame 1 (by omega)).trans h.cursor,
    (doneRows.dataFrame 0 (by omega) (by omega)).trans h.numerator,
    (doneRows.dataFrame 1 (by omega) (by omega)).trans h.denominator⟩

/-- Exact affine rows passed to the sign subroutine, with all materialization costs
added to its own cost. -/
theorem materialize_answers {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (k B left right out : ℕ) (hL : 5 < left) (hLR : left+p ≤ right) (hRO : right+p ≤ out)
    (P : ℚ → Prop) (W : ℤ) (hW : 0 ≤ W) (ha : ∀ i, |a i| ≤ W) (hb : ∀ i, |b i| ≤ W)
    (hP : ∀ n : ℤ, |n| ≤ (2:ℤ)^k * (2*W+1) → P n)
    (F : Memory ℚ → Prop) (hF : PreservedByQuery a b left right out F) (code : Block)
    (allowed : (Fin p → ℤ) → Prop)
    (hallowed : ∀ j < k, allowed (dyadicQuery a b j (dyadicSearch oracle a b j).numerator))
    (hr : ReadsSign code oracle out B P (fun m => Buffers a b left right out m ∧ F m) allowed) :
    Answers (.seq queryArrayBlock code) oracle a b k (12*p+5+B) P (fun m => Buffers a b left right out m ∧ F m) := by
  intro j hj m h
  obtain ⟨u,eu,hu,rows⟩ := materialize_row_at oracle a b k left right out hL hLR hRO P W hW ha hb hP F hF j hj m h
  obtain ⟨t,time,ht,et,ft,hnum,hden,hprec,hctr,hbit⟩ :=
    hr _ (hallowed j hj) u eu.safe_end hu.inputs rows
  refine ⟨t,(12*p+5)+time,by omega,eu.seq et,?_,hbit⟩
  exact ⟨et.safe_end,ft,hprec.trans hu.limit,hctr.trans hu.cursor,
    hnum.trans hu.numerator,hden.trans hu.denominator⟩

/-- Uniform compiled bisection with no abstract cost for forming its oracle queries.
Each iteration makes one sign call and writes all p integer coordinates. -/
theorem materialized_search_eval {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (k B left right out : ℕ) (hL : 5 < left) (hLR : left+p ≤ right) (hRO : right+p ≤ out)
    (P : ℚ → Prop) (W : ℤ) (hW : 0 ≤ W) (ha : ∀ i, |a i| ≤ W) (hb : ∀ i, |b i| ≤ W)
    (hP : ∀ n : ℤ, |n| ≤ (2:ℤ)^k * (2*W+1) → P n)
    (F : Memory ℚ → Prop) (stable : Stable F) (hF : PreservedByQuery a b left right out F) (code : Block)
    (allowed : (Fin p → ℤ) → Prop)
    (hallowed : ∀ j < k, allowed (dyadicQuery a b j (dyadicSearch oracle a b j).numerator))
    (hr : ReadsSign code oracle out B P (fun m => Buffers a b left right out m ∧ F m) allowed) (m : Memory ℚ)
    (hm : m.AllData P) (hbuf : Buffers a b left right out m) (henv : F m) (hprec : m.index 0 = k) :
    ∃ t time, time ≤ k*(12*p+5+B+6)+4 ∧
      Block.Eval (Memory.AllData P) (searchBlock (.seq queryArrayBlock code)) m time t ∧
      At oracle a b k P (fun m => Buffers a b left right out m ∧ F m) k t := by
  have hsmall : ∀ n : ℤ, |n| ≤ 2^k → P n := by
    intro n hn
    apply hP
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ 2*W+1 by omega) (pow_nonneg (by decide : (0:ℤ) ≤ 2) k)
    exact hn.trans (by simpa using hh)
  exact searchBlock_eval oracle a b k (12*p+5+B) P hsmall _
    ((Buffers.stable a b hL hLR).combine stable) (.seq queryArrayBlock code)
    (materialize_answers oracle a b k B left right out hL hLR hRO P W hW ha hb hP F hF code allowed hallowed hr)
    m hm ⟨hbuf,henv⟩ hprec

end DyadicRAM
end Compression
end LinearProgramming
end Optimization
end OAI
