import OAI.Optimization.LinearProgramming.Compression.BinaryPacketPromote
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec OracleSpec.MinorLog NativePrice

/-- The physical optional-rational result format. Each rational payload is the sealed
canonical `encodeRat` word. This shape does not require the bit-stack arithmetic library. -/
def optionalRationalWord : Option ℚ → Word
  | none => [false]
  | some q => true :: encodeRat q

def captureFlatTag : Block := .seq (.op (.load 7 3)) (.seq (.op (.const 5 1)) (.op (.incr 3 3)))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Consume the leading optional-value tag while leaving the tagged payload readable. -/
theorem captureFlatTag_spec (m : Memory K) (flag : Bool) (w : Word) {P : K → Prop}
    (safe : m.AllData P) (h1 : P 1) (room : 10 ≤ m.index 3) (input : WordAt m (m.index 3) (flag::w)) :
    ∃ t, Block.Eval (Memory.AllData P) captureFlatTag m 3 t ∧ t.data 7=(flag.toNat:K) ∧
      t.data 5=1 ∧ t.index 37=m.index 37 ∧ t.index 3=m.index 3+1 ∧ WordAt t (t.index 3) w := by
  let a := m.putData 7 (m.data (m.index 3))
  let b := a.putData 5 1
  let t := b.putIndex 3 (b.index 3+1)
  obtain ⟨tag,rest⟩ := wordAt_cons.mp input
  have ld := Block.Eval.op_load m 7 3 safe (safe.putData 7 (safe _))
  have one : Block.Eval (Memory.AllData P) (.op (.const 5 1)) a 1 b := by
    simpa only [b,Rat.cast_one] using Block.Eval.op_const a 5 1 ld.safe_end
      (ld.safe_end.putData 5 (by simpa only [Rat.cast_one] using h1))
  have inc := Block.Eval.op_incr b 3 3 one.safe_end (one.safe_end.putIndex _ _)
  have endp : t.index 3=m.index 3+1 := by simp [t,b,a]
  refine ⟨t,ld.seq (one.seq inc),by simpa [t,b,a] using tag,by simp [t,b],by simp [t,b,a],endp,?_⟩
  rw [endp]
  apply rest.of_data
  intro i hi _; simp [t,b,a,show i ≠ 5 by omega,show i ≠ 7 by omega]

/-- The dispatcher needs a scalar comparison after both branches. Public scalar 0
and every already written address digit survive these final two writes. -/
def replyMark (success : Bool) : Block := .seq (.op (.const 5 (if success then 0 else 1)))
  (.op (.const 6 (if success then 1 else 0)))

theorem replyMark_spec (m : Memory K) (success : Bool) {P : K → Prop}
    (safe : m.AllData P) (h0 : P 0) (h1 : P 1) :
    ∃ t, Block.Eval (Memory.AllData P) (replyMark success) m 2 t ∧
      (t.data 5 < t.data 6 ↔ success=true) ∧ t.data 0=m.data 0 ∧ t.index=m.index := by
  cases success with
  | false =>
    let a := m.putData 5 1
    let t := a.putData 6 0
    have f : Block.Eval (Memory.AllData P) (.op (.const 5 1)) m 1 a := by
      simpa only [a,Rat.cast_one] using Block.Eval.op_const m 5 1 safe
        (safe.putData 5 (by simpa only [Rat.cast_one] using h1))
    have g : Block.Eval (Memory.AllData P) (.op (.const 6 0)) a 1 t := by
      simpa only [t,Rat.cast_zero] using Block.Eval.op_const a 6 0 f.safe_end
        (f.safe_end.putData 6 (by simpa only [Rat.cast_zero] using h0))
    exact ⟨t,f.seq g,by simp [t,a],by simp [t,a],rfl⟩
  | true =>
    let a := m.putData 5 0
    let t := a.putData 6 1
    have f : Block.Eval (Memory.AllData P) (.op (.const 5 0)) m 1 a := by
      simpa only [a,Rat.cast_zero] using Block.Eval.op_const m 5 0 safe
        (safe.putData 5 (by simpa only [Rat.cast_zero] using h0))
    have g : Block.Eval (Memory.AllData P) (.op (.const 6 1)) a 1 t := by
      simpa only [t,Rat.cast_one] using Block.Eval.op_const a 6 1 f.safe_end
        (f.safe_end.putData 6 (by simpa only [Rat.cast_one] using h1))
    exact ⟨t,f.seq g,by simp [t,a],by simp [t,a],rfl⟩

def TaggedReady (m : Memory ℚ) : Option ℚ → Prop
  | none => ¬m.data 5 < m.data 6
  | some q => m.data 5 < m.data 6 ∧ explicitValue (m.atPC 0) q

theorem explicitValue_preserve_output {m t : Memory ℚ} {q : ℚ} (h : explicitValue (m.atPC 0) q)
    (val : t.data 0=m.data 0) (idx : t.index=m.index) : explicitValue (t.atPC 0) q := by
  obtain ⟨qv,wn,wd,sg,nb,db⟩ := h
  exact ⟨val.trans qv,(congrFun idx 0).trans wn,(congrFun idx 1).trans wd,(congrFun idx 2).trans sg,
    fun i hi => (congrFun idx _).trans (nb i hi),fun i hi => (congrFun idx _).trans (db i hi)⟩

end Compression
end LinearProgramming
end Optimization
end OAI
