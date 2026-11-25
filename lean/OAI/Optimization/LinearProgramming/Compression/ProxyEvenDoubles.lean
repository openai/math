import OAI.Optimization.LinearProgramming.RAM.CallHeader
import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.Compression.ServiceAddressPlan

/-! Set the four numerical parameter words and the odd physical source cursor. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceFill

variable {K : Type*}

open RAM GeneratorTable

def doubleWord (s : Memory K) (dst src : ℕ) : Memory K :=
  (s.putIndex dst (2*s.index src)).putIndex 5 (s.index src)

private theorem memory_ext {s t : Memory K} (h₁ : s.data = t.data) (h₂ : s.index = t.index) :
    s = t := by
  cases s; cases t; cases h₁; cases h₂; rfl

theorem doubleWord_eval {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (dst src : ℕ) (hs : s.AllData P)
    (hd : dst ≠ 5) (hsrc : src ≠ 5) (hne : src ≠ dst) :
    Block.Eval (Memory.AllData P) (RAM.Call.doubleHeaderEntry dst src) s (4*s.index src+3)
      (doubleWord s dst src) := by
  obtain ⟨t, run, dest, count, frame, dat⟩ := RAM.Call.doubleHeaderEntry_run (P := P) s dst src hs hd hsrc hne
  have eq : t = doubleWord s dst src := by
    refine memory_ext (s := t) (t := doubleWord s dst src) dat ?_
    funext j
    by_cases h5 : j = 5
    · simpa [doubleWord, h5] using count
    by_cases hdst : j = dst
    · simpa [doubleWord, hdst, hd] using dest
    · simpa [doubleWord, h5, hdst] using frame j h5 hdst
  exact eq ▸ run

def doubleInputWords : Block :=
  .seq (RAM.Call.doubleHeaderEntry 0 107) <| .seq (RAM.Call.doubleHeaderEntry 2 105) <|
    .seq (RAM.Call.doubleHeaderEntry 4 111) <| .seq (RAM.Call.doubleHeaderEntry 6 109)
      (RAM.Call.doubleHeaderEntry 11 103)

def doubledInput (s : Memory K) : Memory K :=
  doubleWord (doubleWord (doubleWord (doubleWord (doubleWord s 0 107) 2 105) 4 111) 6 109) 11 103

private theorem doubleInputWords_eval {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (hs : s.AllData P) :
    Block.Eval (Memory.AllData P) doubleInputWords s
      (4*(s.index 107+s.index 105+s.index 111+s.index 109+s.index 103)+15) (doubledInput s) := by
  let a := doubleWord s 0 107
  let b := doubleWord a 2 105
  let c := doubleWord b 4 111
  let d := doubleWord c 6 109
  have e₁ := doubleWord_eval P s 0 107 hs (by decide) (by decide) (by decide)
  have e₂ := doubleWord_eval P a 2 105 hs (by decide) (by decide) (by decide)
  have e₃ := doubleWord_eval P b 4 111 hs (by decide) (by decide) (by decide)
  have e₄ := doubleWord_eval P c 6 109 hs (by decide) (by decide) (by decide)
  have e₅ := doubleWord_eval P d 11 103 hs (by decide) (by decide) (by decide)
  convert e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅))) using 1 <;> first | rfl | (simp [a,b,c,d,doubleWord]; omega)

private def evenCursorSetup : List AddressSet :=
  [.next 11 11, .next 13 11, .next 13 13, .fix 15 2]

def prepareEvenInput : Block := .seq doubleInputWords (addressPlan evenCursorSetup)

def preparedEvenInput (s : Memory K) : Memory K :=
  applyPlan evenCursorSetup (doubledInput s)

@[simp] theorem preparedEvenInput_data (s : Memory K) : (preparedEvenInput s).data = s.data :=
  applyPlan_data _ _

theorem prepareEvenInput_eval {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (hs : s.AllData P) :
    Block.Eval (Memory.AllData P) prepareEvenInput s
      (4*(s.index 107+s.index 105+s.index 111+s.index 109+s.index 103)+19) (preparedEvenInput s) := by
  have d := doubleInputWords_eval P s hs
  have a : Block.Eval (Memory.AllData P) (addressPlan evenCursorSetup) (doubledInput s) 4 (preparedEvenInput s) :=
    addressPlan_spec (fun f => ∀ j, P (f j)) _ _ d.safe_end
  convert d.seq a using 1
  rfl

theorem preparedEvenInput_words (s : Memory K) :
    let t := preparedEvenInput s
    t.index 0 = 2*s.index 107 ∧ t.index 2 = 2*s.index 105 ∧ t.index 4 = 2*s.index 111 ∧
    t.index 6 = 2*s.index 109 ∧ t.index 11 = 2*s.index 103+1 ∧
    t.index 13 = 2*s.index 103+3 ∧ t.index 15 = 2 ∧ t.index 105 = s.index 105 := by
  simp [preparedEvenInput,evenCursorSetup,applyPlan,AddressSet.apply,doubledInput,doubleWord]

theorem preparedEvenInput_frame (s : Memory K) (j : ℕ) (h : j ∉ ([0,2,4,5,6,11,13,15] : List ℕ)) :
    (preparedEvenInput s).index j = s.index j := by
  simp only [List.mem_cons, not_or] at h
  simp (disch := omega) [preparedEvenInput,evenCursorSetup,applyPlan,AddressSet.apply,doubledInput,doubleWord]

end ServiceFill
end Compression
end LinearProgramming
end Optimization
end OAI
