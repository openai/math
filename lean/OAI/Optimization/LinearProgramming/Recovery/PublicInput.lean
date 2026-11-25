import OAI.Optimization.LinearProgramming.Recovery.SlackRAM
import OAI.Optimization.LinearProgramming.RAM.FrameHeaders
import OAI.Optimization.LinearProgramming.PrimalDual.CopyRAM
import OAI.Optimization.LinearProgramming.PrimalDual.InputSize

/-! A normal-entry prefix for the principal RAM. The unfixed A,b tape starts at scalar
zero, so it is copied into a protected window before any numeric scratch is initialized. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PublicInput

open RAM RAM.Tape RAM.Call Polynomial
open _root_.OAI.Optimization.LinearProgramming.Geometry

/-- The original input is stored above all scalar scratch. The generated slack matrix
immediately follows that original window. -/
def words (m d : ℕ) := m*d+m
def sourceBase (m d : ℕ) := 256+words m d
def matrixBase (m d : ℕ) := sourceBase m d+words m d

def headers : HeaderPlan 36 :=
  let m : AddressTerm 36 := .reg 28
  let d : AddressTerm 36 := .reg 29
  let L : AddressTerm 36 := .reg 2
  [(28,.reg 0),(29,.reg 1),(2,m*d+m),(24,(.val 256)+L),(31,m+.val 1),(33,d+.val 1),
   (35,(.reg 24)+L),(0,.val 0),(1,.reg 24),(3,.val 0)]

def program : Block := .seq (HeaderPlan.code 40 headers) (.seq (PrimalDual.copyWindow false)
  (.seq (.op (.const 1 0)) SlackRAM.program))

noncomputable def stepBound (m d : ℕ) := headers.budget.eval (m+d) +
  (7*words m d+1+1+uniformTableTime (m+1) (d+1) (SlackRAM.cellPolynomial.eval (m+d+1)))

private def inputEnv (m d : ℕ) (i : Fin 36) := ([m,d][i.val]?).getD 0

private theorem env_bound (m d : ℕ) (i : Fin 36) : inputEnv m d i ≤ m+d := by
  by_cases h0 : i.val=0
  · simp [inputEnv,h0]
  by_cases h1 : i.val=1
  · simp [inputEnv,h1]
  · have h : 2 ≤ i.val := by omega
    have hl : [m,d].length ≤ i.val := by simpa only [List.length_cons,List.length_nil] using h
    simp [inputEnv,List.getElem?_eq_none hl]

private theorem headers_values (m d : ℕ) :
    let ix := headers.output (inputEnv m d)
    ix 0=0 ∧ ix 1=sourceBase m d ∧ ix 2=words m d ∧ ix 3=0 ∧ ix 24=sourceBase m d ∧
      ix 28=m ∧ ix 29=d ∧ ix 31=m+1 ∧ ix 33=d+1 ∧ ix 35=matrixBase m d := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- One compiled code block starts from exactly the comparator's public input. Its output
retains the original input as well as the complete dense (β,u)↦(β,βb−Au) tableau. -/
theorem program_spec {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K)
    (P : K → Prop) (h0 : P 0) (h1 : P 1) (hneg : ∀ x,P x → P (-x))
    (hinput : ∀ k : ℕ,P ((lpInput A b)[k]?.getD 0)) :
    ∃ t c, c ≤ stepBound m d ∧ Block.Eval (Memory.AllData P) program (start [m,d] (lpInput A b)).memory c t ∧
      SlackRAM.InputAt t (sourceBase m d) A b ∧
      uniformRect (m+1) (d+1) (matrixBase m d) t=slackColumns A b ∧
      t.index 24=sourceBase m d ∧ t.index 28=m ∧ t.index 29=d ∧
      t.index 31=m+1 ∧ t.index 33=d+1 ∧ t.index 35=matrixBase m d := by
  let s := (start [m,d] (lpInput A b)).memory
  have hs : s.AllData P := hinput
  obtain ⟨u,k,e,hk,ud,ui⟩ := headers.correct 40 (by decide) s (inputEnv m d) (fun _=>rfl) hs
  obtain ⟨x0,x1,x2,x3,x24,x28,x29,x31,x33,x35⟩ := headers_values m d
  have u0 := (ui 0).trans x0; have u1 := (ui 1).trans x1
  have u2 := (ui 2).trans x2; have u3 := (ui 3).trans x3
  obtain ⟨v,ev,copy,_,vi⟩ := PrimalDual.copyWindow_correct false (words m d) 0 (sourceBase m d)
    u e.safe_end u0 u1 u2 u3 (Or.inl (by simp [sourceBase])) (by simp [sourceBase])
  let w := v.putData 1 (0 : K)
  have sw : w.AllData P := by
    intro p
    by_cases hp : p=1
    · subst p; simpa [w] using h0
    · simpa [w,Memory.putData_ne _ hp] using ev.safe_end p
  have ew : Block.Eval (Memory.AllData P) (.op (.const 1 0)) v 1 w := by
    have before : v.AllData P := fun j=>ev.safe_end j
    have after : (v.putData 1 ((0 : ℚ) : K)).AllData P := by
      simpa only [Rat.cast_zero] using (show (v.putData 1 (0 : K)).AllData P from sw)
    simpa only [Rat.cast_zero] using Block.Eval.op_const (safe:=Memory.AllData P) v 1 0 before after
  have w24 := (vi 24 (by decide)).trans ((ui 24).trans x24)
  have w28 := (vi 28 (by decide)).trans ((ui 28).trans x28)
  have w29 := (vi 29 (by decide)).trans ((ui 29).trans x29)
  have w31 := (vi 31 (by decide)).trans ((ui 31).trans x31)
  have w33 := (vi 33 (by decide)).trans ((ui 33).trans x33)
  have w35 := (vi 35 (by decide)).trans ((ui 35).trans x35)
  have lo : 7 ≤ sourceBase m d := by unfold sourceBase;omega
  have hw : SlackRAM.InputAt w (sourceBase m d) A b := by
    apply SlackRAM.inputAt_of_copy
    intro i hi
    have he : (lpInput A b)[i]?=some ((lpInput A b)[i]) := List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩
    have hi' : i < words m d := by simpa [PrimalDual.lpInput_length,words] using hi
    have hv := copy i hi'
    change v.data (sourceBase m d+i)=u.data (0+i) at hv
    have us (i : ℕ) : u.data i=((lpInput A b)[i]?).getD 0 := congrFun ud i
    simp only [Nat.zero_add] at hv
    rw [us] at hv
    rw [show w.data (sourceBase m d+i)=v.data (sourceBase m d+i) by exact Memory.putData_ne _ (by omega) _]
    rw [hv,he]; rfl
  obtain ⟨t,c,hc,et,hB,td,ti⟩ := SlackRAM.program_spec A b P h0 h1 hneg w sw (by simp [w])
    w24 w28 w29 w31 w33 w35 hw lo (by rfl)
  have tr := e.seq (ev.seq (ew.seq et))
  have hx := hk.trans (headers.cost_le _ _ (env_bound m d))
  refine ⟨t,_,?_,tr,?_,hB,(ti 24 (Or.inr (by decide))).trans w24,
    (ti 28 (Or.inr (by decide))).trans w28,(ti 29 (Or.inr (by decide))).trans w29,
    (ti 31 (Or.inl (Or.inl rfl))).trans w31,(ti 33 (Or.inl (Or.inr (Or.inl rfl)))).trans w33,
    (ti 35 (Or.inl (Or.inr (Or.inr rfl)))).trans w35⟩
  · unfold stepBound; omega
  · have read (i : ℕ) (h : i < words m d) : t.data (sourceBase m d+i)=w.data (sourceBase m d+i) :=
      td _ (Or.inr (by omega)) (Or.inl (by unfold matrixBase; omega))
    constructor
    · intro i j
      have hlt := rectOffset_lt i j
      exact (read _ (by unfold words; omega)).trans (hw.1 i j)
    · intro i
      exact (read _ (by unfold words; have := i.isLt; omega)).trans (hw.2 i)

end PublicInput
end Recovery
end LinearProgramming
end Optimization
end OAI
