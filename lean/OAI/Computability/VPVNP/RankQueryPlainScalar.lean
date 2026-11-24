import OAI.Computability.VPVNP.RankQueryGramScalarSpace

/-!
# Scalar-entry routine for an ordinary determinant

The Cramer minors of Appendix D.2 have constant entries in the polynomial
variable. At degree zero this routine reads the chosen entry once. At positive
degree it emits a zero scalar. Both arms restore the binary index bank and
apply the sign requested by the Schur factor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.PlainScalar

open RAMTape BurstRAM Dispatch Engine UniversalCountStack
open GramScalar (Small Registers bank wordBank outWord literalPorts raw_word)
open SliceArithmetic (Vector)

variable {K : Type}

/-- Route the Macaulay row and column inputs to the query registers and the entry result to the
scalar accumulator. -/
def readPorts : MacaulayRead.Port K → GramScalar.Port K
  | .row => .words (.reg (Code.inReg capacity 0))
  | .col => .words (.reg (Code.inReg capacity 1))
  | .result => .mul (.inr .acc)
  | .aux k => .aux k

theorem readPorts_injective : Function.Injective (readPorts (K := K)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [readPorts,Code.inReg,Fin.ext_iff]

/-- Register six contains the zero word. The branch writes the degree-zero
indicator into output word zero, using the same bank as the Gram accessor. -/
def degreeTest : RegCode (14+capacity) :=
  .test (Code.inReg capacity 2) (Code.inReg capacity 6)
    (.lit (Code.outReg capacity 0) 1) (.lit (Code.outReg capacity 0) 0)

/-- Select the matrix-entry reader on tag one and the zero-scalar writer on every other tag. -/
def arm (read : FiniteRoutine (MacaulayRead.Port K)) (tag : ℕ) : FiniteRoutine (GramScalar.Port K) :=
  if tag = 1 then read.onPorts readPorts else (SliceArithmeticConstant.machine false).onPorts literalPorts

/-- Test the requested coefficient degree, read the entry or emit zero, then apply the
requested sign. -/
def machine (read : FiniteRoutine (MacaulayRead.Port K)) (negative : Bool) : FiniteRoutine (GramScalar.Port K) :=
  ((degreeTest.compile.onPorts GramScalar.Port.words).followedBy (TagRouter.select (outWord 0) 1 (arm read))).followedBy
    (GramScalar.sign negative)

/-- Regard a constant matrix as a polynomial matrix by putting each entry in degree zero. -/
def entry {F : Type*} [Zero F] {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Entry n F :=
  fun i j z => if z = 0 then M i j else 0

/-- Step bound for testing the coefficient degree on binary words of width `w`. -/
def testClock (w : ℕ) := 200*(w+1)^2
/-- Step budget for the degree test, scalar read or zero output, and sign adjustment. -/
def clock (w v e B : ℕ) := testClock w + 2 + (B + 7*(e*v)+3) +
    (5*(e*v)+2+SliceArithmetic.AddCall.callCap e v+1)
/-- Stack-space budget for the degree test and scalar reader followed by sign adjustment. -/
def space (w v e A S : ℕ) := max (A+testClock w) S + 7*(e*v)+3 +
    (5*(e*v)+2+SliceArithmetic.AddCall.callCap e v+1)

variable [DecidableEq K] {w v p e n d B S A : ℕ} [Fact p.Prime] [NeZero e] {c : Vector p e}

theorem machine_bounded (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin n) (Scalar c))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v) (hw₁ : 1 ≤ w)
    (i j : Fin n) (z : ℕ) (negative : Bool) (persist : Word w) (rs : Registers w)
    (hr : ∀ a, (rs (Code.inReg capacity a)).val = gramInput i j z n a)
    (aux : Stacks K) (hs : ready aux)
    (start : ∀ a, (bank (wordBank persist rs) (GramRead.arithmeticBank v c [] []) aux a).length ≤ A) :
    ∃ t ≤ clock w v e B, ∃ rs' aux', ready aux' ∧
      (∀ a, rs' (Code.inReg capacity a) = rs (Code.inReg capacity a)) ∧
      (machine read negative).BoundedRun (space w v e A S) t
        (bank (wordBank persist rs) (GramRead.arithmeticBank v c [] []) aux)
        (bank (wordBank persist rs') (GramRead.arithmeticBank v c []
          (scalar v (if negative then -entry M i j z else entry M i j z))) aux') := by
  let regs := degreeTest.exec rs
  let rb := wordBank persist regs
  let idx := Code.outReg capacity 0
  let A₀ := A + testClock w
  let A₁ := max A₀ S + 7*(e*v)+3
  have h01 : A₀ ≤ A₁ := by dsimp [A₁]; omega
  have h12 : A₁ ≤ space w v e A S := Nat.le_add_right ..
  have hcmp : rs (Code.inReg capacity 2) = rs (Code.inReg capacity 6) ↔ z = 0 := by
    rw [Fin.ext_iff, hr, hr]; rfl
  have hregs : regs = Function.update rs idx (Fin.ofNat _ (if z = 0 then 1 else 0)) := by
    by_cases hz : z = 0
    · simp [regs,idx,degreeTest,RegCode.exec,hcmp.mpr hz,hz]
    · have hne : rs (Code.inReg capacity 2) ≠ rs (Code.inReg capacity 6) := fun hh => hz (hcmp.mp hh)
      simp [regs,idx,degreeTest,RegCode.exec,hne,hz]
  have keep (a : Fin 8) : regs (Code.inReg capacity a) = rs (Code.inReg capacity a) := by
    rw [hregs, Function.update_of_ne]
    intro he
    have h := congrArg Fin.val he
    change a.val = 8 at h
    omega
  have flag : rb (.reg idx) = UniversalCountStack.digits w (if z = 0 then 1 else 0) := by
    change wordBits (regs idx) = _
    rw [hregs,Function.update_self]; rfl
  obtain ⟨t₀,ht₀,h₀⟩ := degreeTest.compile_runs Fin.elim0 persist rs
  change t₀ ≤ 2*(100*(w+1)^2) at ht₀
  have htest : t₀ ≤ testClock w := by simpa [testClock,← Nat.mul_assoc] using ht₀
  have load : (degreeTest.compile.onPorts (GramScalar.Port.words (K := K))).Runs t₀
      (bank (wordBank persist rs) (GramRead.arithmeticBank v c [] []) aux)
      (bank rb (GramRead.arithmeticBank v c [] []) aux) := by
    apply degreeTest.compile.runs_onPorts_framed (fun _ _ h => GramScalar.Port.words.inj h) h₀
    · intro k; rfl
    · intro k; rfl
    · intro k hk; cases k <;> first | rfl | exact (hk _ rfl).elim
  have hload := spaceRun_of_steps (cap := A₀) load (fun k => Nat.add_le_add (start k) htest)
  by_cases hz : z = 0
  · rw [ite_eq_left hz] at flag
    obtain ⟨t₁,ht₁,out,ho,hcall⟩ := hc i j aux hs
    have first : rb (.reg (Code.inReg capacity 0)) = UniversalCountStack.digits w i.val := by
      change wordBits (regs _) = _
      rw [keep,raw_word,hr]; rfl
    have second : rb (.reg (Code.inReg capacity 1)) = UniversalCountStack.digits w j.val := by
      change wordBits (regs _) = _
      rw [keep,raw_word,hr]; rfl
    have hcS : S ≤ A₁ := by dsimp [A₁]; omega
    have branch : (arm read 1).BoundedRun A₁ t₁ (bank rb (GramRead.arithmeticBank v c [] []) aux)
        (bank rb (GramRead.arithmeticBank v c [] (scalar v (M i j))) out) := by
      change (read.onPorts readPorts).BoundedRun _ _ _ _
      apply FiniteRoutine.BoundedRun.framed readPorts_injective (hcall.enlarge hcS) (fun a => (hload.final_cap a).trans h01)
      · intro a; cases a <;> first | exact first | exact second | rfl
      · intro a; cases a <;> first | exact first | exact second | rfl
      · intro a ha
        cases a with
        | mul a => rcases a with a|a
                   · rfl
                   · cases a <;> first | rfl | exact (ha .result rfl).elim
        | aux a => exact (ha (.aux a) rfl).elim
        | _ => rfl
    have select := TagRouter.digits_bounded (outWord 0) (arm read) hw₁ (by decide : 1 < 2^1) _ _ flag branch
    obtain ⟨t₂,ht₂,hsign⟩ := GramScalar.sign_runs hw negative (M i j) rb out
    have hfinal := spaceRun_of_steps (cap := space w v e A S) hsign (fun a => Nat.add_le_add (branch.final_cap a) ht₂)
    refine ⟨t₀+(2*1+t₁)+t₂,by unfold clock; omega,regs,out,ho,keep,?_⟩
    rw [entry,ite_eq_left hz]
    exact (((FiniteRoutine.BoundedRun.enlarge hload h01).followedBy select).enlarge h12).followedBy hfinal
  · rw [ite_eq_right hz] at flag
    have hzero := GramScalar.zero_runs (c := c) hw rb aux
    have branch : (arm read 0).BoundedRun A₁ (7*(e*v)+3) (bank rb (GramRead.arithmeticBank v c [] []) aux)
        (bank rb (GramRead.arithmeticBank v c [] (scalar v (0 : Scalar c))) aux) :=
      spaceRun_of_steps hzero (fun a => by have h := hload.final_cap a; dsimp [A₁]; omega)
    have select := TagRouter.digits_bounded (outWord 0) (arm read) hw₁ (by decide : 0 < 2^1) _ _ flag branch
    obtain ⟨t₂,ht₂,hsign⟩ := GramScalar.sign_runs hw negative (0 : Scalar c) rb aux
    have hfinal := spaceRun_of_steps (cap := space w v e A S) hsign (fun a => Nat.add_le_add (branch.final_cap a) ht₂)
    refine ⟨t₀+(2*1+(7*(e*v)+3))+t₂,by unfold clock; omega,regs,aux,hs,keep,?_⟩
    rw [entry,ite_eq_right hz]
    exact (((FiniteRoutine.BoundedRun.enlarge hload h01).followedBy select).enlarge h12).followedBy hfinal

end RankQuery.Stack.PlainScalar

end VPVNP
end Computability
end OAI
