import OAI.ThreeFlat.RAM.PhysicalReaders
import OAI.ThreeFlat.RAM.ExpressionRowWords

namespace OAI
/-! # Fixed native descriptor program for all physical blocks -/

namespace ThreeFlat.RAM.PhysicalPinsExpr

open scoped Fin.CommRing

open Diagonal Diagonal.BoundaryWire DescriptorExpr Computability.VPVNP.BurstRAM PrivateRAM BitLayout

namespace Program

variable {w : ℕ}

abbrev extraIndex (i : Fin 20) : Fin (2+(5+20)) := Fin.natAdd 2 (Fin.natAdd 5 i)
abbrev shapeIndex (i : Param) : Fin (2+(5+20)) := extraIndex (Fin.natAdd 9 i.index)

def registers : GuardedDescriptor.Inputs (Fin 10) := ⟨0,1,2,3,4,5,6,7,8,9⟩

def arg (i : Fin 10) : Term w (2+(5+20)) 1 :=
  Fin.cases (.result 0) (fun j => .parameter (extraIndex (j.castAdd 11))) i

/-- This ROM references only the current address and twenty public words. -/
def program (w : ℕ) : Term w (2+(5+20)) 1 :=
  GuardedDescriptor.bindParams registers (lookups shapeIndex) arg

/-- The emitter's number of registers and instructions is determined entirely
by these four closed formulas and the fixed guarded-record assembly. -/
def bindCount :=
  (copyFormula (.reg 1) (.reg 0) : Formula 2).work +
  (pinFormula (.reg 1) (.reg 0) : Formula 2).work +
  (guardFormula false (.reg 1) (.reg 0) : Formula 2).work +
  (guardFormula true (.reg 1) (.reg 0) : Formula 2).work + 105 + 9

set_option maxRecDepth 12000 in
theorem bindCount_eq : bindCount=2107 := by decide

set_option maxRecDepth 12000 in
theorem program_binds (w : ℕ) : (program w).binds = bindCount := by
  rw [program,GuardedDescriptor.binds_bindParams,GuardedDescriptor.binds_compile]
  simp only [lookups,Formula.binds_compile]
  have h : ∑ j : Fin 10, (arg (w:=w) j).binds = 9 := by
    rw [Fin.sum_univ_succ]
    have each (i : Fin 9) : (arg (w:=w) i.succ).binds=1 := by
      simp [arg,Term.parameter,Term.binds]
    simp [arg,Term.parameter,Term.binds]
  rw [h]
  rfl

theorem program_labels (w : ℕ) : (program w).labels=3*bindCount+1 := by
  rw [Term.labels_eq,program_binds]

def shapeWords (s : Shape) : Fin 11 → Word w :=
  ![s.advice,s.teamBits,s.timeBits,s.parameterBits,s.bits,((s.inside+1 : ℕ) : Word w),s.teams,s.period,
    s.last,s.parameterBase,s.templateBase]

def extraWords {F : Type*} [CommSemiring F] (s : Shape)
    (N : BitNetwork F (s.area+2*s.halfBits)) (code : FieldCode F w) (base : ℕ) :
    Fin 20 → Word w :=
  Fin.append (α := Word w) ![base,((s.area+2*s.halfBits : ℕ) : Word w),N.cells,N.internal,s.halfBits,
    pinWidth s.chunks s.bits s.advice, hiddenWidth s.chunks s.bits s.last s.inside,
    code.encode 0,code.encode 1] (shapeWords s)

variable {F : Type*} [CommSemiring F] (s : Shape) [NeZero s.period]
variable (N : BitNetwork F (s.area+2*s.halfBits)) (code : FieldCode F w) (base : ℕ)

omit [NeZero s.period] in
private theorem shapeWord_eq (data : Fin (2+(5+20)) → Word w)
    (ext : ∀ i, data (extraIndex i) = extraWords s N code base i) :
    data ∘ shapeIndex = fun p => (s.words p : Word w) := by
  funext p
  unfold shapeIndex
  rw [Function.comp_apply,ext]
  cases p <;> rfl

set_option maxRecDepth 12000 in
omit [NeZero s.period] in
theorem eval (mem : Memory w) (data : Fin (2+(5+20)) → Word w)
    (ext : ∀ i,data (extraIndex i)=extraWords s N code base i) (a : ℕ) :
    let R := readers s mem
    ((program w).eval data mem (fun _ => (a : Word w))) =
    GuardedDescriptor.word (GuardedDescriptor.recordInputs N code (pinWidth s.chunks s.bits s.advice)
      (hiddenWidth s.chunks s.bits s.last s.inside) s.halfBits base a) R.copy R.pin R.left R.right := by
  simp only [program,GuardedDescriptor.bindParams, Term.eval_instantiate,GuardedDescriptor.eval_compile]
  have hd := shapeWord_eq s N code base data ext
  simp only [lookups,Formula.eval_compile,hd]
  congr 1
  · change GuardedDescriptor.Inputs.mk (a : Word w)
        (data (extraIndex 0)) (data (extraIndex 1)) (data (extraIndex 2))
        (data (extraIndex 3)) (data (extraIndex 4)) (data (extraIndex 5))
        (data (extraIndex 6)) (data (extraIndex 7)) (data (extraIndex 8)) = _
    simp only [ext]
    rfl

def H (params : Fin s.parameterBits → Bool) :=
  ApproximateNetwork.network (fun i => ApproximateImage.select i.val params) (fun i => s.slots i.val)
    s.choice N s.retained

/-- The generated network's external coefficients are the actual approximating
matrix product with the selected block schedule. -/
theorem H_eval {K : Type*} [Field K] (s : Shape) [NeZero s.period]
    (N : BitNetwork K (s.area+2*s.halfBits)) (params : Fin s.parameterBits → Bool)
    (D : Fin s.advice → Bool) (x y : State s.chunks s.bits) :
    (H s N params).eval (pinBits D x y) =
      (List.ofFn fun i => ∑ f, physicalFixing (s.slots i.val) (s.choice i) f
        (ApproximatePort.catalyst N (ApproximateImage.select i.val params) D f)).prod x y :=
  ApproximateNetwork.eval _ _ _ N s.retained s.retained_spec D x y

theorem row (params : Fin s.parameterBits → Bool) (mem : Memory w)
    (data : Fin (2+(5+20)) → Word w)
    (ext : ∀ i,data (extraIndex i)=extraWords s N code base i)
    (R : GuardedDescriptor.Reads (readers s mem) N (s.input params)
        (s.guardSource false) (s.guardSource true) code)
    (i : Fin (s.last+1)) (u : Fin (N.cells+s.halfBits)) (j : Fin 11)
    (sourceFit : 2+(s.area+2*s.halfBits)+N.internal < 2^w) (widthFit : N.cells+s.halfBits < 2^w)
    (h11 : 11<2^w) (fit : GuardedDescriptor.recordAddress base N.cells s.halfBits i.val u.val j.val<2^w) :
    let address := GuardedDescriptor.recordAddress base N.cells s.halfBits i.val u.val j.val
    (program w).eval data mem (fun _ => (address : Word w)) =
      record (H s N params) code (finProdFinEquiv (i,u)) j := by
  dsimp only
  rw [eval s N code base mem data ext]
  exact GuardedDescriptor.word_record N (s.input params) (s.guardSource false)
    (s.guardSource true) code (readers s mem) R base i u j sourceFit widthFit h11 fit

end Program
end ThreeFlat.RAM.PhysicalPinsExpr

end OAI
