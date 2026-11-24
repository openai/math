import OAI.Computability.VPVNP.PairNativeOperandCompiler
import OAI.Computability.VPVNP.PairNativeGeometry

/-! # Native evaluation of a fixed vector from the eleven pair-stage operands

Register twelve retains the caller's private cache base. Results start at
register thirteen, in vector order. The final two instructions set the cache
write pointer and unit register for the consecutive private stores.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeOperands
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM LiveProgram
open scoped Fin.CommRing

variable {k : ℕ}

/-- Number of extra temporary slots above an operand's result slot. A geometry expression uses
its compiler's space bound and a prefix field uses zero. -/
def need : InputOperand → ℕ
  | .geometry e => RAMTape.PublicExprMachine.extra e
  | _ => 0

/-- Tick allowance for one vector entry, using the expression cost for a geometry operand and
one copy for either prefix operand. -/
def fieldCost (w : ℕ) : InputOperand → ℕ
  | .geometry e => cost w e
  | _ => 1

/-- Produce one vector field in temporary slot `base` by compiling a geometry expression or
copying the selected prefix word or length. -/
def field (r base : ℕ) : InputOperand → Code r
  | .geometry e => compile r base e
  | .prefixLength => .line (.copy (temp r base) (inputReg r 4))
  | .prefixWord => .line (.copy (temp r base) (inputReg r 5))

/-- For a geometry operand, all bounds required by the public-expression evaluator hold at
modulus `2^g.w`. The two prefix operands are already word-valued. -/
def FieldFits (g : Geometry) : InputOperand → Prop
  | .geometry e => e.Fits g (2^g.w)
  | _ => True

theorem field_eval (g : Geometry) (lit : LiteralPrefix) (hw : 2 ≤ g.w) (r base : ℕ) (e : InputOperand)
    (hr : base+need e ≤ r) (hf : FieldFits g e) :
    Eval g lit r base (e.eval g lit) (fieldCost g.w e) (field r base e) := by
  cases e with
  | geometry e => exact compile_eval g lit hw _ _ e hr hf
  | prefixLength => exact input_eval g lit (by simpa [need] using hr) 4 _ rfl
  | prefixWord => exact input_eval g lit (by simpa [need] using hr) 5 _ rfl

/-- Largest temporary index reserved for the vector, allowing one result slot per entry and
enough extra slots for its most demanding expression. -/
def capacity (args : Fin k → InputOperand) := k + Finset.univ.sup (fun i => need (args i))

/-- Register `13+i` holds vector entry `i` for the subsequent private cache store. -/
def src (args : Fin k → InputOperand) (i : Fin k) := temp (capacity args) (i.val+1)
/-- Temporary slot zero, register 12, holds the caller's cache base throughout geometry and
field evaluation. -/
def saved (args : Fin k → InputOperand) := temp (capacity args) 0
/-- Fixed register 10 carries the write pointer for the sequence of private cache stores. -/
def cursor (args : Fin k → InputOperand) := fixed (capacity args) 10
/-- Fixed register 11 holds the unit increment used to advance from one cache entry to the
next. -/
def unit (args : Fin k → InputOperand) := fixed (capacity args) 11

theorem src_val (args : Fin k → InputOperand) (i : Fin k) : (src args i).val = 13+i.val := by
  rw [src,temp_val (by unfold capacity; omega)]
  omega

private def initialFields (args : Fin k → InputOperand) : (n : ℕ) → n ≤ k → Code (capacity args)
  | 0, _ => .line (.copy (fixed _ 0) (fixed _ 0))
  | n+1, h => .seq (initialFields args n (by omega)) (field _ (n+1) (args ⟨n,h⟩))

private def maxCost (args : Fin k → InputOperand) := Finset.univ.sup (fun i => fieldCost 0 (args i))

private theorem prefix_run (args : Fin k → InputOperand) (g : Geometry) (lit : LiteralPrefix)
    (hw : 2 ≤ g.w) (hf : ∀ i, FieldFits g (args i)) (pub : Fin 11 → Word g.w) (st : Word g.w)
    (m : Memory g.w) (rs : Regs g.w (registerCount (capacity args))) (ready : Ready g lit rs)
    (n : ℕ) (hn : n ≤ k) :
    ∃ t ≤ n*(maxCost args*(g.w+1))+1, ∃ out,
      Flow.Exec pub st (initialFields args n hn) rs m (List.replicate t .tick) out m ∧ Ready g lit out ∧
      out (saved args) = rs (saved args) ∧
      ∀ i : Fin k, i.val < n → out (src args i) = Pieces.word g lit (args i) := by
  induction n with
  | zero =>
    have h : Flow.Exec pub st (.line (.copy (fixed (capacity args) 0) (fixed _ 0))) rs m [Event.tick] rs m := by
      apply Flow.Exec.line; simp only [Op.effect,Function.update_eq_self]
    exact ⟨1,by simp,rs,h,ready,rfl,fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ n ih =>
    obtain ⟨t,ht,mid,first,hr,hsaved,hprev⟩ := ih (by omega)
    let i : Fin k := ⟨n,hn⟩
    have room : n+1+need (args i) ≤ capacity args :=
      Nat.add_le_add hn (Finset.le_sup (f := fun j => need (args j)) (Finset.mem_univ i))
    obtain ⟨u,hu,out,second,hout,keep⟩ := field_eval g lit hw _ (n+1) (args i) room (hf i) pub st m mid hr
    have hcost : fieldCost g.w (args i) ≤ fieldCost 0 (args i)*(g.w+1) := by
      cases h : args i with
      | geometry e => exact cost_le e _
      | prefixLength | prefixWord => simp [fieldCost]
    have hmax : fieldCost 0 (args i) ≤ maxCost args := Finset.le_sup (f := fun j => fieldCost 0 (args j)) (Finset.mem_univ i)
    have bound := hu.trans (hcost.trans (Nat.mul_le_mul_right _ hmax))
    have hs : (saved args).val = 12 := by rw [saved,temp_val (Nat.zero_le _)]
    refine ⟨_,by rw [Nat.succ_mul]; omega,out,seqTicks first second,keep.ready hr,
      (keep _ (by omega) (by omega)).trans hsaved,?_⟩
    intro j hj
    by_cases hji : j.val = n
    · have eq : j = i := Fin.ext hji
      subst j; exact hout
    · exact (keep _ (by rw [src_val]; omega) (by rw [src_val]; omega)).trans (hprev _ (by omega))

/-- Load the geometry, compute the vector fields in index order, and initialize the cache write
pointer and its unit increment. -/
def vector (args : Fin k → InputOperand) (a b : ℕ) : Code (capacity args) :=
  .seq (.seq (PrimedCounter.renameFlow (fixed (capacity args)) id (PairNativeGeometry.program a b))
    (initialFields args k le_rfl)) (.seq (.line (.copy (cursor args) (saved args))) (.line (.constant (unit args) 1)))

/-- Tick bound for evaluating the entire operand vector, combining geometry setup with a
uniform per-entry bound and three bookkeeping instructions. -/
def work (args : Fin k → InputOperand) (a b : ℕ) (g : Geometry) :=
  PairNativeGeometry.ticks a b g.n + k*(maxCost args*(g.w+1)) + 3

/-- Postcondition for native vector evaluation. Each source register holds its encoded operand,
the cursor holds the supplied base and the increment register holds one. -/
structure Result (args : Fin k → InputOperand) (g : Geometry) (lit : LiteralPrefix)
    (base : Word g.w) (rs : Regs g.w (registerCount (capacity args))) : Prop where
  value (i : Fin k) : rs (src args i) = Pieces.word g lit (args i)
  pointer : rs (cursor args) = base
  one : rs (unit args) = 1

theorem vector_run (args : Fin k → InputOperand) (g : Geometry) (lit : LiteralPrefix) (a b : ℕ)
    (hb : 0 < b) (hn : 0 < g.n) (hwidth : g.w = (g.d+10)^4) (hbucket : g.H = 2^roundedUp a b g.n)
    (fit : PairNativeGeometry.Fits a b g.n g.w) (hf : ∀ i, FieldFits g (args i))
    (pub : Fin 11 → Word g.w) (h6 : (pub 6).val = g.n) (h7 : (pub 7).val = g.d)
    (h1 : pub 1 = Fin.ofNat _ lit.length) (h0 : pub 0 = Fin.ofNat _ lit.value)
    (st : Word g.w) (m : Memory g.w) (rs : Regs g.w (registerCount (capacity args))) :
    ∃ t ≤ work args a b g, ∃ out, Flow.Exec pub st (vector args a b) rs m (List.replicate t .tick) out m ∧
      Result args g lit (rs (saved args)) out := by
  let r := capacity args
  obtain ⟨small,geo,values⟩ := PairNativeGeometry.program_run pub st m (rs ∘ fixed r) a b g.n g.d hb hn hwidth fit h6 h7
  obtain ⟨mid,load,keep,other⟩ := PrimedCounter.liftExec (fixedEmbedding r) id pub geo rs rfl
  have wordEq (x : Word g.w) : x = Fin.ofNat _ x.val := (Fin.ofNat_val_eq_self x).symm
  have ready : Ready g lit mid := by
    intro i
    have eq := congrFun keep (inputSlot i)
    change mid (inputReg r i) = small _ at eq
    apply eq.trans
    fin_cases i
    · exact (wordEq (small 4)).trans (congrArg (Fin.ofNat _) values.length)
    · exact (wordEq (small 5)).trans (congrArg (Fin.ofNat _) values.address)
    · exact (wordEq (small 7)).trans (congrArg (Fin.ofNat _) (values.bucket.trans hbucket.symm))
    · exact (wordEq (small 6)).trans (congrArg (Fin.ofNat _) values.width)
    · exact values.prefixLength.trans h1
    · exact values.prefixWord.trans h0
  have hs : mid (saved args) = rs (saved args) :=
    other _ (by rintro ⟨j,hj⟩; exact temp_ne_fixed (r := r) 0 j hj.symm)
  have hw : 2 ≤ g.w := by rw [hwidth]; exact (show 2 ≤ g.d+10 by omega).trans (Nat.le_self_pow (by decide) _)
  obtain ⟨t,ht,z,body,_,hz,hout⟩ := prefix_run args g lit hw hf pub st m mid ready k le_rfl
  let u := Function.update z (cursor args) (z (saved args))
  let out := Function.update u (unit args) (Fin.ofNat (2^g.w) 1)
  have cp : Flow.Exec pub st (.line (.copy (cursor args) (saved args))) z m (List.replicate 1 .tick) u m := .line rfl
  have un : Flow.Exec pub st (.line (.constant (unit args) 1)) u m (List.replicate 1 .tick) out m := .line rfl
  refine ⟨_,by unfold work; omega,out,seqTicks (seqTicks load body) (seqTicks cp un),?_⟩
  constructor
  · intro i
    rw [show out (src args i) = u (src args i) from Function.update_of_ne (temp_ne_fixed (i.val+1) 11) ..,
      show u (src args i) = z (src args i) from Function.update_of_ne (temp_ne_fixed (i.val+1) 10) ..]
    exact hout i i.isLt
  · change Function.update u (unit args) _ (cursor args) = _
    rw [Function.update_of_ne (show cursor args ≠ unit args from by
      intro h; have := congrArg Fin.val h; change 10 = 11 at this; contradiction)]
    exact (Function.update_self ..).trans (hz.trans hs)
  · exact Function.update_self ..

end PairSimulation.NativeOperands

end VPVNP
end Computability
end OAI
