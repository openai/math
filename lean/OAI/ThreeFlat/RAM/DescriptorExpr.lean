import OAI.ThreeFlat.RAM.DeterministicBlock
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Native expressions for random-access descriptors

A let binds one word at index zero, shifting older variables to successor
indices. Inputs are caller registers. Parameters are machine public words.
Evaluation may read arbitrary addresses and never writes memory. Each let
takes two native instructions and the final result copy takes one.
-/

namespace ThreeFlat.RAM.DescriptorExpr

open Computability.VPVNP.BurstRAM PrivateRAM

inductive Comparison where
  | eq | lt
  deriving DecidableEq

variable {w k n p r : ℕ}

inductive Op (w k n : ℕ) where
  | literal (v : Word w)
  | parameter (i : Fin k)
  | binary (opcode : BinaryOp) (a b : Fin n)
  | load (addr : Fin n)
  | select (cmp : Comparison) (a b yes no : Fin n)

def Comparison.test (cmp : Comparison) (a b : Word w) : Bool :=
  match cmp with
  | .eq => a == b
  | .lt => decide (a < b)

def Op.eval (o : Op w k n) (params : Fin k → Word w) (vars : Fin n → Word w)
    (mem : Memory w) : Word w :=
  match o with
  | .literal v => v
  | .parameter i => params i
  | .binary op a b => op.eval (vars a) (vars b)
  | .load addr => mem (vars addr).val
  | .select cmp a b yes no => if cmp.test (vars a) (vars b) then vars yes else vars no

inductive Term (w k : ℕ) : ℕ → Type
  | result {n : ℕ} (i : Fin n) : Term w k n
  | bind {n : ℕ} (op : Op w k n) (body : Term w k (n+1)) : Term w k n

def Term.eval (params : Fin k → Word w) (m : Memory w) :
    {n : ℕ} → Term w k n → (Fin n → Word w) → Word w
  | _, .result i, vs => vs i
  | _, .bind op body, vs => body.eval params m (Fin.cons (op.eval params vs m) vs)

def Op.instruction (o : Op w k n) (pc : Fin 3 → Fin p) (vars : Fin n → Fin r)
    (dst : Fin r) (exit : Fin p) (i : Fin 3) : Instr w p r k :=
  match i.val with
  | 0 =>
    match o with
    | .literal v => .constant dst v (pc 1)
    | .parameter j => .publicWord dst j (pc 1)
    | .binary op a b => .binary op dst (vars a) (vars b) (pc 1)
    | .load a => .readExternal dst (vars a) (pc 1)
    | .select .eq a b _ _ => .jumpEq (vars a) (vars b) (pc 1) (pc 2)
    | .select .lt a b _ _ => .jumpLt (vars a) (vars b) (pc 1) (pc 2)
  | _ =>
    match o with
    | .select _ _ _ yes no => .copy dst (vars (if i.val = 1 then yes else no)) exit
    | _ => .jumpEq dst dst exit exit

private theorem Op.advance_two (M : Machine w p r k) (o : Op w k n)
    (pc : Fin 3 → Fin p) (vars : Fin n → Fin r) (dst : Fin r) (exit : Fin p)
    (inst : ∀ i, M.code (pc i) = o.instruction pc vars dst exit i)
    (c : Config w p r) (mem : Memory w) (atStart : c.pc = pc 0) :
    advance M.program 2 c mem = some (c.put exit dst (o.eval M.publicData (c.reg ∘ vars) mem), mem) := by
  cases o with
  | select cmp a b yes no =>
    cases cmp
    · by_cases h : c.reg (vars a) = c.reg (vars b) <;>
        simp [advance, Machine.program, atStart, inst, Op.instruction, Instr.run, Config.put,
          Op.eval, Comparison.test, h]
    · by_cases h : c.reg (vars a) < c.reg (vars b) <;>
        simp [advance, Machine.program, atStart, inst, Op.instruction, Instr.run, Config.put,
          Op.eval, Comparison.test, h]
  | _ =>
    simp [advance, Machine.program, atStart, inst, Op.instruction, Instr.run, Config.put,
      Op.eval]

def Term.binds : {n : ℕ} → Term w k n → ℕ
  | _, .result _ => 0
  | _, .bind _ body => body.binds + 1

private instance {op : Op w k n} {b : Term w k (n+1)} : NeZero (Term.bind op b).binds :=
  ⟨by simp [Term.binds]⟩

def Term.labels : {n : ℕ} → Term w k n → ℕ
  | _, .result _ => 1
  | _, .bind _ body => 3 + body.labels

def Term.steps : {n : ℕ} → Term w k n → ℕ
  | _, .result _ => 1
  | _, .bind _ body => 2 + body.steps

theorem Term.labels_eq (e : Term w k n) : e.labels = 3 * e.binds + 1 := by
  induction e <;> simp_all [labels,binds]; omega

theorem Term.steps_eq (e : Term w k n) : e.steps = 2 * e.binds + 1 := by
  induction e <;> simp_all [steps,binds]; omega

def Term.first (e : Term w k n) : Fin e.labels :=
  ⟨0, by rw [e.labels_eq]; omega⟩

private def headPC {z : ℕ} (loc : Fin (3+z) → Fin p) (i : Fin 3) := loc (i.castAdd z)
private def tailPC {z : ℕ} (loc : Fin (3+z) → Fin p) (i : Fin z) := loc (Fin.natAdd 3 i)

/-- Compile a let-expression into a caller's chosen control and register layout. -/
def Term.emit : {n : ℕ} → (e : Term w k n) → (Fin e.labels → Fin p) →
    (Fin n → Fin r) → (Fin e.binds → Fin r) → Fin r → Fin p → Fin e.labels → Instr w p r k
  | _, .result j, _, vs, _, out, exit => fun _ => .copy out (vs j) exit
  | _, .bind op body, loc, vs, tmp, out, exit =>
    Fin.addCases (op.instruction (headPC loc) vs (tmp 0) (tailPC loc body.first))
      (body.emit (tailPC loc) (Fin.cons (tmp 0) vs) (tmp ∘ Fin.succ) out exit)

/-- Final configuration of the compiled expression. -/
def Term.run (params : Fin k → Word w) (m : Memory w) :
    {n : ℕ} → (e : Term w k n) → (Fin n → Fin r) → (Fin e.binds → Fin r) →
      Fin r → Fin p → Config w p r → Config w p r
  | _, .result i, vs, _, out, exit, c => c.put exit out (c.reg (vs i))
  | _, .bind op body, vs, tmp, out, exit, c =>
    body.run params m (Fin.cons (tmp 0) vs) (tmp ∘ Fin.succ) out exit
      (c.put exit (tmp 0) (op.eval params (c.reg ∘ vs) m))

private theorem Term.run_pc_irrel (params : Fin k → Word w) (mem : Memory w)
    (e : Term w k n) (vs : Fin n → Fin r) (tmp : Fin e.binds → Fin r)
    (out : Fin r) (exit : Fin p) (c : Config w p r) (i : Fin p) :
    e.run params mem vs tmp out exit {c with pc := i} = e.run params mem vs tmp out exit c := by
  cases e <;> rfl

/-- Execute the expression deterministically. The second returned component is
the original external memory even for nested row-address dereferences. -/
theorem Term.advance_emit (M : Machine w p r k) (e : Term w k n) (loc : Fin e.labels → Fin p)
    (vs : Fin n → Fin r) (tmp : Fin e.binds → Fin r) (out : Fin r) (exit : Fin p)
    (inst : ∀ i, M.code (loc i) = e.emit loc vs tmp out exit i)
    (c : Config w p r) (m : Memory w) (start : c.pc = loc e.first) :
    advance M.program e.steps c m = some (e.run M.publicData m vs tmp out exit c, m) := by
  induction e generalizing c with
  | result j =>
    simp [steps, advance, Machine.program, start, inst, emit, Instr.run, run]
  | bind op body ih =>
    let next := tailPC loc body.first
    have hhead (i : Fin 3) : M.code (headPC loc i) =
        op.instruction (headPC loc) vs (tmp 0) next i := by
      simpa [headPC, next, emit] using inst (i.castAdd body.labels)
    have htail (i : Fin body.labels) : M.code (tailPC loc i) =
        body.emit (tailPC loc) (Fin.cons (tmp 0) vs) (tmp ∘ Fin.succ) out exit i := by
      simpa [tailPC, emit] using inst (Fin.natAdd 3 i)
    have h0 : c.pc = headPC loc 0 := start
    rw [steps, advance_add, op.advance_two M _ _ _ _ hhead c m h0, Option.bind_some]
    let d := c.put next (tmp 0) (op.eval M.publicData (c.reg ∘ vs) m)
    have bodyStep := ih (tailPC loc) (Fin.cons (tmp 0) vs) (tmp ∘ Fin.succ) htail d rfl
    change advance M.program body.steps d m = some (_,m)
    rw [bodyStep]
    congr 2
    exact (body.run_pc_irrel M.publicData m _ _ out exit
      (c.put exit (tmp 0) (op.eval M.publicData (c.reg ∘ vs) m)) next)

/-- The result register is the denotation of the source expression. Input
registers may alias one another. Only the compiler's scratch must be fresh. -/
theorem Term.run_result (params : Fin k → Word w) (m : Memory w) (e : Term w k n)
    (vs : Fin n → Fin r) (tmp : Fin e.binds → Fin r) (out : Fin r) (exit : Fin p)
    (c : Config w p r) (fresh : ∀ i j, vs i ≠ tmp j) (inj : Function.Injective tmp) :
    (e.run params m vs tmp out exit c).reg out = e.eval params m (c.reg ∘ vs) := by
  induction e generalizing c with
  | result i => simp [run, eval]
  | bind op body ih =>
    let val := op.eval params (c.reg ∘ vs) m
    let d := c.put exit (tmp 0) val
    have fresh' (i : Fin (_+1)) (j : Fin body.binds) :
        Fin.cons (α := fun _ => Fin r) (tmp 0) vs i ≠ (tmp ∘ Fin.succ) j := by
      refine Fin.cases ?_ (fun t => ?_) i
      · exact inj.ne (by change (0 : Fin (body.binds+1)) ≠ j.succ; exact Fin.succ_ne_zero j |>.symm)
      · exact fresh t j.succ
    have inj' : Function.Injective (tmp ∘ Fin.succ) := inj.comp (fun _ _ eq => Fin.succ_inj.mp eq)
    change (body.run params m _ _ out exit d).reg out = body.eval params m _
    rw [ih _ _ d fresh' inj']
    apply congrArg (body.eval params m)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [d, val]
    · simp [d, Config.put, Function.update_of_ne (fresh j 0)]

theorem Term.run_pc (params : Fin k → Word w) (m : Memory w) (e : Term w k n)
    (vs : Fin n → Fin r) (tmp : Fin e.binds → Fin r) (out : Fin r) (exit : Fin p)
    (c : Config w p r) : (e.run params m vs tmp out exit c).pc = exit := by
  induction e generalizing c with
  | result i => rfl
  | bind _ _ ih => apply ih

/-- All other registers and private memory are preserved. -/
theorem Term.run_frame (params : Fin k → Word w) (m : Memory w) (e : Term w k n)
    (vs : Fin n → Fin r) (tmp : Fin e.binds → Fin r) (out : Fin r) (exit : Fin p)
    (c : Config w p r) :
    let d := e.run params m vs tmp out exit c
    d.persistent = c.persistent ∧ d.privateMem = c.privateMem ∧
      ∀ i, i ≠ out → (∀ j, i ≠ tmp j) → d.reg i = c.reg i := by
  induction e generalizing c with
  | result j =>
    exact ⟨rfl, rfl, fun _ ho _ => Function.update_of_ne ho ..⟩
  | bind op body ih =>
    dsimp only [run]
    obtain ⟨hp,hm,hr⟩ := ih (Fin.cons (tmp 0) vs) (tmp ∘ Fin.succ) (c.put exit (tmp 0) _)
    refine ⟨hp,hm,?_⟩
    intro i ho ht
    rw [hr i ho (fun j => ht j.succ)]
    exact Function.update_of_ne (ht 0) ..

abbrev Term.regCount (e : Term w k n) := n + (e.binds + 1)
def Term.argReg (e : Term w k n) (i : Fin n) : Fin e.regCount := i.castAdd (e.binds+1)
def Term.tempReg (e : Term w k n) (i : Fin e.binds) : Fin e.regCount := Fin.natAdd n i.castSucc
def Term.outReg (e : Term w k n) : Fin e.regCount := Fin.natAdd n (Fin.last e.binds)

theorem Term.fresh_regs (e : Term w k n) (i : Fin n) (j : Fin e.binds) :
    e.argReg i ≠ e.tempReg j := by
  intro h
  have := congrArg Fin.val h
  simp [argReg,tempReg] at this
  omega

theorem Term.injective_tempReg (e : Term w k n) : Function.Injective e.tempReg := by
  intro i j h
  have z := congrArg Fin.val h
  apply Fin.ext
  simpa [tempReg] using z

/-- Allocate a finite ROM with one final return opcode. Its public parameters
are independent of the input words. -/
def Term.machine (e : Term w k n) (data : Fin k → Word w) :
    Machine w (e.labels+1) e.regCount k where
  entry := e.first.castSucc
  code := Fin.addCases (e.emit Fin.castSucc e.argReg e.tempReg e.outReg (Fin.last e.labels))
    (fun _ => .returnState e.outReg)
  publicData := data

theorem Term.machine_advance (e : Term w k n) (data : Fin k → Word w)
    (c : Config w (e.labels+1) e.regCount) (mem : Memory w)
    (start : c.pc = e.first.castSucc) :
    advance (e.machine data).program e.steps c mem =
      some (e.run data mem e.argReg e.tempReg e.outReg (Fin.last e.labels) c,mem) := by
  exact e.advance_emit _ Fin.castSucc _ _ _ _ (fun i => by
    rw [show i.castSucc = i.castAdd 1 from rfl]
    simp [machine]) c mem start

/-- The result returned by the native program is the source expression's word,
with one final return instruction after its deterministic prefix. -/
theorem Term.mass_machine {F : Type*} [Semiring F] (code : FieldCode F w)
    (e : Term w k n) (data : Fin k → Word w)
    (c : Config w (e.labels+1) e.regCount) (mem : Memory w)
    (start : c.pc = e.first.castSucc) (fuel : ℕ) :
    mass code (e.machine data).program ((fuel+1)+e.steps) c mem =
      code.decode (e.eval data mem (c.reg ∘ e.argReg)) := by
  rw [mass_of_advance code _ (e.machine_advance data c mem start) (fuel+1)]
  have lastInst : (e.machine data).code (Fin.last e.labels) = .returnState e.outReg := by
    rw [show Fin.last e.labels = Fin.natAdd e.labels (0 : Fin 1) from rfl]
    simp [machine]
  simp only [mass,Machine.program,e.run_pc,lastInst,Instr.run,FieldCode.terminal]
  rw [e.run_result data mem _ _ _ _ _ e.fresh_regs e.injective_tempReg]

/-- Rename free registers while preserving every local binder. -/
def Op.rename {m : ℕ} (f : Fin n → Fin m) : Op w k n → Op w k m
  | .literal v => .literal v
  | .parameter i => .parameter i
  | .binary op a b => .binary op (f a) (f b)
  | .load a => .load (f a)
  | .select c a b y z => .select c (f a) (f b) (f y) (f z)

@[simp] theorem Op.eval_rename {m : ℕ} (f : Fin n → Fin m) (op : Op w k n)
    (data : Fin k → Word w) (vs : Fin m → Word w) (mem : Memory w) :
    (op.rename f).eval data vs mem = op.eval data (vs ∘ f) mem := by
  cases op <;> rfl

def Term.rename : {n m : ℕ} → Term w k n → (Fin n → Fin m) → Term w k m
  | _, _, .result i, f => .result (f i)
  | _, _, .bind op b, f => .bind (op.rename f) (b.rename (Fin.cons 0 (Fin.succ ∘ f)))

@[simp] theorem Term.eval_rename {s : ℕ} (e : Term w k n) (f : Fin n → Fin s)
    (data : Fin k → Word w) (mem : Memory w) (vs : Fin s → Word w) :
    (e.rename f).eval data mem vs = e.eval data mem (vs ∘ f) := by
  induction e generalizing s with
  | result _ => rfl
  | bind op body ih =>
    simp only [rename, eval, ih, Op.eval_rename]
    apply congrArg (body.eval data mem)
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> simp

@[simp] theorem Term.binds_rename {s : ℕ} (e : Term w k n) (f : Fin n → Fin s) :
    (e.rename f).binds = e.binds := by
  induction e generalizing s <;> simp_all [rename,binds]

/-- Evaluate a subexpression and bind its value at zero in the continuation. -/
def Term.letThen : {n : ℕ} → Term w k n → Term w k (n+1) → Term w k n
  | _, .result i, cont => cont.rename (Fin.cons i id)
  | _, .bind op b, cont =>
    .bind op (b.letThen (cont.rename (Fin.cons 0 (fun j => j.succ.succ))))

@[simp] theorem Term.eval_letThen (e : Term w k n) (cont : Term w k (n+1))
    (data : Fin k → Word w) (mem : Memory w) (vs : Fin n → Word w) :
    (e.letThen cont).eval data mem vs = cont.eval data mem (Fin.cons (e.eval data mem vs) vs) := by
  induction e with
  | result i =>
    rw [letThen, eval_rename]
    apply congrArg (cont.eval data mem)
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> simp [eval]
  | bind op b ih =>
    simp only [letThen, eval, ih, eval_rename]
    apply congrArg (cont.eval data mem)
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> simp

@[simp] theorem Term.binds_letThen (e : Term w k n) (cont : Term w k (n+1)) :
    (e.letThen cont).binds = e.binds + cont.binds := by
  induction e with
  | result i => simp [letThen,binds]
  | bind op b ih => simp [letThen,binds,ih]; omega

def Term.literal (v : Word w) : Term w k n := .bind (.literal v) (.result 0)
def Term.parameter (i : Fin k) : Term w k n := .bind (.parameter i) (.result 0)
def Term.load (addr : Term w k n) : Term w k n :=
  addr.letThen (.bind (.load 0) (.result 0))
def Term.binary (op : BinaryOp) (a b : Term w k n) : Term w k n :=
  a.letThen ((b.rename Fin.succ).letThen (.bind (.binary op (Fin.succ 0) 0) (.result 0)))
def Term.select (cmp : Comparison) (a b yes no : Term w k n) : Term w k n :=
  a.letThen ((b.rename Fin.succ).letThen
    ((yes.rename (fun i => i.succ.succ)).letThen
      ((no.rename (fun i => i.succ.succ.succ)).letThen
        (.bind (.select cmp (Fin.succ (Fin.succ (Fin.succ 0))) (Fin.succ (Fin.succ 0))
          (Fin.succ 0) 0) (.result 0)))))

@[simp] theorem Term.eval_literal (v : Word w) (data : Fin k → Word w) (mem : Memory w)
    (vs : Fin n → Word w) : (literal v).eval data mem vs = v := by simp [literal,eval,Op.eval]

@[simp] theorem Term.eval_parameter (i : Fin k) (data : Fin k → Word w) (mem : Memory w)
    (vs : Fin n → Word w) : (parameter i).eval data mem vs = data i := by
  simp [parameter,eval,Op.eval]

@[simp] theorem Term.eval_load (a : Term w k n) (data : Fin k → Word w) (mem : Memory w)
    (vs : Fin n → Word w) : a.load.eval data mem vs = mem (a.eval data mem vs).val := by
  simp [load,eval,Op.eval]

@[simp] theorem Term.eval_binary (op : BinaryOp) (a b : Term w k n) (data : Fin k → Word w)
    (mem : Memory w) (vs : Fin n → Word w) : (binary op a b).eval data mem vs =
      op.eval (a.eval data mem vs) (b.eval data mem vs) := by
  simp [binary,eval,Op.eval,Function.comp_def]

@[simp] theorem Term.eval_select (cmp : Comparison) (a b yes no : Term w k n)
    (data : Fin k → Word w) (mem : Memory w) (vs : Fin n → Word w) :
    (select cmp a b yes no).eval data mem vs =
      if cmp.test (a.eval data mem vs) (b.eval data mem vs) then yes.eval data mem vs
      else no.eval data mem vs := by
  simp only [select,eval_letThen, eval_rename,eval,Op.eval,Function.comp_def,Fin.cons_succ,
    Fin.cons_zero]

private def skipInputs {m : ℕ} : (d : ℕ) → Fin m → Fin (m+d)
  | 0, i => i
  | d+1, i => (skipInputs d i).succ

private def frontInput {m n : ℕ} (i : Fin n) : Fin (m+n) := ⟨i.val, by omega⟩

private def extendEnv {α : Type*} {m : ℕ} :
    {n : ℕ} → (Fin n → α) → (Fin m → α) → Fin (m+n) → α
  | 0, _, vs => vs
  | _+1, xs, vs => Fin.cons (xs 0) (extendEnv (xs ∘ Fin.succ) vs)

private theorem extendEnv_skip {α : Type*} {m n : ℕ} (xs : Fin n → α) (vs : Fin m → α) :
    extendEnv xs vs ∘ skipInputs n = vs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    simp only [Function.comp_apply, skipInputs, extendEnv, Fin.cons_succ]
    exact congrFun (ih (xs ∘ Fin.succ)) i

private theorem extendEnv_front {α : Type*} {m n : ℕ} (xs : Fin n → α) (vs : Fin m → α) :
    extendEnv xs vs ∘ frontInput = xs := by
  induction n with
  | zero => exact funext fun i => i.elim0
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have z : @frontInput m (n+1) 0 = 0 := Fin.ext rfl
      simp only [Function.comp_apply, z, extendEnv, Fin.cons_zero]
    · have h : @frontInput m (n+1) j.succ = (@frontInput m n j).succ := Fin.ext rfl
      simp only [Function.comp_apply, h, extendEnv, Fin.cons_succ]
      exact congrFun (ih (xs ∘ Fin.succ)) j

private def bindInputs {m : ℕ} : {n : ℕ} →
    (Fin n → Term w k m) → Term w k (m+n) → Term w k m
  | 0, _, body => body
  | n+1, args, body =>
    bindInputs (args ∘ Fin.succ) (((args 0).rename (skipInputs n)).letThen body)

private theorem eval_bindInputs {m n : ℕ} (args : Fin n → Term w k m)
    (body : Term w k (m+n)) (data : Fin k → Word w) (mem : Memory w) (vs : Fin m → Word w) :
    (bindInputs args body).eval data mem vs =
      body.eval data mem (extendEnv (fun i => (args i).eval data mem vs) vs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bindInputs, ih, Term.eval_letThen, Term.eval_rename, extendEnv_skip]
    rfl

private theorem binds_bindInputs {m n : ℕ} (args : Fin n → Term w k m)
    (body : Term w k (m+n)) :
    (bindInputs args body).binds = body.binds + ∑ i, (args i).binds := by
  induction n with
  | zero => simp [bindInputs]
  | succ n ih =>
    rw [bindInputs, ih, Term.binds_letThen, Term.binds_rename, Fin.sum_univ_succ]
    simp [Nat.add_assoc,Nat.add_left_comm]

/-- Supply all free variables by arbitrary expressions in a caller's context.
Each supplied expression is evaluated exactly once even if its value is reused. -/
def Term.instantiate {m : ℕ} (e : Term w k n) (args : Fin n → Term w k m) : Term w k m :=
  bindInputs args (e.rename frontInput)

@[simp] theorem Term.eval_instantiate {m : ℕ} (e : Term w k n) (args : Fin n → Term w k m)
    (data : Fin k → Word w) (mem : Memory w) (vs : Fin m → Word w) :
    (e.instantiate args).eval data mem vs = e.eval data mem (fun i => (args i).eval data mem vs) := by
  rw [instantiate, eval_bindInputs, eval_rename, extendEnv_front]

@[simp] theorem Term.binds_instantiate {m : ℕ} (e : Term w k n) (args : Fin n → Term w k m) :
    (e.instantiate args).binds = e.binds + ∑ i, (args i).binds := by
  simp [instantiate,binds_bindInputs]

end ThreeFlat.RAM.DescriptorExpr

end OAI
