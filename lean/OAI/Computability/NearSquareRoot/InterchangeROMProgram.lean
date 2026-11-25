import OAI.Computability.NearSquareRoot.InterchangeROMRoute

/-! # A literal interchange stage program on packed physical rows -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROM
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space

variable {T M : Type}

/-- A table descriptor or a list of movement instructions indexed by output row. -/
abbrev Instruction (T M : Type) := T ⊕ List (ℕ × M)

def instruction (table : T → Cmd) (moveRow : M → Cmd) : Instruction T M → Cmd
  | .inl t => underHeader (table t)
  | .inr legs => routeCommand moveRow legs

/-- A template is compiled directly into P192 control. -/
def program (table : T → Cmd) (moveRow : M → Cmd) (ops : List (Instruction T M)) : Cmd :=
  ops.foldr (fun op rest => (instruction table moveRow op).join rest) .pass

theorem program_within {R : ℕ} (hR : 3 ≤ R) (table : T → Cmd) (moveRow : M → Cmd)
    (ht : ∀ t, Within R (table t)) (hm : ∀ m, Within R (moveRow m)) (ops : List (Instruction T M)) :
    Within R (program table moveRow ops) := by
  induction ops with
  | nil => trivial
  | cons op ops ih =>
    refine ⟨?_,ih⟩
    cases op with
    | inl t => exact underHeader_within hR (ht t)
    | inr legs => exact route_within hR moveRow hm legs

/-- The width-dependent tree rows can represent arbitrary nested payloads.
All table and movement clocks refer to their compiled implementations. -/
structure Model (T M : Type) where
  table : T → List Tree → List Tree
  moveRow : M → Tree → Tree
  tableDomain : T → List Tree → Prop
  moveDomain : M → Tree → Prop
  tableTime : T → List Tree → ℕ
  moveTime : M → Tree → ℕ
  moveCap : ℕ
  moveDepth : ℕ

structure Result where
  rows : List Tree
  time : ℕ
  space : ℕ
  depth : ℕ

namespace Model

def next (model : Model T M) (header : Tree) (xs : List Tree) : Instruction T M → Result
  | .inl t =>
    let c := 84*header.count + model.tableTime t xs + 11
    ⟨model.table t xs,c,(packet header xs).count+c,c⟩
  | .inr legs =>
    let v := packet header xs
    let ys := legs.map fun (a,m) => model.moveRow m (source xs a)
    let t := costSum (fun z : ℕ × M => model.moveTime z.2 (source xs z.1)) legs
    ⟨ys,(legs.length+2)*(160*(v.count+1))+t,
      170*(v.count+1)+(packet header ys).count+model.moveCap,170*(v.count+1)+model.moveDepth⟩

def eval (model : Model T M) (header : Tree) : List (Instruction T M) → List Tree → Result
  | [],xs => ⟨xs,1,(packet header xs).count,0⟩
  | a::as,xs =>
    let left := model.next header xs a
    let right := model.eval header as left.rows
    ⟨right.rows,left.time+right.time+2,max left.space right.space,max (left.depth+1) right.depth⟩

def Valid (model : Model T M) (xs : List Tree) : Instruction T M → Prop
  | .inl t => model.tableDomain t xs
  | .inr legs => ∀ leg ∈ legs, leg.1 < xs.length ∧ model.moveDomain leg.2 (source xs leg.1)

def WellFormed (model : Model T M) (header : Tree) : List (Instruction T M) → List Tree → Prop
  | [],_ => True
  | a::as,xs => model.Valid xs a ∧ model.WellFormed header as (model.next header xs a).rows

/-- Atomic contracts for the same table and move code for all packets. -/
structure Implements (model : Model T M) (header : Tree) (table : T → Cmd) (moveRow : M → Cmd)
    (env : Env) : Prop where
  atTable : ∀ t xs, model.tableDomain t xs → ∀ r, Fits env (table t) (pile 0 (Task.forest id xs) r)
    (pile 0 (Task.forest id (model.table t xs)) r) (model.tableTime t xs)
  atMove : ∀ m x, model.moveDomain m x → ∀ r base, DeckCap base r →
    BoundedFits env (moveRow m) (pile 0 (.fork header x) r) (pile 0 (model.moveRow m x) r)
      (model.moveTime m x) (base+model.moveCap) model.moveDepth

private theorem literalField (model : Model T M) (header : Tree) (table : T → Cmd) (moveRow : M → Cmd)
    (env : Env) (h : model.Implements header table moveRow env) (a : Instruction T M)
    (xs : List Tree) (valid : model.Valid xs a) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let next := model.next header xs a
    BoundedFits env (instruction table moveRow a) (pile 0 (packet header xs) r)
      (pile 0 (packet header next.rows) r) next.time (base+next.space) next.depth := by
  cases a with
  | inl t =>
    have hf := underHeader_fits header _ _ _ _ env (h.atTable t xs valid) r
    exact BoundedFits.of_fits hf (fun i => by
      have hi := hr.pile 0 (packet header xs) i
      change (letters (pile 0 (packet header xs) r) i).length + _ ≤ base+((packet header xs).count+_)
      simp only [next]
      omega) le_rfl
  | inr legs =>
    let sel : {z // z ∈ legs} → ℕ × M := Subtype.val
    let out := fun z : {z // z ∈ legs} => model.moveRow z.1.2 (source xs z.1.1)
    let t := fun z : {z // z ∈ legs} => model.moveTime z.1.2 (source xs z.1.1)
    have hr' := route_bounded header xs legs.attach sel moveRow out t model.moveCap model.moveDepth env
      (fun z => (valid _ z.2).1) (fun z => h.atMove z.1.2 _ (valid _ z.2).2) r base hr
    have f {A : Type} (g : ℕ × M → A) :
        (legs.attach.map (fun z => g z.1)) = legs.map g := by
      exact (List.map_map (f:=Subtype.val) (g:=g)).symm.trans
        (congrArg (List.map g) (List.attach_map_subtype_val legs))
    have e : Task.forest out legs.attach =
        Task.forest (fun z : ℕ × M => model.moveRow z.2 (source xs z.1)) legs := by
      let fn (z : ℕ × M) := model.moveRow z.2 (source xs z.1)
      exact (Task.forest_map fn Subtype.val legs.attach).symm.trans
        (congrArg (Task.forest fn) (List.attach_map_subtype_val legs))
    have et : costSum t legs.attach = costSum (fun z : ℕ × M => model.moveTime z.2 (source xs z.1)) legs :=
      congrArg List.sum (f (fun z : ℕ × M => model.moveTime z.2 (source xs z.1)))
    rw [et] at hr'
    rw [show legs.attach.map sel = legs from List.attach_map_subtype_val _,e] at hr'
    simpa only [sel,out,t,packet,instruction,next,costSum,Task.forest_map,
      List.length_attach,Nat.add_assoc,id_eq] using hr'

/-- Execution of the actual compiled stage. The local times add, and only
the maximum of the per-instruction space allowances is retained. -/
theorem run (model : Model T M) (header : Tree) (table : T → Cmd) (moveRow : M → Cmd)
    (env : Env) (h : model.Implements header table moveRow env) (ops : List (Instruction T M))
    (xs : List Tree) (ok : model.WellFormed header ops xs) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let res := model.eval header ops xs
    BoundedFits env (program table moveRow ops) (pile 0 (packet header xs) r)
      (pile 0 (packet header res.rows) r) res.time (base+res.space) res.depth := by
  induction ops generalizing xs with
  | nil => exact BoundedFits.pass (hr.pile 0 (packet header xs))
  | cons a ops ih =>
    let left := model.next header xs a
    let right := model.eval header ops left.rows
    let space := max left.space right.space
    let depth := max (left.depth+1) right.depth
    have one := literalField model header table moveRow env h a xs ok.1 r base hr
    have two := ih left.rows ok.2
    have h₁ := one.mono le_rfl (show base+left.space ≤ base+space from Nat.add_le_add_left (le_max_left ..) _)
      le_rfl
    have h₂ := two.mono le_rfl (show base+right.space ≤ base+space from Nat.add_le_add_left (le_max_right ..) _)
      (show right.depth ≤ depth from le_max_right ..)
    exact h₁.join h₂ (le_max_left ..)

end Model
end InterchangeROM

end NearSquareRoot
end Computability
end OAI
