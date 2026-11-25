import OAI.Hierarchy.ProbeStageResident
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.ProbeStageFabric

namespace OAI
/-! # Native row operands for the entering, inner and exiting tile stages -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

/-- Three parent columns and the color/rank columns written by the allocator. -/
structure Inputs where
  parentGroup : Bank
  parentInput : Bank
  parentOutput : Bank
  color : Bank
  enterRank : Bank
  exitRank : Bank

/-- Each public table is one fixed function of one group or offset. -/
structure Tables where
  groupBlocks : Bank
  groupColors : Bank
  block : Bank
  offset : Bank
  colorQuota : Bank
  blockQuota : Bank

def rowCell (b : Bank) := Expr.lookup b .row
def rowAdd (x y : Expr) := Expr.op .add x y

/-- The three fields of each move are group number, source offset, target
offset, in that order. -/
def field (x : Inputs) (t : Tables) : Fin 9 → Expr :=
  let g := rowCell x.parentGroup
  let u := rowCell x.parentInput
  let v := rowCell x.parentOutput
  let c := rowCell x.color
  let i := rowCell x.enterRank
  let j := rowCell x.exitRank
  let a := Expr.lookup t.block u
  let b := Expr.lookup t.block v
  let gc := Expr.lookup t.groupBlocks g
  let ci := Expr.lookup t.colorQuota c
  ![rowAdd gc a, .lookup t.offset u, rowAdd ci i,
    rowAdd (.lookup t.groupColors g) c, rowAdd (.lookup t.blockQuota a) i, rowAdd (.lookup t.blockQuota b) j,
    rowAdd gc b, rowAdd ci j, .lookup t.offset v]

def passes (x : Inputs) (t : Tables) (base n : ℕ) := columns n base (List.ofFn (field x t))

theorem field_work (x : Inputs) (t : Tables) (j : Fin 9) : (field x t j).work ≤ 32 := by
  fin_cases j <;> norm_num [field,rowCell,rowAdd,Expr.work]

theorem clock_bound (x : Inputs) (t : Tables) (n base : ℕ) :
    clock (passes x t base n) ≤ 4+9*(4+n*68) := by
  have h := columns_clock n base 32 (List.ofFn (field x t)) (by
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact field_work x t i)
  simpa only [passes,List.length_ofFn,show 2*32+4=68 by decide] using h

section Readback
variable {n m B w groups : ℕ} {G : Type} (p : Tiles (Fin n) G m) (pos : 0<B)
    (a : Allocation B (leftBlock p pos) (rightBlock p pos)) (encode : G ↪ Fin groups)
    (x : Inputs) (t : Tables) (mem : Memory w)

structure Loaded : Prop where
  group : Resident x.parentGroup mem (fun r => (encode (p.group r)).val)
  parentIn : Resident x.parentInput mem (fun r => (p.input r).val)
  parentOut : Resident x.parentOutput mem (fun r => (p.output r).val)
  color : Resident x.color mem (fun r => (a.color r).val)
  rankIn : Resident x.enterRank mem (fun r => (a.enterRank r).val)
  rankOut : Resident x.exitRank mem (fun r => (a.exitRank r).val)
  groupBlock : Resident t.groupBlocks mem (fun i : Fin groups => blocks m B*i.val)
  groupColor : Resident t.groupColors mem (fun i : Fin groups => B*i.val)
  toBlock : Resident t.block mem (fun i : Fin m => (decode m B pos i).1.val)
  toOffset : Resident t.offset mem (fun i : Fin m => (decode m B pos i).2.val)
  colorBase : Resident t.colorQuota mem (fun i : Fin B => quota B*i.val)
  blockBase : Resident t.blockQuota mem (fun i : Fin (blocks m B) => quota B*i.val)

private def pairCode {k d : ℕ} (s : Fin k) (v : Fin d) := (finProdFinEquiv (s,v)).val

def rowWords (r : Fin n) : Fin 9 → ℕ :=
  let e := enter p pos a
  let c := inner p pos a
  let z := exitStage p pos a
  ![pairCode (encode (e.group r).1) (e.group r).2,(e.input r).val,(e.output r).val,
    pairCode (encode (c.group r).1) (c.group r).2,(c.input r).val,(c.output r).val,
    pairCode (encode (z.group r).1) (z.group r).2,(z.input r).val,(z.output r).val]

theorem field_eval (resident : Loaded p pos a encode x t mem) (r : Fin n) (j : Fin 9) :
    (field x t j).eval mem (r.val:Word w) = (rowWords p pos a encode r j : Word w) := by
  have g := resident.group r
  have i := resident.parentIn r
  have o := resident.parentOut r
  have c := resident.color r
  have e := resident.rankIn r
  have z := resident.rankOut r
  have gb := resident.groupBlock (encode (p.group r))
  have gc := resident.groupColor (encode (p.group r))
  have ib := resident.toBlock (p.input r)
  have ob := resident.toBlock (p.output r)
  have io := resident.toOffset (p.input r)
  have oo := resident.toOffset (p.output r)
  have cb := resident.colorBase (a.color r)
  have si := resident.blockBase (decode m B pos (p.input r)).1
  have so := resident.blockBase (decode m B pos (p.output r)).1
  fin_cases j <;>
    simp [field,rowCell,rowAdd,Expr.eval,RowOp.opcode,BinaryOp.eval,rowWords,pairCode,
      enter,inner,exitStage,leftBlock,rightBlock,g,i,o,c,e,z,gb,gc,ib,ob,io,oo,cb,si,so,
      finProdFinEquiv,add_comm] <;> rfl

/-- Execution of the nine column scans together, and readback at their final
memory addresses for every record and every output lane. -/
theorem emit {base src : ℕ} (resident : Loaded p pos a encode x t mem)
    (fits : ∀ pass ∈ passes x t base n, pass.Fits w) (before : src≤base)
    (reader : ∀ j, (field x t j).Fits w src) :
    (program w (passes x t base n)).Exec mem (result (passes x t base n) mem) (clock (passes x t base n)) ∧
    ∀ (r : Fin n) (j : Fin 9), result (passes x t base n) mem (base+j.val*n+r.val) =
      (rowWords p pos a encode r j : Word w) := by
  refine ⟨columns_exec _ _ fits,?_⟩
  intro r j
  have read := columns_read (List.ofFn (field x t)) mem before
    (fun e he => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he;exact reader i)
    j.val (by simp) r
  simp only [List.getElem_ofFn] at read
  exact read.trans (field_eval p pos a encode x t mem resident r j)

/-- The output of a single real pass may be used immediately as the parent
input of the next split, in the same memory. -/
def outputBank (base h : ℕ) (j : Fin 9) : Bank := ⟨base+j.val*2^h,h⟩

def innerEncode {G : Type} {groups B : ℕ} (encode : G ↪ Fin groups) :
    G × Fin B ↪ Fin (groups*B) :=
  (encode.prodMap (Function.Embedding.refl (Fin B))).trans finProdFinEquiv.toEmbedding

theorem inner_resident {h base src : ℕ} (hn : n=2^h) (word : n≤2^w)
    (resident : Loaded p pos a encode x t mem) (fits : ∀ pass ∈ passes x t base n, pass.Fits w)
    (before : src≤base) (reader : ∀ j, (field x t j).Fits w src) :
    let after := result (passes x t base n) mem
    let next := inner p pos a
    Resident (outputBank base h 3) after (fun r => (innerEncode encode (next.group r)).val) ∧
      Resident (outputBank base h 4) after (fun r => (next.input r).val) ∧
      Resident (outputBank base h 5) after (fun r => (next.output r).val) := by
  have wrote := (emit p pos a encode x t mem resident fits before reader).2
  have each (j : Fin 9) : Resident (outputBank base h j) (result (passes x t base n) mem)
      (fun r => rowWords p pos a encode r j) := by
    apply Resident.of_cells _ _ _ (by change n ≤ 2^h;omega) word
    intro r
    simpa only [outputBank,hn] using wrote r j
  exact ⟨each 3,each 4,each 5⟩

end Readback
end Hierarchy.ProbeStage.Native

end OAI
