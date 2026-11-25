import OAI.ThreeFlat.RAM.PhysicalPinsNat
import OAI.ThreeFlat.RAM.TraceBucketLayout
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.HeaderScanProcedure

namespace OAI
/-! # Selected initial chronological nodes on the physical tick tape -/

namespace ThreeFlat.RAM.HistoryInitialSeed

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open scoped Fin.CommRing

/-- The selected guard has bumped its chronological cursor before entry.
The node result directory has eight words per chronological node. Every local
arena bank has V words, and successive node arenas are V² words apart. -/
structure Layout where
  cursor : ℕ
  nodes : ℕ
  output : ℕ
  arena : ℕ
  V : ℕ
  ctrl : ℕ
  intervals : ℕ
  bounds : ℕ
  trace : TraceBucketAtom.Layout
  rawPublic : ℕ

def Layout.hidden (A : Layout) := A.trace.lowRows*A.trace.shape.stride

structure Site where
  index : ℕ
  lane : ℕ
  stage : ℕ
  extPins : ℕ
  deriving DecidableEq

def site (A : Layout) (m : ℕ→ℕ) : Site :=
  let i := m A.cursor-1
  let n := A.nodes+8*i
  let kernel := m (n+5)
  ⟨i,m (kernel+3),m (kernel+4),m (n+7)⟩

def Site.rows (z : Site) (A : Layout) := A.trace.relays +
  (if z.stage=0 then A.trace.gates+A.trace.tags+A.hidden else 0)
def Site.bits (z : Site) (A : Layout) := if z.stage=0 then A.hidden else 0
def Site.stream (z : Site) (A : Layout) := A.arena+z.index*(A.V*A.V)
def Site.extBase (z : Site) (A : Layout) := z.stream A+A.V
def Site.resultBase (z : Site) (A : Layout) := A.output+8*z.index

/-- The three native commands materialize the physical trace/relay records,
the interleaved endpoint sources, and the six-word selected-node result. -/
def Site.words (z : Site) (A : Layout) : Fin 42 → ℕ :=
  let t := A.ctrl
  let dst := z.stream A
  let ext := z.extBase A
  let out := z.resultBase A
  let rows := z.rows A
  ![t+2,t+23,
    t+23,dst,0,0,0,0,dst+4*rows,
    t+29,ext,9,0,0,0,ext+z.extPins,
    t+33,out,10,0,0,0,out+6,
    0,z.lane,z.stage,0,dst,4*rows,
    ext,z.extPins,A.intervals+4*z.lane,A.bounds,
    out,6,t+36,
    dst,z.extPins+2*A.trace.bank,rows,z.bits A,ext,z.extPins]

private abbrev E := Formula 1
private def index : ℕ → List E → E → E
  | _,[],_ => .lit 0
  | n,x::xs,k => eqz k (.lit n) x (index (n+1) xs k)

private def recs (A : Layout) : List E :=
  let lit := @Formula.lit 1
  let get (ptr : E) (j : ℕ) : E := .load (add ptr (lit j))
  let i := Formula.cut (.load (lit A.cursor)) (lit 1)
  let node := add (lit A.nodes) (mul (lit 8) i)
  let kernel := get node 5
  let lane := get kernel 3
  let stage := get kernel 4
  let ext := get node 7
  let dst := add (lit A.arena) (mul i (lit (A.V*A.V)))
  let pins := add dst (lit A.V)
  let out := add (lit A.output) (mul (lit 8) i)
  let rows := add (lit A.trace.relays)
    (eqz stage (lit 0) (lit (A.trace.gates+A.trace.tags+A.hidden)) (lit 0))
  let bits := eqz stage (lit 0) (lit A.hidden) (lit 0)
  let count := mul (lit 4) rows
  [lit (A.ctrl+2),lit (A.ctrl+23),
   lit (A.ctrl+23),dst,lit 0,lit 0,lit 0,lit 0,add dst count,
   lit (A.ctrl+29),pins,lit 9,lit 0,lit 0,lit 0,add pins ext,
   lit (A.ctrl+33),out,lit 10,lit 0,lit 0,lit 0,add out (lit 6),
   lit 0,lane,stage,lit 0,dst,count,
   pins,ext,add (lit A.intervals) (mul (lit 4) lane),lit A.bounds,
   out,lit 6,lit (A.ctrl+36),
   dst,add ext (lit (2*A.trace.bank)),rows,bits,pins,ext]

def formula (A : Layout) : E := index 0 (recs A) (.cut (.reg 0) (.lit A.ctrl))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem natural (A : Layout) (W : ℕ) (pub : Param → ℕ) (m : ℕ→ℕ) (i : Fin 42) :
    (formula A).natural W pub m (fun _ => A.ctrl+i.val)=(site A m).words A i := by
  by_cases first : m (m (A.nodes+8*(m A.cursor-1)+5)+4)=0 <;>
    fin_cases i <;>
    simp [formula,recs,index,site,Site.words,Site.rows,Site.bits,Site.stream,Site.extBase,
      Site.resultBase,eqz,add,mul,Formula.natural,natOp,natTest,first]

def seed (W : ℕ) (A : Layout) : Procedure W :=
  PhysicalInputPhases.writing (HeaderScan.closed (formula A)) Fin.elim0 A.ctrl 42

/-- All 42 header words have a fixed formula tree. Changing the lane width,
the underlying table size or any address changes only literal operands. -/
theorem seed_work (A B : Layout) : (formula A).work=(formula B).work := rfl

private theorem index_work (n : ℕ) (xs : List E) (k : E) :
    (index n xs k).work=(k.work+2)*xs.length+(xs.map Formula.work).sum+1 := by
  induction xs generalizing n with
  | nil=>simp [index,Formula.work]
  | cons x rest ih=>
    simp only [index,eqz,Formula.work,ih,List.length_cons,List.map_cons,List.sum_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem seed_budget (A : Layout) : 4+42*(2*(formula A).work+4) ≤ 400000 := by
  rw [formula,index_work]
  norm_num [recs,Formula.work,add,mul,eqz]

theorem seed_spec (W : ℕ) (A : Layout) (z : Site) (pre : Memory W → Prop)
    (room : A.ctrl+42<2^W)
    (live : ∀ m₀, pre m₀ → ∀ m : Memory W, DescriptorScan.agreesOutside A.ctrl (A.ctrl+42) m m₀ →
      site A (fun i => (m i).val)=z ∧ ∀ j : Fin 42,
        (formula A).Fits W (fun _ => 0) (fun i => (m i).val) (fun _ => A.ctrl+j.val)) :
    (seed W A).Spec pre (fun m o => o=fillSegment A.ctrl 42
      (fun a => if ok : a-A.ctrl<42 then (z.words A ⟨a-A.ctrl,ok⟩ : Word W) else 0) m)
      (4+42*(2*(formula A).work+4)) := by
  unfold seed
  rw [← HeaderScan.binds_closed (w:=W) (formula A)]
  apply PhysicalInputPhases.writing_spec _ _ _ _ room
  intro m₀ hm a m lo hi same
  let j : Fin 42 := ⟨a.val-A.ctrl,by omega⟩
  have idx : A.ctrl+j.val=a.val := by dsimp [j]; omega
  obtain ⟨found,fit⟩ := live m₀ hm m same
  rw [HeaderScan.eval_closed]
  have reg : (fun _ : Fin 1 => a) = (fun _ : Fin 1 => ((A.ctrl+j.val : ℕ) : Word W)) := by
    rw [idx]; simp
  rw [reg]
  have origin := Formula.value_eq_natural (formula A) (fun _ => 0) (fun i => (m i).val)
    (fun _ => A.ctrl+j.val) (fit j)
  rw [natural A W (fun _=>0) (fun i=>(m i).val) j,found] at origin
  simpa [dite_eq_left j.isLt,j] using origin

end ThreeFlat.RAM.HistoryInitialSeed

end OAI
