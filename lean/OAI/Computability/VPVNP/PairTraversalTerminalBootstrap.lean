import OAI.Computability.VPVNP.CompressorHistoryArenaBase
import OAI.Computability.VPVNP.CompressorDescriptorTableFits

/-!
# Terminal pair bootstrap after the descriptor calendar

The first and last stored traversal-row bases give the exact accumulated row size.
A single fixed eleven-operand burst reads the persistent level headers and the last
auxiliary descriptor, initializes the terminal header and leaves every other cell intact.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalBootstrap

open BurstRAM BurstRAM.PrivateRAM CompressorRecords DescriptorSpace PhaseRecipe RowRecipe
open scoped Fin.CommRing

variable {w : ℕ}

/-- Workspace base, grammar counter base, address width, auxiliary shadow and grammar length. -/
def operand : Fin 5 → Fin 11 := ![2,4,7,3,5]

private def workspace : Expr := .publicWord 0
private def cell (base : Expr) (j : ℕ) : Expr := .load (base.add (.lit j))
private def first (F : Shape) := DescriptorParameters.firstLevel F.arity
private def pitch (F : Shape) := cell workspace (10+F.arity)
private def levels (F : Shape) := cell (first F) 28
private def lastLevel (F : Shape) := (first F).add (((levels F).sub (.lit 1)).mul (pitch F))
private def radix := Expr.binary .shiftLeft (.lit 1) (.publicWord 2)
private def high := (workspace.add (radix.mul radix)).sub (.lit 32)

/-- The histogram begins after all reserved auxiliary fields, including both padded exterior cuts. -/
def shadowSpan {w : ℕ} (pub : Fin 11 → Word w) (m : Memory w) : Word w := m (pub 4-1).val - pub 3 + pub 5
private def spanExpr := (((Expr.load ((.publicWord 1 : Expr).sub (.lit 1))).sub (.publicWord 3)).add (.publicWord 4))

/-- The terminal bootstrap header begins 32 words before the end of the square workspace of
radix two to the address exponent. -/
def address (base r : ℕ) := base + 2^r*2^r - 32

/-- Initialize all twenty-one public terminal header fields. The phase and both counters
start at zero. The final-width pass subsequently supplies the total and role offset. -/
def calculation (F : Shape) (cap : ℕ) : FormulaRow 18 :=
  let head := lastLevel F
  let arena := cell (first F) 14
  let finalRows := cell head 14
  let sites := (cell head 0).mul (cell head 2)
  let slots := sites.mul (cell head 1)
  let step : Expr := .lit (cap+2)
  let words := (finalRows.sub arena).add (sites.mul step)
  ⟨high, ![.lit 0, levels F, .lit 0, arena, arena, words, finalRows, sites, slots,
    cell head (F.scalarFields+5), cell head (F.scalarFields+4), cell head (F.scalarFields+6), .lit 0,
    arena.add words, .lit 0, step, first F, pitch F, cell (first F) 10, cell (first F) 11, spanExpr]⟩

/-- The fixed table has no dependence on the input size or the selected compression branch. -/
def table (F : Shape) (cap : ℕ) := LiveStageLink.widen (calculation F cap).recipe.acceptTable
  (Function.Embedding.refl _) operand

/-- Native instruction cost of the terminal bootstrap's compiled header calculation at the
chosen descriptor shape and record capacity. -/
def cost (F : Shape) (cap : ℕ) := (calculation F cap).recipe.code.length

/-- The bootstrap worker's report contains the calculation's external events and closes without
a successor state. -/
def report (F : Shape) (cap : ℕ) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w) : Report w :=
  ⟨((calculation F cap).recipe.report (pub ∘ operand) s m).events,none⟩

/-- The table accepts exactly the empty choice string, from every incoming persistent state. -/
theorem execute_table (F : Shape) (cap : ℕ) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (bits : List Bool) (fuel : ℕ) (budget : cost F cap < fuel) :
    let M := (table F cap).instantiate w pub
    execute M.program fuel (M.program.start s) m bits =
      if bits = [] then some (report F cap pub s m) else none :=
  (LiveStageLink.execute_widen_start ..).trans (execute_accept (calculation F cap).recipe (pub ∘ operand) s m bits fuel budget)

/-- Stored values needed at the calendar's terminal exit. `priorWords` counts all
traversal rows strictly before the final level, with their fixed row stride. -/
structure Header (L : Layout) (last : ℕ) where
  /-- Total words occupied by all DFS row layers before the final layer. -/
  priorWords : ℕ
  /-- Number of final base vertices before expanding their lane assignments. -/
  vertices : ℕ
  /-- Number of lane assignments per final base vertex. -/
  lanes : ℕ
  /-- Number of numbered final outgoing slots per site. -/
  degree : ℕ
  /-- Head of the final outgoing arc-width column used by the terminal prefix scan. -/
  widthHead : ℕ
  /-- Head of the inverse incidence column used to gather the incoming final half-wires. -/
  incomingHead : ℕ
  /-- Base address of the terminal prefix array used to locate each final arc's shared bits. -/
  prefixBase : ℕ
  /-- Saved initial base radix used by the terminal cursor-leaf decoder. -/
  baseRadix : ℕ
  /-- Saved initial lane radix used by the terminal cursor-leaf decoder. -/
  laneRadix : ℕ

/-- Read the external cell at a natural base and offset after conversion to the runtime word
address. -/
def atCell (m : Memory w) (head offset : ℕ) := m (((head+offset : ℕ) : Word w).val)

/-- The physical workspace, level geometry, row counts, final incidence heads, and saved
radices have the values required by terminal bootstrap. -/
structure Ready (L : Layout) (last : ℕ) (A : Header L last) (pub : Fin 11 → Word w) (m : Memory w) : Prop where
  workspace : (pub 2).val = L.base
  rows : m (pub 2+8).val = (directoryRows L : Word w)
  pitch : m (pub 2+((10+L.shape.arity : ℕ) : Word w)).val = (levelWords L : Word w)
  levels : atCell m (levelStart L 0) 28 = ((last+1 : ℕ) : Word w)
  firstBase : atCell m (levelStart L 0) 14 = (endAddress L : Word w)
  lastBase : atCell m (levelStart L last) 14 = ((endAddress L+A.priorWords : ℕ) : Word w)
  vertices : atCell m (levelStart L last) 0 = (A.vertices : Word w)
  lanes : atCell m (levelStart L last) 2 = (A.lanes : Word w)
  degree : atCell m (levelStart L last) 1 = (A.degree : Word w)
  widthHead : atCell m (levelStart L last) (L.shape.scalarFields+5) = (A.widthHead : Word w)
  incomingHead : atCell m (levelStart L last) (L.shape.scalarFields+4) = (A.incomingHead : Word w)
  prefixBase : atCell m (levelStart L last) (L.shape.scalarFields+6) = (A.prefixBase : Word w)
  baseRadix : atCell m (levelStart L 0) 10 = (A.baseRadix : Word w)
  laneRadix : atCell m (levelStart L 0) 11 = (A.laneRadix : Word w)

private theorem word_eq {x : Word w} {n : ℕ} (h : x.val = n) : x = (n : Word w) := by
  apply Fin.ext
  exact h.trans (Nat.mod_eq_of_lt (h ▸ x.isLt)).symm

variable (L : Layout) (last : ℕ) (A : Header L last) (cap : ℕ) (pub : Fin 11 → Word w) (m : Memory w)

/-- Total number of final sites, including every combination of base vertex and remaining lane
assignment. -/
def Header.sites {L last} (A : Header L last) := A.vertices*A.lanes
/-- Total words reserved for DFS rows, including the final sites at their capacity-plus-two
word pitch. -/
def Header.rowWords {L last} (A : Header L last) (cap : ℕ) := A.priorWords + A.sites*(cap+2)

/-- The 21 terminal bootstrap header words computed from the descriptor layout, selected final
state, row geometry, and public shadow data. -/
def values : Fin 21 → Word w :=
  ![0,((last+1 : ℕ) : Word w),0,(endAddress L : Word w),(endAddress L : Word w),(A.rowWords cap : Word w),
    ((endAddress L+A.priorWords : ℕ) : Word w),(A.sites : Word w),((A.sites*A.degree : ℕ) : Word w),
    (A.widthHead : Word w),(A.incomingHead : Word w),(A.prefixBase : Word w),0,
    ((endAddress L+A.rowWords cap : ℕ) : Word w),0,((cap+2 : ℕ) : Word w),(levelStart L 0 : Word w),
    (levelWords L : Word w),(A.baseRadix : Word w),(A.laneRadix : Word w),shadowSpan pub m]

private theorem eval_high (hbase : (pub 2).val = L.base) (s : Word w) (hw : 0 < w) (r : ℕ)
    (hr : (pub 7).val = r) (hrw : r < w) (h32 : 32 ≤ L.base+2^r*2^r) :
    high.eval (pub ∘ operand) s m = (address L.base r : Word w) := by
  have one : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')
  have pow : radix.eval (pub ∘ operand) s m = ((2^r : ℕ) : Word w) := by
    change (if (pub 7).val < w then Fin.ofNat _ ((1 : Word w).val <<< (pub 7).val) else 0) = _
    rw [hr,ite_eq_left hrw,one,Nat.shiftLeft_eq,Nat.one_mul]
    rfl
  change pub 2 + radix.eval (pub ∘ operand) s m * radix.eval (pub ∘ operand) s m - 32 = _
  rw [pow,word_eq hbase,address,Nat.cast_sub h32,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]

set_option maxRecDepth 4096 in
private theorem eval_values (s : Word w) (h : Ready L last A pub m) (i : Fin 21) :
    ((calculation L.shape cap).fields i).eval (pub ∘ operand) s m = values L last A cap pub m i := by
  let p := pub ∘ operand
  have head : (first L.shape).eval p s m = (levelStart L 0 : Word w) := by
    change pub 2 + ((11+L.shape.arity : ℕ) : Word w) + m (pub 2+8).val * ((L.shape.arity+3 : ℕ) : Word w) = _
    rw [h.rows,word_eq h.workspace]
    simp only [levelStart, Nat.zero_mul, Nat.add_zero, levelsBase, directoryBase, plannerTag, frameBase,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  have read {e : Expr} {x : ℕ} (eqn : e.eval p s m = (x : Word w)) (j : ℕ) :
      (cell e j).eval p s m = atCell m x j := by
    change m (e.eval p s m+(j : Word w)).val = m (((x+j : ℕ) : Word w).val)
    rw [eqn,Nat.cast_add]
  have len : (levels L.shape).eval p s m = ((last+1 : ℕ) : Word w) := (read head 28).trans h.levels
  have pt : (pitch L.shape).eval p s m = (levelWords L : Word w) := h.pitch
  have finalHead : (lastLevel L.shape).eval p s m = (levelStart L last : Word w) := by
    change (first L.shape).eval p s m + ((levels L.shape).eval p s m-1)*(pitch L.shape).eval p s m = _
    rw [head,len,pt,Nat.cast_add_one,add_sub_cancel_right]
    simp only [levelStart,Nat.zero_mul,Nat.add_zero,Nat.cast_add,Nat.cast_mul]
  have rv := (read finalHead 0).trans h.vertices
  have rl := (read finalHead 2).trans h.lanes
  have rd := (read finalHead 1).trans h.degree
  have rb := (read head 14).trans h.firstBase
  have re := (read finalHead 14).trans h.lastBase
  have sites : ((cell (lastLevel L.shape) 0).mul (cell (lastLevel L.shape) 2)).eval p s m = (A.sites : Word w) := by
    change (cell (lastLevel L.shape) 0).eval p s m * (cell (lastLevel L.shape) 2).eval p s m = _
    rw [rv,rl,Header.sites,Nat.cast_mul]
  have size : (((cell (lastLevel L.shape) 14).sub (cell (first L.shape) 14)).add
      (((cell (lastLevel L.shape) 0).mul (cell (lastLevel L.shape) 2)).mul (.lit (cap+2)))).eval p s m =
      (A.rowWords cap : Word w) := by
    change (cell (lastLevel L.shape) 14).eval p s m - (cell (first L.shape) 14).eval p s m +
      ((cell (lastLevel L.shape) 0).mul (cell (lastLevel L.shape) 2)).eval p s m * ((cap+2 : ℕ) : Word w) = _
    simp only [re,rb,sites,Header.rowWords,Nat.cast_add,Nat.cast_mul]; ring
  fin_cases i
  · rfl
  · exact len
  · rfl
  · exact rb
  · exact rb
  · exact size
  · exact re
  · exact sites
  · change ((cell (lastLevel L.shape) 0).mul (cell (lastLevel L.shape) 2)).eval p s m * (cell (lastLevel L.shape) 1).eval p s m = ((A.sites*A.degree : ℕ) : Word w)
    rw [sites,rd,Nat.cast_mul]
  · exact (read finalHead _).trans h.widthHead
  · exact (read finalHead _).trans h.incomingHead
  · exact (read finalHead _).trans h.prefixBase
  · rfl
  · change (cell (first L.shape) 14).eval p s m + _ = ((endAddress L+A.rowWords cap : ℕ) : Word w)
    rw [rb,size,Nat.cast_add]
  · rfl
  · rfl
  · exact head
  · exact pt
  · exact (read head _).trans h.baseRadix
  · exact (read head _).trans h.laneRadix
  · rfl

/-- The one-shot native table is ready for a terminal phase linker. It performs a fixed
number of probes and ticks and does not use a choice bit. -/
theorem native (s : Word w) (h : Ready L last A pub m) (r : ℕ) (hr : (pub 7).val = r)
    (hrw : r < w) (h32 : 32 ≤ L.base+2^r*2^r) (room : L.base+2^r*2^r ≤ 2^w) :
    let M := (table L.shape cap).instantiate w pub
    let rep := report L.shape cap pub s m
    execute M.program (cost L.shape cap+1) (M.program.start s) m [] = some rep ∧ rep.result = none ∧
      (∀ i : Fin 21, after m rep.events (address L.base r+i.val) = values L last A cap pub m i) ∧
      (∀ x, x < address L.base r ∨ address L.base r+21 ≤ x → after m rep.events x = m x) ∧
      rep.events.length = cost L.shape cap ∧ rep.probes = (calculation L.shape cap).recipe.reads+21 ∧
      choiceBits rep.events = [] := by
  intro M rep
  let R := calculation L.shape cap
  have hi : address L.base r+21 ≤ 2^w := by dsimp [address]; omega
  have hd : (R.dest.eval (pub ∘ operand) s m).val = address L.base r := by
    rw [show R.dest.eval (pub ∘ operand) s m = (address L.base r : Word w) from
      eval_high L pub m h.workspace s (by omega) r hr hrw h32,Fin.val_natCast,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨_,_,store,keep,work⟩ := R.execute (pub ∘ operand) s m (hd ▸ hi)
  refine ⟨execute_table L.shape cap pub s m [] _ (Nat.lt_succ_self _),rfl,?_,?_,work⟩
  · intro i
    exact (hd ▸ store i).trans (eval_values L last A cap pub m s h i)
  · intro x hx
    exact keep x (hd ▸ hx)

end PairSimulation.TerminalBootstrap

end VPVNP
end Computability
end OAI
