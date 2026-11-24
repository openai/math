import OAI.Computability.VPVNP.CompressorScatterCall
import OAI.Computability.VPVNP.CompressorRecordsBlockPlanner
import OAI.Computability.VPVNP.CompressorShrinkSliceSweep

/-!
# A fixed native surviving-slice visit for one subdivision

Each of the four role passes has a constant public bank. Its ordinal gives
the dense motif number and subdivision index. Four reads obtain the absolute
arc number, the common layout, the repetition word and the selected payload.
The call writes the balanced width and both endpoint directories directly.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep.SurvivingNative

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM RowRecipe PhaseRecipe
open scoped Fin.CommRing

variable {w : ℕ}

/-- The eleven public operand words shared by the visits for a surviving role. -/
abbrev Public (w : ℕ) := Fin 11 → Word w

/-- The fixed role and subdivision count accompany the level's array heads. -/
def params {n A : ℕ} (T : Allocation w n A) (t : Fin 4) (abs layout : Word w) : Public w :=
  ![T.subdiv t,t.val,T.termBase,T.termStride,abs,layout,T.selectors,T.widthBase,T.stride,T.widthEnd,T.recordStride]

private abbrev div (x y : Word w) := BinaryOp.div.eval x y
private abbrev mod (x y : Word w) := BinaryOp.mod.eval x y
private abbrev flag (x : Word w) := div x x

/-- All dynamic fields of a single call, in machine-word arithmetic. -/
structure Data (w : ℕ) where
  /-- Zero-based index of the subdivision visited within the motif and role. -/
  rank : Word w
  /-- Number of subdivisions into which the role's width is split. -/
  count : Word w
  /-- Full role width obtained by adding the selected payload to the repetition contribution. -/
  width : Word w
  /-- Address of the total-width cell at the start of the motif and role's interval record. -/
  total : Word w
  /-- Base of the output width row for this absolute arc and role. -/
  dst : Word w

/-- Decode the motif and subdivision from the cursor and read the arc ID, layout, repetition
count, and payload to form the visit's data. -/
def read (p : Public w) (st : Word w) (m : Memory w) : Data w :=
  let i := div st (p 0)
  let j := mod st (p 0)
  let four : Word w := 2+2
  let term := p 2+i*p 3
  let id := m (p 4+i).val
  let layout := m (p 5).val
  let u := m (term+1).val
  let payload := m (term+2+(layout*four+p 1)).val
  ⟨j,p 0,u*p 6+payload,p 9+(i*four+p 1)*p 10,p 7+(id*four+p 1)*p 8⟩

/-- Absolute ID, common layout, repetition word and selected payload word,
in the order in which the instruction table reads them. -/
def readAddresses (p : Public w) (st : Word w) (m : Memory w) : Fin 4 → Word w :=
  let i := div st (p 0)
  let term := p 2+i*p 3
  ![p 4+i,p 5,term+1,term+2+(m (p 5).val*(2+2)+p 1)]

/-- Width assigned to this subdivision, including one extra unit for the first subdivisions
that share the remainder. -/
def Data.piece (d : Data w) := div d.width d.count + flag (div (mod d.width d.count) (d.rank+1))

/-- Starting offset of this subdivision in the balanced split of the role's width. -/
def Data.offset (d : Data w) :=
  let rem := mod d.width d.count
  let pick := flag (div rem (d.rank+1))
  d.rank * div d.width d.count + (rem + (d.rank-rem)*pick)

/-- Number of positive-width subdivisions in the balanced split. -/
def Data.live (d : Data w) := d.width + (d.count-d.width)*flag (div d.width d.count)

/-- The thirteen destination cells for the total, piece width, interval metadata, copy frame,
and endpoint references. -/
def Data.addresses (d : Data w) : Fin 13 → Word w :=
  let B := d.total+1
  let two : Word w := 2
  let four := two+two
  let frame := B+four+(d.count+d.count)
  let pair := frame+3*d.rank
  ![d.total,d.dst+d.rank,B,B+1,B+two,B+3+d.rank,B+3+d.count,B+four+d.count+d.rank,
    pair,pair+1,pair+two,frame+3*d.count+d.rank,frame+four*d.count+d.rank]

/-- The thirteen field values to store, ordered to match the visit's destination addresses. -/
def Data.values (d : Data w) : Fin 13 → Word w :=
  ![d.width,d.piece,d.width,d.width,d.live,flag d.piece,0,d.offset,d.offset,0,d.piece,d.rank,d.rank]

/-- A list of register assignments for the worker with 64 private registers and eleven public
operands. -/
abbrev Lines := List (Assign 64 11)

private def readLines : Lines :=
  [⟨0,.state⟩,⟨1,.publicWord 0⟩,⟨2,.binary .div 0 1⟩,⟨3,.binary .mod 0 1⟩,
   ⟨4,.literal 1⟩,⟨5,.literal 2⟩,⟨6,.binary .add 5 5⟩,⟨7,.publicWord 1⟩,
   ⟨8,.publicWord 4⟩,⟨8,.binary .add 8 2⟩,⟨8,.read 8⟩,
   ⟨9,.publicWord 5⟩,⟨9,.read 9⟩,
   ⟨10,.publicWord 3⟩,⟨10,.binary .mul 2 10⟩,⟨11,.publicWord 2⟩,⟨10,.binary .add 11 10⟩,
   ⟨11,.binary .add 10 4⟩,⟨11,.read 11⟩,
   ⟨12,.binary .mul 9 6⟩,⟨12,.binary .add 12 7⟩,⟨13,.binary .add 10 5⟩,
   ⟨13,.binary .add 13 12⟩,⟨13,.read 13⟩,⟨14,.publicWord 6⟩,
   ⟨14,.binary .mul 11 14⟩,⟨14,.binary .add 14 13⟩,
   ⟨15,.binary .mul 8 6⟩,⟨15,.binary .add 15 7⟩,⟨16,.publicWord 8⟩,
   ⟨15,.binary .mul 15 16⟩,⟨16,.publicWord 7⟩,⟨15,.binary .add 16 15⟩,
   ⟨16,.binary .mul 2 6⟩,⟨16,.binary .add 16 7⟩,⟨17,.publicWord 10⟩,
   ⟨16,.binary .mul 16 17⟩,⟨17,.publicWord 9⟩,⟨16,.binary .add 17 16⟩]

private def valueLines : Lines :=
  [⟨17,.binary .div 14 1⟩,⟨18,.binary .mod 14 1⟩,⟨19,.binary .add 3 4⟩,
   ⟨19,.binary .div 18 19⟩,⟨19,.binary .div 19 19⟩,⟨20,.binary .add 17 19⟩,
   ⟨21,.binary .sub 3 18⟩,⟨21,.binary .mul 21 19⟩,⟨21,.binary .add 18 21⟩,
   ⟨22,.binary .mul 3 17⟩,⟨22,.binary .add 22 21⟩,
   ⟨23,.binary .div 17 17⟩,⟨24,.binary .sub 1 14⟩,⟨24,.binary .mul 24 23⟩,
   ⟨24,.binary .add 14 24⟩,⟨25,.binary .div 20 20⟩,⟨26,.literal 0⟩,⟨27,.literal 3⟩]

private def addressLines : Lines :=
  [⟨29,.binary .add 16 4⟩,⟨30,.binary .add 15 3⟩,⟨31,.binary .add 29 4⟩,
   ⟨32,.binary .add 29 5⟩,⟨33,.binary .add 29 27⟩,⟨34,.binary .add 33 3⟩,
   ⟨35,.binary .add 33 1⟩,⟨36,.binary .add 29 6⟩,⟨37,.binary .add 36 1⟩,⟨37,.binary .add 37 3⟩,
   ⟨38,.binary .add 1 1⟩,⟨38,.binary .add 36 38⟩,⟨39,.binary .mul 27 3⟩,
   ⟨39,.binary .add 38 39⟩,⟨40,.binary .add 39 4⟩,⟨41,.binary .add 39 5⟩,
   ⟨42,.binary .mul 27 1⟩,⟨42,.binary .add 38 42⟩,⟨42,.binary .add 42 3⟩,
   ⟨43,.binary .mul 6 1⟩,⟨43,.binary .add 38 43⟩,⟨43,.binary .add 43 3⟩,⟨44,.binary .add 0 4⟩]

/-- Assignments that read the term, compute the balanced piece, and form the addresses of its
output fields. -/
def lines : Lines := readLines ++ valueLines ++ addressLines

/-- Registers containing the destination addresses of the thirteen scatter writes. -/
def destinations : Fin 13 → Fin 64 := ![16,30,29,31,32,34,35,37,39,40,41,42,43]
/-- Registers containing the values for the thirteen scatter writes. -/
def sources : Fin 13 → Fin 64 := ![14,20,14,14,24,25,26,22,22,26,20,3,3]
/-- Ordered address-register and value-register pairs consumed by the scatter worker. -/
def writes := List.ofFn fun f : Fin 13 => (destinations f,sources f)
/-- Native instruction sequence that evaluates the assignments and performs all thirteen
writes. -/
def ops := ScatterCall.ops lines writes
/-- Schedulable surviving-piece worker returning the next subdivision cursor from register 44. -/
def pass : Schedule.Pass := ⟨_,_,_,template ops 44⟩
/-- Event report and return word for a surviving-piece call at the supplied cursor and memory. -/
abbrev report (p : Public w) (st : Word w) (m : Memory w) := ScatterCall.report lines writes 44 p st m

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2200000 in
theorem registers (p : Public w) (st : Word w) (m : Memory w) :
    let rs := (evaluate p st m lines (fun _ => 0)).2
    let d := read p st m
    (∀ f, rs (destinations f) = d.addresses f ∧ rs (sources f) = d.values f) ∧ rs 44 = st+1 := by
  constructor
  · intro f; fin_cases f <;> exact ⟨rfl,rfl⟩
  · rfl

/-- Ordered address and value pairs describing the surviving-piece call's effect on memory. -/
def stores (d : Data w) := List.ofFn fun f : Fin 13 => (d.addresses f,d.values f)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem native (p : Public w) (st : Word w) (m : Memory w) :
    let T := (pass.table.instantiate w p).program
    let rep := report p st m
    execute T (1+ops.length) (T.start st) m [] = some rep ∧ rep.result = some (st+1) ∧
      after m rep.events = ScatterCall.applyStores m (stores (read p st m)) ∧
      rep.probes = 17 ∧ rep.events.length = ops.length ∧ choiceBits rep.events = [] := by
  obtain ⟨fields,ret⟩ := registers p st m
  obtain ⟨steps,probes,bits⟩ := ScatterCall.cost lines writes 44 p st m
  refine ⟨ScatterCall.native lines writes 44 p st m,congrArg some ret,?_,probes.trans (by decide),?_,bits⟩
  · rw [ScatterCall.effect]
    unfold stores ScatterCall.stores writes
    rw [List.map_ofFn]
    exact congrArg (ScatterCall.applyStores m) (congrArg List.ofFn (funext fun f => Prod.ext (fields f).1 (fields f).2))
  · exact steps.trans (by simp [ops,ScatterCall.ops])

/-- Planner heads for four passes, with one runtime ordinal per live piece. -/
structure Heads where
  /-- Recipe expression for the number of dense motifs scanned at this level. -/
  motifs : Expr
  /-- Recipe expression for the base address of the selected motif records. -/
  terms : Expr
  /-- Recipe expression for the spacing in words between successive selected motif records. -/
  termStride : Expr
  /-- Recipe expression for the base of the table mapping dense motif numbers to absolute arc
  IDs. -/
  absolute : Expr
  /-- Recipe expression for the address of the common layout word used to select payload
  columns. -/
  layout : Expr
  /-- Recipe expression for the selector width contributed by each repetition. -/
  selectors : Expr
  /-- Recipe expression for the base of the output width rows indexed by absolute arc and role. -/
  widthBase : Expr
  /-- Recipe expression for the start of the interval records indexed by dense motif and role. -/
  intervalBase : Expr

/-- Schedule one role's surviving-piece pass with one call per motif and subdivision. -/
def visits (subdiv : Fin 4 → ℕ) (H : Heads) (t : Fin 4) : BlockPlanner.Visit :=
  let stride := ∑ r, subdiv r
  ⟨pass,.lit 0,H.motifs.mul (.lit (subdiv t)),
    ![.lit (subdiv t),.lit t.val,H.terms,H.termStride,H.absolute,H.layout,H.selectors,H.widthBase,
      .lit stride,H.intervalBase,.lit (5+7*stride)]⟩

/-- List the four surviving-piece visits in role order. -/
def phases (subdiv : Fin 4 → ℕ) (H : Heads) := List.ofFn (visits subdiv H)

/-- Evaluate the four fixed visits against the allocation's actual heads.
Only the phase stop depends on the number of dense motifs. -/
theorem visit_fields {n A : ℕ} (T : Allocation w n A) (H : Heads) (t : Fin 4)
    (pub : Fin 5 → Word w) (st abs layout : Word w) (m : Memory w)
    (hm : H.motifs.eval pub st m = (n : Word w)) (ht : H.terms.eval pub st m = (T.termBase : Word w))
    (hs : H.termStride.eval pub st m = (T.termStride : Word w)) (ha : H.absolute.eval pub st m = abs)
    (hl : H.layout.eval pub st m = layout) (hsel : H.selectors.eval pub st m = T.selectors)
    (hw : H.widthBase.eval pub st m = (T.widthBase : Word w))
    (hb : H.intervalBase.eval pub st m = (T.widthEnd : Word w)) :
    let v := visits T.subdiv H t
    v.initial.eval pub st m = 0 ∧ v.stop.eval pub st m = ((n*T.subdiv t : ℕ) : Word w) ∧
      (fun i => (v.params i).eval pub st m) = params T t abs layout := by
  refine ⟨rfl,?_,?_⟩
  · change H.motifs.eval pub st m * (T.subdiv t : Word w) = _
    rw [hm,Nat.cast_mul]
  · funext i
    change Fin 11 at i
    fin_cases i <;> first | exact ht | exact hs | exact ha | exact hl | exact hsel | exact hw | exact hb | rfl

end CompressorRecords.ShrinkSliceSweep.SurvivingNative

end VPVNP
end Computability
end OAI
