import OAI.Hierarchy.GridApproximationAdvice
import OAI.Hierarchy.GridOrderedNetworkRAM
import OAI.Hierarchy.GridDescription
import OAI.Hierarchy.GridThroughOrdered

namespace OAI
/-! # Publishing the expanded contraction from one compact approximation

The original external bits occupy address zero onwards. A native copy first
saves them above the output interval. One bounded sweep then writes constants,
rail pins, zeros, network records, and field products in physical address order.
The sweep reads all approximation-dependent dimensions from the packed tape.
-/

namespace Hierarchy.GridPaddedCellImage

open ThreeFlat RAM RAM.DescriptorExpr RAM.BitLayout
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Catalyst UniversalGrid
open GridOrderedNetworkRAM RAM.PhysicalProcedure
open scoped Fin.CommRing

noncomputable section
set_option maxRecDepth 8192
variable {F : Type} [Field F] [Fintype F] {w k p e L : ℕ}

structure Banks where
  compact : ℕ
  pin : ℕ
  edge : ℕ
  exterior : ℕ
  limit : ℕ

def Banks.layout (b : Banks) (k : ℕ) : GridOrderedRowRAM.Layout :=
  ⟨0,b.compact+(6+k),b.pin,b.edge⟩

private def substitute {s t : ℕ} (d : Fin s → Term w t 0) :
    {n : ℕ} → Term w s n → Term w t n
  | _, .result i => .result i
  | _, .bind (.parameter i) body => ((d i).rename Fin.elim0).letThen (substitute d body)
  | _, .bind (.literal v) body => .bind (.literal v) (substitute d body)
  | _, .bind (.load a) body => .bind (.load a) (substitute d body)
  | _, .bind (.binary op a b) body => .bind (.binary op a b) (substitute d body)
  | _, .bind (.select q a b y z) body => .bind (.select q a b y z) (substitute d body)

private theorem substitution {s t n : ℕ} (d : Fin s → Term w t 0) (f : Term w s n)
    (data : Fin t → Word w) (m : Memory w) (vs : Fin n → Word w) :
    (substitute d f).eval data m vs = f.eval (fun i => (d i).eval data m Fin.elim0) m vs := by
  have empty {n : ℕ} (v : Fin n → Word w) :
      v ∘ (Fin.elim0 : Fin 0 → Fin n) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  induction f with
  | result i => rfl
  | bind op body ih =>
    cases op <;> simp only [substitute,Term.eval,Term.eval_letThen,Term.eval_rename,Op.eval,ih,empty]

private theorem substitute_binds {s t n : ℕ} (d : Fin s → Term w t 0) (f : Term w s n)
    {D : ℕ} (pos : 1 ≤ D) (fit : ∀ i,(d i).binds ≤ D) :
    (substitute d f).binds ≤ D*f.binds := by
  induction f with
  | result i => simp [substitute,Term.binds]
  | bind op body ih =>
    cases op <;> simp only [substitute,Term.binds,Term.binds_letThen,Term.binds_rename,
      Nat.mul_add,Nat.mul_one] <;> first | omega | exact (Nat.add_le_add (fit _) ih).trans_eq (Nat.add_comm ..)

private abbrev E (w n : ℕ) := Term w 12 n

private def fld {n : ℕ} (i : ℕ) : E w n :=
  .load (.binary .add (.parameter 0) (.literal i))

private def copies {n : ℕ} : E w n := .binary .mul (.parameter 6) (fld 3)
private def privateCount {n : ℕ} : E w n := .binary .add (.parameter 7) (.binary .mul (.parameter 6) (fld 2))
private def rowAt {n : ℕ} : E w n := .binary .add (.binary .add (.literal 2) (.parameter 5)) privateCount
private def eqAt {n : ℕ} : E w n := .binary .add rowAt (.binary .mul (.literal 11) copies)
private def mulAt {n : ℕ} : E w n := .binary .add eqAt (.binary .mul (.literal 11) (.parameter 8))
private def stopAt {n : ℕ} : E w n :=
  .binary .add mulAt (.binary .mul (.parameter 9) (.parameter 9))
private def tableAt {n : ℕ} : E w n := .binary .add
  (.binary .add (.parameter 1) (.binary .mul (.literal 11) (fld 3)))
  (.binary .mul (.literal 3) (fld 4))

private def args (edge : Bool) : Fin 12 → E w 0 :=
  ![if edge then eqAt else rowAt, if edge then .literal 0 else fld 4,
    if edge then .literal 0 else fld 3, if edge then .literal 0 else fld 2,
    .literal edge.toNat,.parameter 5,.parameter 7,.parameter 10,.parameter 11,
    .parameter 1,.parameter 2,.parameter 3]

def expression (w : ℕ) : E w 1 :=
  let a := Term.result 0
  .select .lt a (.literal 2) a <|
  .select .lt a (.binary .add (.literal 2) (.parameter 5))
    (.load (.binary .add (.parameter 4) (.binary .sub a (.literal 2)))) <|
  .select .lt a rowAt (.literal 0) <|
  .select .lt a eqAt (substitute (args false) (GridOrderedRowRAM.program w)) <|
  .select .lt a mulAt (substitute (args true) (GridOrderedRowRAM.program w)) <|
  .select .lt a stopAt (.load (.binary .add tableAt (.binary .sub a mulAt))) (.literal 0)

def publicWords (b : Banks) (k pins length shared edges fieldSize : ℕ) (z one : Word w) :
    Fin 12 → Word w :=
  ![(b.compact:Word w),((b.layout k).gate:Word w),(b.pin:Word w),(b.edge:Word w),
    (b.exterior:Word w),(pins:Word w),(length:Word w),(shared:Word w),(edges:Word w),
    (fieldSize:Word w),z,one]

/-- The uniform-height scan and the preceding high copy depend only on the
grid dimensions, the fixed field and the public memory map. -/
def build (b : Banks) (k pins length shared edges fieldSize : ℕ) (z one : Word w) : Procedure w :=
  (PhysicalInputPhases.copying w 0 pins b.exterior).seq
    (PhysicalInputPhases.writing (expression w)
      (publicWords b k pins length shared edges fieldSize z one) 0 b.limit)

variable (X : Approximation F k p) (W : Wiring (Fin e) (Port p X.width) L) (code : FieldCode F w)

private abbrev imageNetwork := W.network X.network
private abbrev data (b : Banks) := publicWords b k (e*2) L W.internal W.equal.length
  (Fintype.card F) (code.encode 0) (code.encode 1)

def target (pin : Fin (e*2) → Bool) := memory (imageNetwork X W) code pin (fun _ => false)

/-- Only specific original tape words, the true per-copy source pointers and
the two physical pointers per appended equality are used by the sweep. -/
structure Mounted (b : Banks) (m : Memory w) : Prop where
  records : GridOrderedNetworkRAM.Mounted W X.network code (b.layout k) m
  header : ∀ j : Fin 6, m (b.compact+j.val) = (GridApproximationAdvice.header X j : Word w)
  product : ∀ x y : F, m (b.compact+(GridApproximationAdvice.multBase X+
      (Fintype.card F*((Fintype.equivFin F) x).val+((Fintype.equivFin F) y).val))) =
    code.encode (x*y)

theorem mounted_of_packed (b : Banks) (B : ℕ) (m original : Memory w)
    (records : GridOrderedNetworkRAM.Mounted W X.network code (b.layout k) m)
    (cap : GridApproximationAdvice.wordCount X ≤ 12*B)
    (keep : ∀ i < GridApproximationAdvice.wordCount X, m (b.compact+i) =
      GridApproximationAdvice.paddedMemory X code B b.compact original (b.compact+i)) :
    Mounted X W code b m := by
  constructor
  · exact records
  · intro j
    have hi : j.val < GridApproximationAdvice.wordCount X := by
      unfold GridApproximationAdvice.wordCount GridApproximationAdvice.multBase
        GridApproximationAdvice.portBase GridApproximationAdvice.rowBase
      omega
    rw [keep _ hi,GridApproximationAdvice.paddedMemory_eq X code B _ original _ hi cap]
    exact GridApproximationAdvice.packed_header X code _ _ _
  · intro x y
    let q := Fintype.card F
    let ix := ((Fintype.equivFin F) x).val
    let iy := ((Fintype.equivFin F) y).val
    have hx : ix+1 ≤ q := ((Fintype.equivFin F) x).isLt
    have hy : iy < q := ((Fintype.equivFin F) y).isLt
    have bound := Nat.mul_le_mul_left q hx
    rw [Nat.mul_succ] at bound
    have hi : GridApproximationAdvice.multBase X+(q*ix+iy) < GridApproximationAdvice.wordCount X := by
      change _ < GridApproximationAdvice.multBase X+q*q
      omega
    rw [keep _ hi,GridApproximationAdvice.paddedMemory_eq X code B _ original _ hi cap]
    exact GridApproximationAdvice.packed_product X code _ _ _ _

/-- Read every compact cell directly from advice; the only additional words
are the port and equality pointers published for this setting. -/
theorem mounted_banks (b : Banks) (B : ℕ) (m original : Memory w)
    (cap : GridApproximationAdvice.wordCount X ≤ 12*B)
    (keep : ∀ i < GridApproximationAdvice.wordCount X, m (b.compact+i) =
      GridApproximationAdvice.paddedMemory X code B b.compact original (b.compact+i))
    (pins : ∀ (c : Fin L) (i : Fin (GridApproximationAdvice.portCount X)),
      m (b.pin+GridApproximationAdvice.portCount X*c.val+i.val) =
      (sourceAddress (W.copyInput c i):Word w))
    (lhs : ∀ a : Fin W.equal.length,m (b.edge+2*a.val+0)=
      (sourceAddress (Wiring.source (W.equal.get a).1):Word w))
    (rhs : ∀ a : Fin W.equal.length,m (b.edge+2*a.val+1)=
      (sourceAddress (Wiring.source (W.equal.get a).2):Word w)) :
    Mounted X W code b m := by
  apply mounted_of_packed X W code b B m original _ cap keep
  refine ⟨?_,pins,lhs,rhs⟩
  intro i j
  have hi : GridApproximationAdvice.rowBase X+(11*i.val+j.val) < GridApproximationAdvice.wordCount X := by
    unfold GridApproximationAdvice.wordCount GridApproximationAdvice.multBase GridApproximationAdvice.portBase
    have := i.isLt; have := j.isLt; omega
  change m (b.compact+(6+k)+11*i.val+j.val)=_
  rw [show b.compact+(6+k)+11*i.val+j.val =
    b.compact+(GridApproximationAdvice.rowBase X+(11*i.val+j.val)) by
      unfold GridApproximationAdvice.rowBase; omega,keep _ hi,
    GridApproximationAdvice.paddedMemory_eq X code B _ original _ hi cap]
  exact GridApproximationAdvice.packed_row X code _ _ i j

structure Fits (b : Banks) : Prop where
  stop : b.limit < 2^w
  image : footprint (imageNetwork X W) ≤ b.limit
  high : b.limit ≤ b.exterior
  afterCompact : b.exterior+e*2 ≤ b.compact
  afterPin : b.exterior+e*2 ≤ b.pin
  afterEdge : b.exterior+e*2 ≤ b.edge
  exterior : b.exterior+e*2 < 2^w
  compact : b.compact+GridApproximationAdvice.wordCount X < 2^w
  ports : b.pin+Fintype.card (Port p X.width)*L ≤ 2^w
  edges : b.edge+2*W.equal.length ≤ 2^w
  source : 2+Fintype.card (Port p X.width)+X.network.internal < 2^w
  cells : X.network.cells < 2^w
  eleven : 11 < 2^w

private theorem Mounted.agree {b : Banks} {m m' : Memory w} (h : Mounted X W code b m)
    (range : ℕ) (sources : range ≤ b.compact ∧ range ≤ b.pin ∧ range ≤ b.edge)
    (frame : ∀ a,range ≤ a → m' a=m a) : Mounted X W code b m' where
  records := {
    gate := fun i j => (frame _ (by dsimp [Banks.layout]; omega)).trans (h.records.gate i j)
    pin := fun c j => (frame _ (by dsimp [Banks.layout]; omega)).trans (h.records.pin c j)
    left := fun i => (frame _ (by dsimp [Banks.layout]; omega)).trans (h.records.left i)
    right := fun i => (frame _ (by dsimp [Banks.layout]; omega)).trans (h.records.right i) }
  header j := (frame _ (by omega)).trans (h.header j)
  product x y := (frame _ (by omega)).trans (h.product x y)

private theorem field_eval {n : ℕ} (b : Banks) (m : Memory w) (H : Mounted X W code b m)
    (fit : Fits (w:=w) X W b) (vs : Fin n → Word w) (j : Fin 6) :
    (fld j.val).eval (data X W code b) m vs =
      (GridApproximationAdvice.header X j : Word w) := by
  have bound := fit.compact
  unfold GridApproximationAdvice.wordCount GridApproximationAdvice.multBase
    GridApproximationAdvice.portBase GridApproximationAdvice.rowBase at bound
  have hj := j.isLt
  have hj' : b.compact+j.val < 2^w := by omega
  simpa [fld,data,publicWords,BinaryOp.eval,←Nat.cast_add,Fin.val_cast_of_lt hj'] using H.header j

private structure Coordinates {n : ℕ} (b : Banks) (m : Memory w) (vs : Fin n → Word w) : Prop where
  row : rowAt.eval (data X W code b) m vs = (rowStart W X.network : Word w)
  eq : eqAt.eval (data X W code b) m vs = (edgeStart W X.network : Word w)
  mul : mulAt.eval (data X W code b) m vs = (rowStop W X.network : Word w)
  stop : stopAt.eval (data X W code b) m vs = (footprint (imageNetwork X W) : Word w)
  table : tableAt.eval (data X W code b) m vs =
    ((b.compact+GridApproximationAdvice.multBase X : ℕ) : Word w)

private theorem coordinates {n : ℕ} (b : Banks) (m : Memory w) (H : Mounted X W code b m)
    (fit : Fits (w:=w) X W b) (vs : Fin n → Word w) : Coordinates X W code b m vs := by
  have f2 := field_eval X W code b m H fit vs (2:Fin 6)
  have f3 := field_eval X W code b m H fit vs (3:Fin 6)
  have f4 := field_eval X W code b m H fit vs (4:Fin 6)
  change (fld 2).eval _ _ _ = (X.network.internal:Word w) at f2
  change (fld 3).eval _ _ _ = (X.network.cells:Word w) at f3
  change (fld 4).eval _ _ _ = (Fintype.card (Port p X.width):Word w) at f4
  have sizes := W.network_sizes X.network
  constructor <;>
    simp only [rowAt,eqAt,mulAt,stopAt,tableAt,copies,privateCount,Term.eval_binary,
      Term.eval_parameter,Term.eval_literal,BinaryOp.eval,f2,f3,f4] <;>
    simp [rowStart,edgeStart,rowStop,data,publicWords,cellsBase,hiddenBase,footprint,mulBase,
      GridApproximationAdvice.multBase,GridApproximationAdvice.portBase,GridApproximationAdvice.rowBase,
      Banks.layout,sizes.1,sizes.2,GridApproximationAdvice.portCount,Nat.cast_add,Nat.cast_mul] <;> ring

private theorem copy_args (b : Banks) (m : Memory w) (H : Mounted X W code b m)
    (fit : Fits (w:=w) X W b) :
    (fun i => ((args false) i).eval (data X W code b) m Fin.elim0) =
      GridOrderedRowRAM.operands (copyLayout W X.network (b.layout k)) (Fintype.card (Port p X.width))
        X.network.cells X.network.internal 0 (e*2) W.internal (code.encode 0) (code.encode 1) := by
  have cs := coordinates X W code b m H fit (Fin.elim0 : Fin 0 → Word w)
  have field := field_eval X W code b m H fit (Fin.elim0 : Fin 0 → Word w)
  funext i
  fin_cases i
  · exact cs.row
  · exact field 4
  · exact field 3
  · exact field 2
  all_goals rfl

private theorem edge_args (b : Banks) (m : Memory w) (H : Mounted X W code b m)
    (fit : Fits (w:=w) X W b) :
    (fun i => ((args true) i).eval (data X W code b) m Fin.elim0) =
      GridOrderedRowRAM.operands (edgeLayout W X.network (b.layout k)) 0 0 0 1 (e*2) W.internal
        (code.encode 0) (code.encode 1) := by
  have cs := coordinates X W code b m H fit (Fin.elim0 : Fin 0 → Word w)
  funext i
  fin_cases i
  · exact cs.eq
  all_goals rfl

private theorem dynamic_copy (b : Banks) (m : Memory w) (H : Mounted X W code b m)
    (fit : Fits (w:=w) X W b) (a : Word w) :
    (substitute (args false) (GridOrderedRowRAM.program w)).eval (data X W code b) m (fun _ => a) =
    (GridOrderedRowRAM.program w).eval
      (GridOrderedRowRAM.operands (copyLayout W X.network (b.layout k)) (Fintype.card (Port p X.width))
        X.network.cells X.network.internal 0 (e*2) W.internal (code.encode 0) (code.encode 1)) m
        (fun _ => a) :=
  (substitution (args false) (GridOrderedRowRAM.program w) (data X W code b) m (fun _ => a)).trans
    (congrArg (fun u : Fin 12 → Word w => (GridOrderedRowRAM.program w).eval u m (fun _ => a))
      (copy_args X W code b m H fit))

private theorem dynamic_edge (b : Banks) (m : Memory w) (H : Mounted X W code b m)
    (fit : Fits (w:=w) X W b) (a : Word w) :
    (substitute (args true) (GridOrderedRowRAM.program w)).eval (data X W code b) m (fun _ => a) =
    (GridOrderedRowRAM.program w).eval
      (GridOrderedRowRAM.operands (edgeLayout W X.network (b.layout k)) 0 0 0 1 (e*2) W.internal
        (code.encode 0) (code.encode 1)) m (fun _ => a) :=
  (substitution (args true) (GridOrderedRowRAM.program w) (data X W code b) m (fun _ => a)).trans
    (congrArg (fun u : Fin 12 → Word w => (GridOrderedRowRAM.program w).eval u m (fun _ => a))
      (edge_args X W code b m H fit))

private theorem naturalAddress (a : Word w) (start base : ℕ)
    (lo : start ≤ a.val) (endFit : base+(a.val-start) < 2^w) :
    ((base:Word w)+(a-(start:Word w))).val = base+(a.val-start) := by
  calc
    _ = ((base+(a.val-start) : ℕ) : Word w).val := by simp [Nat.cast_sub lo]
    _ = _ := Fin.val_cast_of_lt endFit

private theorem less (a : Word w) (n : ℕ) (hn : n < 2^w) :
    ((Comparison.lt).test a (n:Word w) = true) ↔ a.val < n := by
  simp [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt hn]

set_option maxHeartbeats 1000000 in
private theorem word_value (b : Banks) (m : Memory w) (H : Mounted X W code b m)
    (fit : Fits (w:=w) X W b) (pin : Fin (e*2)→Bool)
    (ext : ∀ i : Fin (e*2), m (b.exterior+i.val)=bitWord w (pin i)) (a : Word w) :
    (expression w).eval (data X W code b) m (fun _ => a) =
      (if a.val < footprint (imageNetwork X W) then target X W code pin a.val else 0) := by
  let N := imageNetwork X W
  have coords := coordinates X W code b m H fit (fun _ : Fin 1 => a)
  have sizeEq := W.network_sizes X.network
  have mulEq : rowStop W X.network=mulBase (e*2) N.internal N.cells := by
    simp [rowStop,edgeStart,rowStart,mulBase,N,sizeEq.1,Nat.mul_add,Nat.add_assoc]
  have stop := fit.image.trans_lt fit.stop
  change footprint N < 2^w at stop
  have rowStopBound : rowStop W X.network ≤footprint N := by rw [mulEq]; exact Nat.le_add_right _ _
  have edgeLe : edgeStart W X.network ≤ rowStop W X.network := Nat.le_add_right _ _
  have rowLe : rowStart W X.network ≤ edgeStart W X.network := Nat.le_add_right _ _
  have pinsLe : 2+e*2 ≤ rowStart W X.network := Nat.le_add_right _ _
  have stopWord := rowStopBound.trans_lt stop
  have edgeWord := edgeLe.trans_lt stopWord
  have rowWord := rowLe.trans_lt edgeWord
  have pinWord := pinsLe.trans_lt rowWord
  have two : 2 < 2^w := by have := fit.eleven; omega
  have first : Comparison.lt.test a (2 : Word w) = true ↔ a.val < 2 := by
    simp [Comparison.test,Fin.lt_def,Nat.mod_eq_of_lt two]
  have whole : Comparison.lt.test a ((footprint (imageNetwork X W) : ℕ) : Word w) = true ↔
      a.val < footprint N := less a _ stop
  change (expression w).eval (data X W code b) m (fun _ => a) =
    (if a.val < footprint N then target X W code pin a.val else 0)
  have mulEq' : (2:Word w)+(data X W code b) 5=((2+e*2 : ℕ):Word w) := by simp [data,publicWords]
  simp only [expression,Term.eval_select,Term.eval_literal,Term.eval_parameter,Term.eval_binary,
    Term.eval_load,Term.eval,BinaryOp.eval,coords.row,coords.eq,coords.mul,coords.stop,coords.table,
    mulEq',first,less a _ pinWord,less a _ rowWord,less a _ edgeWord,less a _ stopWord,whole]
  by_cases ac : a.val < 2
  · have good : a.val < footprint N := by omega
    rw [ite_eq_left ac,ite_eq_left good]
    rcases (show a.val = 0 ∨ a.val = 1 by omega) with h|h
    · have co := read_source N code pin (fun _=>false) (.constant false)
      change target X W code pin 0 = bitWord w false at co
      rw [h,co]; apply Fin.ext; simpa [bitWord,Fin.val_ofNat] using h
    · have co := read_source N code pin (fun _=>false) (.constant true)
      change target X W code pin 1 = bitWord w true at co
      rw [h,co]; apply Fin.ext
      simpa [bitWord,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 1 < 2^w)] using h
  rw [ite_eq_right ac]
  by_cases ap : a.val < 2+e*2
  · have good : a.val < footprint N := by omega
    rw [ite_eq_left ap,ite_eq_left good]
    let i : Fin (e*2) := ⟨a.val-2,by omega⟩
    have addr : 2+i.val=a.val := by dsimp [i]; omega
    change m (((b.exterior:Word w)+(a-(2:Word w))).val) = _
    have bound := fit.exterior
    have exteriorWord : ((b.exterior : Word w)+(a-2)).val = b.exterior+i.val := by
      simpa only [Nat.cast_two] using naturalAddress a 2 b.exterior (by omega) (by omega)
    rw [exteriorWord,ext]
    simpa only [target,sourceAddress,BitSource.read,addr] using
      (read_source N code pin (fun _=>false) (.pin i)).symm
  rw [ite_eq_right ap]
  by_cases ah : a.val < rowStart W X.network
  · have good : a.val < footprint N := by omega
    rw [ite_eq_left ah,ite_eq_left good]
    let i : Fin N.internal := ⟨a.val-(2+e*2),by change a.val < 2+e*2+N.internal at ah; omega⟩
    have addr : hiddenBase (e*2)+i.val=a.val := by dsimp [i,hiddenBase]; omega
    have fetched := read_source N code pin (fun _=>false) (.hidden i)
    change target X W code pin (hiddenBase (e*2)+i.val) = bitWord w false at fetched
    rw [addr] at fetched
    exact (show bitWord w false = 0 by apply Fin.ext; simp [bitWord]).symm.trans fetched.symm
  rw [ite_eq_right ah]
  by_cases ax : a.val < edgeStart W X.network
  · have good : a.val < footprint N := by omega
    rw [ite_eq_left ax,ite_eq_left good,dynamic_copy X W code b m H fit a]
    have gateFit : (b.layout k).gate+11*X.network.cells ≤ 2^w := by
      have bb := fit.compact
      dsimp [Banks.layout]
      unfold GridApproximationAdvice.wordCount GridApproximationAdvice.multBase
        GridApproximationAdvice.portBase GridApproximationAdvice.rowBase at bb
      omega
    exact copy_word_at W X.network code _ m H.records pin a (by omega) ax
      gateFit fit.ports fit.source fit.cells fit.eleven
  rw [ite_eq_right ax]
  by_cases ae : a.val < rowStop W X.network
  · have good : a.val < footprint N := by omega
    rw [ite_eq_left ae,ite_eq_left good,dynamic_edge X W code b m H fit a]
    exact edge_word_at W X.network code _ m H.records pin a (by omega) ae fit.edges fit.eleven
  rw [ite_eq_right ae]
  by_cases am : a.val < footprint N
  · simp only [ite_eq_left am]
    let q := Fintype.card F
    let z := a.val-rowStop W X.network
    have grow : z < q*q := by
      change a.val < mulBase (e*2) N.internal N.cells+q*q at am
      rw [←mulEq] at am
      dsimp [z]; omega
    have pos : 0 < q := Fintype.card_pos
    let i : Fin q := ⟨z/q,(Nat.div_lt_iff_lt_mul pos).mpr grow⟩
    let j : Fin q := ⟨z%q,Nat.mod_lt _ pos⟩
    let x := (Fintype.equivFin F).symm i
    let y := (Fintype.equivFin F).symm j
    have index : q*i.val+j.val=z := Nat.div_add_mod _ _
    have adr : mulBase (e*2) N.internal N.cells+q*i.val+j.val=a.val := by rw [←mulEq]; dsimp [z] at index; omega
    have room := fit.compact
    change b.compact+(GridApproximationAdvice.multBase X+q*q) < 2^w at room
    rw [naturalAddress a _ _ (by omega) (by dsimp [z] at grow; omega)]
    have prod := H.product x y
    have prod' := read_product N code pin (fun _=>false) x y
    simp only [x,y,Equiv.apply_symm_apply] at prod prod'
    rw [←Nat.add_assoc] at prod
    change m (b.compact+GridApproximationAdvice.multBase X+(q*i.val+j.val))=_ at prod
    rw [index] at prod
    unfold q at adr
    rw [adr] at prod'
    exact prod.trans prod'.symm
  · simp only [ite_eq_right am]

set_option maxHeartbeats 1000000 in
private theorem expr_bounds (w : ℕ) : (expression w).binds ≤ 22000 := by
  have a (b : Bool) (i : Fin 12) : ((args b i : E w 0)).binds ≤ 70 := by
    cases b <;> fin_cases i <;> simp [args,rowAt,eqAt,copies,fld,privateCount,Term.literal,
      Term.parameter,Term.load,Term.binary,Term.binds]
  have yes := substitute_binds (args true) (GridOrderedRowRAM.program w) (by decide : 1 ≤ 70) (a true)
  have no := substitute_binds (args false) (GridOrderedRowRAM.program w) (by decide : 1 ≤ 70) (a false)
  rw [GridOrderedRowRAM.program_size] at yes no
  simp only [expression,Term.select,Term.binary,Term.load,Term.binds_letThen,Term.binds_rename,
    Term.binds,Term.parameter,Term.literal,rowAt,eqAt,copies,fld,privateCount,tableAt,mulAt,stopAt]
  omega

theorem text_bound (b : Banks) (k p L h g q : ℕ) (z one : Word w) :
    let M := build b k p L h g q z one
    M.labels+M.registers+M.slots ≤ 90000 := by
  change (10+(6+(expression w).labels))+(5+(4+(expression w).binds))+(3+12) ≤ 90000
  rw [Term.labels_eq]
  have := expr_bounds w
  omega


/-- From the literal old bit prefix and the high banks, execute the physical
right-shift staging and the full padded sweep. All lookup rows and the field
table are those of the selected actual network. -/
theorem build_spec (b : Banks) (fit : Fits (w:=w) X W b) (pin : Fin (e*2)→Bool) :
    (build b k (e*2) L W.internal W.equal.length (Fintype.card F)
      (code.encode 0) (code.encode 1)).Spec
      (fun m => Mounted X W code b m ∧ ∀ i : Fin (e*2),m i.val=bitWord w (pin i))
      (fun m o => (∀ a < footprint (imageNetwork X W),o a=target X W code pin a) ∧
        ∀ a, b.limit ≤ a → (a < b.exterior ∨ b.exterior+e*2 ≤ a) → o a=m a)
      (10+5*(e*2)+44004*b.limit) := by
  let prep := PhysicalInputPhases.copying w 0 (e*2) b.exterior
  let scan := PhysicalInputPhases.writing (expression w) (data X W code b) 0 b.limit
  let ready (m : Memory w) := Mounted X W code b m ∧
    ∀ i : Fin (e*2),m (b.exterior+i.val)=bitWord w (pin i)
  let value (a : ℕ) := if a < footprint (imageNetwork X W) then target X W code pin a else 0
  have leafRoom : e*2 ≤ b.limit := by
    have := fit.image
    change 2+e*2+_+_+_ ≤ b.limit at this
    omega
  have copySpec : prep.Spec (fun _ => True)
      (fun m o => o=PhysicalInputCopy.copied 0 (e*2) b.exterior m) (6+5*(e*2)) :=
    PhysicalInputPhases.copying_spec (w:=w) 0 (e*2) b.exterior
      (by have := fit.stop; omega) fit.exterior (Or.inr (by have := fit.high; omega))
  let pre (m : Memory w) := Mounted X W code b m ∧ ∀ i : Fin (e*2),m i.val=bitWord w (pin i)
  have prepSpec : prep.Spec pre
      (fun m o => o=PhysicalInputCopy.copied 0 (e*2) b.exterior m ∧ ready o) (6+5*(e*2)) := by
    intro P R K M pc reg pub exit inst words c m start hm
    obtain ⟨t,ht,out,m',run,done,post⟩ := copySpec M pc reg pub exit inst words c m start trivial
    subst m'
    refine ⟨t,ht,out,_,run,done,rfl,?_,?_⟩
    · apply Mounted.agree X W code hm.1 (b.exterior+e*2)
        ⟨fit.afterCompact,fit.afterPin,fit.afterEdge⟩
      exact fun a ha => PhysicalInputCopy.copied_outside 0 _ _ m a (.inr ha)
    · intro i
      simpa only [PhysicalInputCopy.copied_at _ _ _ _ _ i.isLt,Nat.zero_add] using hm.2 i
  have scanned : scan.Spec ready (fun m o => o=fillSegment 0 b.limit value m)
      (4+b.limit*(2*(expression w).binds+4)) := by
    apply PhysicalInputPhases.writing_spec _ _ _ _ (by simpa using fit.stop) _ _
    intro m₀ h₀ a m _ _ frame
    have high (i : ℕ) (hi : b.limit ≤ i) : m i=m₀ i := frame i (.inr (by omega))
    have mh := Mounted.agree X W code h₀.1 b.limit
      ⟨by have := fit.afterCompact; have := fit.high; omega,
       by have := fit.afterPin; have := fit.high; omega,
       by have := fit.afterEdge; have := fit.high; omega⟩ high
    apply word_value X W code b m mh fit pin _ a
    exact fun i => (high _ (by have := fit.high; omega)).trans (h₀.2 i)
  have together : (prep.seq scan).Spec pre (fun m o => ∃ tmp,
      (tmp=PhysicalInputCopy.copied 0 (e*2) b.exterior m ∧ ready tmp) ∧
        o=fillSegment 0 b.limit value tmp) ((6+5*(e*2))+(4+b.limit*(2*(expression w).binds+4))) :=
    Procedure.Spec.seq (A:=prep) (B:=scan) prepSpec scanned (fun _ _ h => h.2)
  intro P R K machine pc reg pub exit install rom c m start hm
  obtain ⟨t, ht, out, final, run, done, tmp, ⟨copied, _⟩, hfinal⟩ :=
    together machine pc reg pub exit install rom c m start hm
  refine ⟨t, ?_, out, final, run, done, ?_⟩
  · have h := Nat.mul_le_mul_left b.limit (show 2*(expression w).binds+4 ≤ 44004 by
        have := expr_bounds w; omega)
    rw [Nat.mul_comm b.limit 44004] at h
    omega
  · subst final
    subst tmp
    constructor
    · intro a ha
      have small := lt_of_lt_of_le ha fit.image
      simp [fillSegment, value, ha, small]
    · intro a ha outside
      simpa [fillSegment, Nat.not_lt.mpr ha] using
        PhysicalInputCopy.copied_outside 0 (e*2) b.exterior m a outside

/-- The prefix read by the physical staging pass is precisely the paired
part of the same description/controller input, before its first two addresses
are reused for the contraction constants. -/
theorem build_input {q : ℕ} (b : Banks) (fit : Fits (w:=w) X W b)
    (pin : Fin (e*2)→Bool) (description : Fin q→Bool) (fixed : ℕ→Bool) :
    (build b k (e*2) L W.internal W.equal.length (Fintype.card F)
      (code.encode 0) (code.encode 1)).Spec
      (fun m => Mounted X W code b m ∧ ∀ i : Fin (e*2), m i.val =
        bitWord w (GridDescription.input pin description fixed i.val))
      (fun m o => (∀ a < footprint (imageNetwork X W),o a=target X W code pin a) ∧
        ∀ a,b.limit ≤ a → (a < b.exterior ∨ b.exterior+e*2 ≤ a) → o a=m a)
      (10+5*(e*2)+44004*b.limit) := by
  intro P R K machine pc reg pub exit install rom c m start hm
  apply build_spec X W code b fit pin machine pc reg pub exit install rom c m start
  exact ⟨hm.1, fun i => (hm.2 i).trans (congrArg (bitWord w)
    (GridDescription.pair_at pin description fixed i))⟩

/-- All selectors and all networks of size at most B share this linear sweep
length. The much larger sector stride is only an address separation. -/
def limit (e L B shared equality fieldSize : ℕ) :=
  2+e*2+shared+11*(L*B)+11*equality+fieldSize*fieldSize

def sectors (age low : ℕ) : Banks :=
  let J := GridDescription.sector age
  ⟨2*J,3*J,4*J,J,low⟩

theorem sector_fits {age B : ℕ} (large : 0 < age) (copiesPositive : 0 < L)
    (size : X.size ≤ B) (fixedPart : 6+k+Fintype.card F*Fintype.card F ≤ B)
    (small : limit e L B W.internal W.equal.length (Fintype.card F) ≤ 2^(4*age)) :
    Fits (w:=64*age) X W (sectors age (limit e L B W.internal W.equal.length (Fintype.card F))) := by
  let J := GridDescription.sector age
  let top := limit e L B W.internal W.equal.length (Fintype.card F)
  have room : 64*J < 2^(64*age) := GridDescription.sectors_fit large
  have low : top < J := lt_of_le_of_lt small (GridDescription.small_before_sector large)
  have lb : B ≤ L*B := Nat.le_mul_of_pos_left _ copiesPositive
  have bc : B ≤ top := by dsimp [top,limit]; omega
  have qLe : Fintype.card (Port p X.width) ≤ B := by unfold Approximation.size at size; omega
  have pSize : X.network.internal+X.network.cells ≤ B := by unfold Approximation.size at size; omega
  have repl := Nat.mul_le_mul_left L pSize
  rw [Nat.mul_add] at repl
  have portsRoom : Fintype.card (Port p X.width)*L ≤ L*B := by
    simpa only [Nat.mul_comm (Fintype.card (Port p X.width)) L] using Nat.mul_le_mul_left L qLe
  have compact := GridApproximationAdvice.wordCount_cap X size fixedPart
  have src : 2+Fintype.card (Port p X.width)+X.network.internal ≤ 2+B := by
    unfold Approximation.size at size; omega
  have sizes := W.network_sizes X.network
  change Fits (w:=64*age) X W ⟨2*J,3*J,4*J,J,top⟩
  constructor <;> try dsimp only
  · omega
  · change 2+e*2+(W.network X.network).internal+11*(W.network X.network).cells+
      Fintype.card F*Fintype.card F ≤ top
    rw [sizes.1,sizes.2,Nat.mul_add]
    dsimp [top,limit]
    omega
  · exact low.le
  · dsimp [top,limit] at low; omega
  · dsimp [top,limit] at low; omega
  · dsimp [top,limit] at low; omega
  · dsimp [top,limit] at low; omega
  · omega
  · dsimp [top,limit] at low; omega
  · dsimp [top,limit] at low; omega
  · omega
  · omega
  · dsimp [top,limit] at low; omega

/-- Unpack the actual raw fixed-length public tape into sector two before
producing any selector-dependent source pointers. Its end stays below sector
three, where the port rows will be published. -/
theorem load_sector {age B src : ℕ} (enc : FieldCode F (64*age)) (large : 768 ≤ age)
    (positive : 0 < B) (inputRoom : src+B*age^2 ≤ 2^(4*age)) :
    let J := GridDescription.sector age
    2*J+12*B ≤ 3*J ∧
    (GridApproximationAdvice.loader age B src (2*J)).Spec
      (fun m => ∀ i,m (src+i.val) =
        ((GridApproximationAdvice.paddedTape X age B enc i).toNat : Word (64*age)))
      (fun m o => o=GridApproximationAdvice.paddedMemory X enc B (2*J) m) (4000*(age*B)) := by
  intro J
  have high : 2^(4*age) < J := GridDescription.small_before_sector (by omega)
  have fit : 64*J < 2^(64*age) := GridDescription.sectors_fit (by omega)
  have clock := (GridApproximationAdvice.padded_clock age B large positive).1
  have count : 12*B ≤ (64*age)*(12*B) := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨by omega,GridApproximationAdvice.loader_spec X enc large positive (.inr (by omega))
    (by omega) (by omega)⟩

omit [Field F] in
theorem linear_limit {n B : ℕ} (rails : e*(n+1) ≤ 2*k*((n+1)^k*B)) :
    limit e ((n+1)^k) B (GridThrough.Ordered.hiddenCount e n)
      (GridThrough.Ordered.edgeCount e n) (Fintype.card F) ≤
      (250*k+40)*((n+1)^k*B)+(Fintype.card F)^2+11 := by
  have es : e ≤ e*(n+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos n)
  unfold limit GridThrough.Ordered.hiddenCount GridThrough.Ordered.edgeCount
  nlinarith only [es,rails,Nat.zero_le ((n+1)^k*B)]


end
end Hierarchy.GridPaddedCellImage

end OAI
