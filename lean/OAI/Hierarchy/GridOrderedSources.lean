import OAI.Hierarchy.GridOrderedEdgeRAM
import OAI.Hierarchy.GridOrderedPinsRAM
import OAI.Hierarchy.GridPaddedCellImage
import OAI.Hierarchy.GridPassageSelected
import OAI.Hierarchy.GridOrderedPinOrigins
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Linking the two concrete source emitters to the padded native evaluator -/

namespace Hierarchy.GridOrderedSources
open GridThrough GridThrough.Ordered UniversalGrid ThreeFlat
open Computability.VPVNP.BurstRAM RAM RAM.BitLayout RAM.PhysicalProcedure
open scoped Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {k n p r w : ℕ}
variable (X : Catalyst.Approximation F k p) (P : GridThrough.Program (Fin r) n p X.width)
variable (code : FieldCode F w)

structure Arena where
  J : ℕ

def Arena.pins (A : Arena) : GridOrderedPinsRAM.Banks :=
  ⟨2*A.J,11*A.J,7*A.J,5*A.J+2*(A.J/8),3*A.J⟩
def Arena.edges (A : Arena) : GridOrderedEdgeRAM.Banks :=
  ⟨4*A.J,5*A.J+3*(A.J/8),8*A.J⟩
def Arena.railMap (A : Arena) : GridPassageRAMRow.AddressMap :=
  ⟨5*A.J,5*A.J+A.J/8,5*A.J+2*(A.J/8),5*A.J+3*(A.J/8),
    ⟨6*A.J,7*A.J,8*A.J⟩,5*A.J+4*(A.J/8)⟩
def Arena.data (A : Arena) (r n : ℕ) : GridOrderedDataRAM.Banks :=
  ⟨10*A.J,9*A.J,11*A.J,GridOrderedPinOrigins.centerBase r n⟩
def Arena.finalBanks (A : Arena) (limit : ℕ) : GridPaddedCellImage.Banks :=
  {compact:=2*A.J,pin:=3*A.J,edge:=4*A.J,exterior:=A.J,limit:=limit}

def prepare (A : Arena) (k n p r B w : ℕ) : Procedure w :=
  (GridOrderedPinsRAM.build A.pins B k p r n w).seq (GridOrderedEdgeRAM.build A.edges r n w)

private noncomputable def portImage (A : Arena) (B : ℕ) (m : Memory w) :=
  fillSegment A.pins.output (((n+1)^k)*B) (GridOrderedPinsRAM.imageWord X P A.pins) m
noncomputable def prepared (A : Arena) (B : ℕ) (m : Memory w) :=
  fillSegment A.edges.output (GridOrderedEdgeRAM.totalWords r n) (GridOrderedEdgeRAM.word P A.edges)
    (portImage X P A B m)

/-- Each region is charged by its real extent, irrespective of the spacing J
between banks. A single page-size hypothesis bounds all scratch intervals. -/
structure Fits (A : Arena) (B : ℕ) : Prop where
  words : GridApproximationAdvice.wordCount X ≤ A.J
  pin : (n+1)^k*B ≤ A.J
  edge : GridOrderedEdgeRAM.totalWords r n ≤ A.J
  rails : r*(n+1) ≤ A.J
  high : 12*A.J < 2^w
  pinsFit : GridOrderedPinsRAM.Fits (n:=n) (w:=w) X A.pins B
  two : 2 < 2^w

omit [Field F] in
/-- One public page bound discharges the word and table address obligations.
The reserve rectangle includes the padded direction-specific ranks. -/
theorem fits_of_pages (A : Arena) (B : ℕ)
    (advice : GridApproximationAdvice.wordCount X ≤ A.J)
    (ports : GridApproximationAdvice.portCount X ≤ B) (width : ∀ j,X.width j ≤ B)
    (L : (n+1)^k ≤ A.J) (g : n+1 ≤ A.J) (K : k ≤ A.J/8)
    (cap : B ≤ A.J) (localPins : (n+1)^k*p ≤ A.J) (entries : (n+1)^k*B ≤ A.J)
    (reservation : ((n+1)^k*k)*B ≤ A.J)
    (edges : GridOrderedEdgeRAM.totalWords r n ≤ A.J) (rails : r*(n+1) ≤ A.J)
    (nontrivial : 2 ≤ A.J) (headroom : 12*A.J < 2^w) : Fits (n:=n) (r:=r) (w:=w) X A B := by
  have compact : GridApproximationAdvice.multBase X ≤ GridApproximationAdvice.wordCount X := Nat.le_add_right _ _
  refine ⟨advice,entries,edges,rails,headroom,?_,by omega⟩
  constructor
  · omega
  · omega
  · exact width
  · exact ports
  · dsimp [Arena.pins]; omega
  · dsimp [Arena.pins]; omega
  · dsimp [Arena.pins]; omega
  · dsimp [Arena.pins]; omega
  · dsimp [Arena.pins]; omega
  · omega

structure Mounted (A : Arena) (B : ℕ) (m original : Memory w) : Prop where
  pins : GridOrderedPinsRAM.Mounted X P A.pins B m
  edges : GridOrderedEdgeRAM.Mounted P A.edges m
  gates : ∀ i < GridApproximationAdvice.wordCount X,m (A.pins.compact+i) =
      GridApproximationAdvice.paddedMemory X code B A.pins.compact original (A.pins.compact+i)

/-- Before selection, endpoint scatter has already produced the data map
in the high bank. The bounded native selection sweep preserves its words. -/
structure Input (A : Arena) (B : ℕ) (m original : Memory w) : Prop where
  controller : ∀ e : Fin r, GridPassageRAMRow.DecodeReads m A.railMap.dir A.railMap.cell
    A.railMap.powers A.railMap.touch e.val (P.direction e) (P.row e) (P.touch e)
  powers : ∀ j : Fin k, m (A.railMap.powers+j.val)=((n+1)^j.val:Word w)
  localData : ∀ c : Cell k n, ∀ i : Fin p,m (A.pins.data+((finFunctionFinEquiv c).val*p+i.val)) =
    (sourceAddress (Wiring.source (sourcePin P P.data c (.inl i))):Word w)
  compact : ∀ i < GridApproximationAdvice.wordCount X, m (A.pins.compact+i) =
    GridApproximationAdvice.paddedMemory X code B A.pins.compact original (A.pins.compact+i)

section Scheduled

variable {q d : ℕ} (Y : Catalyst.Approximation F k (q*d)) (A : Arena)
    (assignment : PinAssignment (Fin r) k n q d)

/-- The only setting-dependent descriptor input is the genuine address of
each allocated rail side and the literal at each flattened cell/data slot.
The source-address addend is independent of the wiring. -/
theorem scatter_input (B : ℕ) (code : FieldCode F w) (m original : Memory w)
    (count : Fin k → GridTicks.Tick k (n+1) q → ℕ)
    (conserve : ∀ j t,(GridTicks.pairFiber assignment.direction (fun e=>GridTicks.index (assignment.tick e)) j t).card=count j t)
    (enough : ∀ x j,Y.width j ≤ ((GridTicks.pairsOn (count j) (GridTicks.lineTicks j x)) \
      (GridTicks.pairsOn (count j) (GridTicks.cellTicks x))).card)
    (fit : Fits (r:=r) (n:=n) (w:=w) Y A B)
    (dataRoom : (n+1)^k*(q*d) ≤ A.J) (axisRoom : k ≤ A.J)
    (destRoom : r*2 ≤ A.J) (spare : 11*A.J+(n+1)^k*(q*d) < 2^w)
    (input : ∀ e:Fin r, GridPassageRAMRow.DecodeReads m A.railMap.dir A.railMap.cell
      A.railMap.powers A.railMap.touch e.val (assignment.direction e) (assignment.row e) (assignment.touch e))
    (powers : ∀ j : Fin k, m (A.railMap.powers+j.val)=((n+1)^j.val:Word w))
    (addr : ∀ i < r*2,m ((A.data r n).dest+i)=(GridOrderedPinOrigins.slot assignment i:Word w))
    (literal : ∀ ci : Cell k n × Fin (q*d),
      m ((A.data r n).literal+(dataCode ci).val)=((assignment.literal ci).toNat:Word w))
    (packed : ∀ i < GridApproximationAdvice.wordCount Y,m (A.pins.compact+i)=
      GridApproximationAdvice.paddedMemory Y code B A.pins.compact original (A.pins.compact+i)) :
    let S := A.data r n
    let P := GridThrough.Program.ofScheduled assignment Y.width count conserve enough
    let out := GridOrderedDataRAM.prepared S ((n+1)^k*(q*d)) (r*2) (GridOrderedPinOrigins.slot assignment) m
    (GridOrderedDataRAM.prepare w S ((n+1)^k*(q*d)) (r*2)).Exec m out (9+5*((n+1)^k*(q*d))+11*(r*2)) ∧
      Input Y P code A B out original := by
  dsimp only
  let S := A.data r n
  let P := GridThrough.Program.ofScheduled assignment Y.width count conserve enough
  let out := GridOrderedDataRAM.prepared S ((n+1)^k*(q*d)) (r*2) (GridOrderedPinOrigins.slot assignment) m
  have H := fit.high
  have W := fit.words
  have R := fit.rails
  have K := fit.pinsFit.stride
  have E : r ≤ r*(n+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have fr (i : ℕ) (lo : i < 11*A.J) : out i=m i :=
    GridOrderedDataRAM.prepared_frame S _ _ _ m i (fun j hj=>by
      simp [GridOrderedPinOrigins.slot,hj]) (.inl lo)
  constructor
  · exact Procedure.Spec.exec (GridOrderedPinOrigins.scatter_cost assignment S (by omega)
      (by dsimp [S,Arena.data]; omega) spare (by dsimp [S,Arena.data]; omega)
      (Or.inr (by dsimp [S,Arena.data]; omega)) (Or.inr (by dsimp [S,Arena.data]; omega))) m addr
  refine ⟨?_,?_,?_,?_⟩
  · intro e
    have v := e.isLt
    have dir := (assignment.direction e).isLt
    rcases input e with ⟨hd,hr,hp,ht⟩
    constructor
    · exact (fr _ (by dsimp [Arena.railMap]; omega)).trans hd
    · exact (fr _ (by dsimp [Arena.railMap]; omega)).trans hr
    · exact (fr _ (by dsimp [Arena.railMap,Arena.pins] at *; omega)).trans hp
    · exact (fr _ (by dsimp [Arena.railMap]; omega)).trans ht
  · intro j
    exact (fr _ (by have jv := j.isLt; dsimp [Arena.pins,Arena.railMap] at *; omega)).trans (powers j)
  · intro c i
    have origin := GridOrderedPinOrigins.prepared_at assignment S m c i rfl literal
    have id := GridOrderedPinOrigins.scheduled_value assignment Y.width count conserve enough c i
    rw [id] at origin
    simpa [P,S,out,Arena.data,Arena.pins,dataCode,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using origin
  · intro i hi
    exact (fr _ (by dsimp [Arena.pins]; omega)).trans (packed i hi)

end Scheduled

/-- Compose the real variable-width first-rank opcode loop with its port and
mark memory invariants. -/
theorem select (A : Arena) (B : ℕ) (m original : Memory w) (fit : Fits (n:=n) (r:=r) (w:=w) X A B)
    (ac : A.railMap.Fits w k n r B)
    (cap : ∀ c j,X.width j ≤ (GridLens.untouchedRails P.direction P.row P.touch c j).card)
    (pass : P.pass=GridLens.firstPassage P.direction P.row P.touch X.width cap)
    (size : GridApproximationAdvice.wordCount X ≤ 12*B) (input : Input X P code A B m original) :
    let a := A.railMap
    let final := GridPassageRAMMask.finalMemory P.direction P.row P.touch X.width a B m
    (GridPassageRAMMask.program a w A.pins.compact k n r B).Exec m final
      (4+((n+1)^k*k)*6+(3+r*(n+1)*55)+(3+((n+1)^k*k*B)*39)) ∧
      Mounted X P code A B final original := by
  dsimp only
  let a := A.railMap
  let final := GridPassageRAMMask.finalMemory P.direction P.row P.touch X.width a B m
  let D := input.controller
  have C := a.final_correct P.direction P.row P.touch B ac m D
  have rf := fit.rails
  have sf := fit.words
  have jf : 6+k ≤ GridApproximationAdvice.wordCount X := by
    unfold GridApproximationAdvice.wordCount GridApproximationAdvice.multBase GridApproximationAdvice.portBase
      GridApproximationAdvice.rowBase
    omega
  have wm : ∀ j : Fin k,m (A.pins.compact+6+j.val)=(X.width j:Word w) := by
    intro j
    have hi : 6+j.val < GridApproximationAdvice.wordCount X := by have := j.isLt; omega
    rw [Nat.add_assoc,input.compact _ hi,GridApproximationAdvice.paddedMemory_eq X code B _ original _ hi size]
    exact GridApproximationAdvice.packed_width X code _ original j
  have low (addr : ℕ) (h : addr < 6*A.J) : final addr=m addr :=
    (GridPassageRAMMask.final_frame P.direction P.row P.touch X.width a B m addr (.inl
      (by change addr < 8*A.J; omega))).trans (C.input addr h)
  have high (addr : ℕ) (h : 8*A.J+r*(n+1) ≤ addr) : final addr=m addr :=
    (GridPassageRAMMask.final_frame P.direction P.row P.touch X.width a B m addr (.inr h)).trans (C.above addr h)
  have compact (i : ℕ) (hi : i < GridApproximationAdvice.wordCount X) :=
    (low (A.pins.compact+i) (by dsimp [Arena.pins]; omega)).trans (input.compact i hi)
  constructor
  · exact GridPassageRAMMask.exec a _ B P.direction P.row P.touch X.width ac
      (by dsimp [a,Arena.railMap,Arena.pins]; omega) fit.pinsFit.widths m D wm
      (fun j => by simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using input.powers j)
  refine ⟨GridOrderedPinsRAM.mounted_of_packed X P A.pins B code final original size compact ?_ ?_ ?_,
    ⟨?_,?_⟩,compact⟩
  · intro c i
    exact (high _ (by dsimp [Arena.pins]; omega)).trans (input.localData c i)
  · intro c z
    rw [pass]
    simpa [final,a,Arena.railMap,Arena.pins,Nat.add_assoc] using GridPassageRAMMask.final_chosen
      P.direction P.row P.touch X.width a B ac m D fit.pinsFit.widths cap c z.1 z.2
  · intro j
    exact (low _ (by have lim := ac.powers; have := j.isLt; dsimp [a,Arena.railMap,Arena.pins] at *; omega)).trans (input.powers j)
  · intro e
    exact (low _ (by have lim := ac.touch; have := e.isLt; dsimp [a,Arena.railMap,Arena.edges] at *; omega)).trans ((D e).touch)
  · intro e t
    have actual := P.corrected_mark_eq_selected cap pass a ac m D fit.pinsFit.widths e t
    by_cases sel : P.Selected e t
    · rw [ite_eq_left ((marked P e t).2 sel)]
      simpa [final,a,Arena.edges,Arena.railMap,GridPassageRAMRow.cursor,Nat.add_assoc,sel] using actual
    · rw [ite_eq_right (mt (marked P e t).1 sel)]
      simpa [final,a,Arena.edges,Arena.railMap,GridPassageRAMRow.cursor,Nat.add_assoc,sel] using actual

theorem execute (A : Arena) (B : ℕ) (m original : Memory w) (fit : Fits (n:=n) (r:=r) (w:=w) X A B)
    (mounted : Mounted X P code A B m original) :
    (prepare A k n p r B w).Exec m (prepared X P A B m)
      (20+1204*(((n+1)^k)*B)+356*GridOrderedEdgeRAM.totalWords r n) := by
  have pf := fit.pin
  have ef := fit.edge
  have rf := fit.rails
  have wf := fit.words
  have all := fit.high
  have er : r ≤ r*(n+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have dis : GridOrderedPinsRAM.Separate X A.pins ((n+1)^k) B := by
    have part : GridApproximationAdvice.multBase X ≤ GridApproximationAdvice.wordCount X := Nat.le_add_right _ _
    constructor <;> dsimp [Arena.pins] <;> omega
  have a : Procedure.Exec _ _ _ _ := Procedure.Spec.exec (GridOrderedPinsRAM.build_spec X P A.pins B fit.pinsFit dis) m mounted.pins
  have frame (i : ℕ) (hi : 4*A.J ≤ i) : portImage X P A B m i=m i := by
    dsimp [portImage,fillSegment,Arena.pins]
    exact ite_eq_right (by omega)
  have edge : GridOrderedEdgeRAM.Mounted P A.edges (portImage X P A B m) := by
    constructor
    · intro i; exact (frame _ (by dsimp [Arena.edges]; omega)).trans (mounted.edges.longitudinal i)
    · intro i j; exact (frame _ (by dsimp [Arena.edges]; omega)).trans (mounted.edges.selected i j)
  have b : Procedure.Exec _ _ _ _ := GridOrderedEdgeRAM.build_exec P A.edges _ edge
    (by dsimp [Arena.edges]; omega) (by dsimp [Arena.edges]; omega)
    (by dsimp [Arena.edges]; omega) (by dsimp [Arena.edges]; omega) fit.pinsFit.grid fit.two
  have actual : Procedure.Exec _ _ _ _ := Procedure.Exec.then a b
  intro pcs regs pubs M pc reg pub exit installed values cfg input start given
  obtain ⟨t,ht,out,image,run,done,correct⟩ := actual M pc reg pub exit installed values cfg input start given
  refine ⟨t,ht.trans ?_,out,image,run,done,correct⟩
  have cost := GridOrderedPinsRAM.time_per_port (w:=w) ((n+1)^k) (n+1)
  have bound := Nat.mul_le_mul_left (((n+1)^k)*B) (show
    2*(GridOrderedPinsRAM.program (w:=w) ((n+1)^k) (n+1)).binds+4 ≤ 1204 by omega)
  nlinarith only [bound]

theorem final_mounted (A : Arena) (B limit : ℕ) (m original : Memory w)
    (fit : Fits (n:=n) (r:=r) (w:=w) X A B) (cap : GridApproximationAdvice.wordCount X ≤ 12*B)
    (mounted : Mounted X P code A B m original) :
    GridPaddedCellImage.Mounted X (wiring P) code (A.finalBanks limit) (prepared X P A B m) := by
  have pf := fit.pin
  have wf := fit.words
  have outside (b count a : ℕ) (word input : Memory w) (h : ¬ (b ≤ a ∧ a < b+count)) :
      fillSegment b count word input a=input a := ite_eq_right h
  have inside (b count a : ℕ) (word input : Memory w) (h : b ≤ a ∧ a < b+count) :
      fillSegment b count word input a=word a := ite_eq_left h
  have pastEdge (a : ℕ) (h : ¬ (A.edges.output ≤ a ∧ a < A.edges.output+GridOrderedEdgeRAM.totalWords r n)) :
      prepared X P A B m a=portImage X P A B m a :=
    outside A.edges.output (GridOrderedEdgeRAM.totalWords r n) a (GridOrderedEdgeRAM.word P A.edges)
      (portImage X P A B m) h
  apply GridPaddedCellImage.mounted_banks X (wiring P) code _ B _ original cap
  · intro i hi
    have pinOutside : ¬ (3*A.J≤2*A.J+i ∧ 2*A.J+i<3*A.J+((n+1)^k)*B) :=by omega
    have edgeOutside : ¬ (4*A.J≤2*A.J+i ∧ 2*A.J+i<4*A.J+GridOrderedEdgeRAM.totalWords r n) :=by omega
    have old : portImage X P A B m (2*A.J+i)=m (2*A.J+i) :=
      outside A.pins.output (((n+1)^k)*B) (2*A.J+i) (GridOrderedPinsRAM.imageWord X P A.pins) m pinOutside
    exact (pastEdge _ edgeOutside).trans (old.trans (mounted.gates i hi))
  · intro c i
    let q:=GridApproximationAdvice.portCount X
    have bound : c.val*q+i.val<((n+1)^k)*B :=calc
      c.val*q+i.val<c.val*q+q := Nat.add_lt_add_left i.isLt _
      _=(c.val+1)*q := (Nat.succ_mul _ _).symm
      _≤((n+1)^k)*B := Nat.mul_le_mul c.isLt fit.pinsFit.ports
    have edgeOutside : ¬ (4*A.J≤3*A.J+c.val*q+i.val ∧
      3*A.J+c.val*q+i.val<4*A.J+GridOrderedEdgeRAM.totalWords r n) :=by omega
    have pinInside : 3*A.J≤3*A.J+c.val*q+i.val ∧ 3*A.J+c.val*q+i.val<3*A.J+((n+1)^k)*B :=by omega
    change prepared X P A B m (3*A.J+q*c.val+i.val)=_
    rw [Nat.mul_comm q c.val]
    have placed : portImage X P A B m (3*A.J+c.val*q+i.val)=
        GridOrderedPinsRAM.imageWord X P A.pins (3*A.J+c.val*q+i.val) :=
      inside A.pins.output (((n+1)^k)*B) (3*A.J+c.val*q+i.val)
        (GridOrderedPinsRAM.imageWord X P A.pins) m pinInside
    exact (pastEdge _ edgeOutside).trans (placed.trans (GridOrderedPinsRAM.imageWord_at X P A.pins c i))
  · intro i
    have observed:=GridOrderedEdgeRAM.emitted_at P A.edges (portImage X P A B m) i (0 : Fin 2)
    change _=(sourceAddress (Wiring.source (((wiring P).equal.get i).1)):Word w) at observed
    rw [show (↑(0 : Fin 2) : ℕ)=0 by decide] at observed
    exact observed
  · intro i
    have observed:=GridOrderedEdgeRAM.emitted_at P A.edges (portImage X P A B m) i (1 : Fin 2)
    change _=(sourceAddress (Wiring.source (((wiring P).equal.get i).2)):Word w) at observed
    rw [show (↑(1 : Fin 2) : ℕ)=1 by decide] at observed
    exact observed

/-- A single common native procedure after authentic rail and literal decoding.
The grid geometry and field codes determine its instruction table for all settings. -/
def writing (A : Arena) (k n p r B limit fieldSize : ℕ) (z one : Word w) : Procedure w :=
  ((GridPassageRAMMask.program A.railMap w A.pins.compact k n r B).seq (prepare A k n p r B w)).seq
    (GridPaddedCellImage.build (A.finalBanks limit) k (r*2) ((n+1)^k)
      (hiddenCount r n) (edgeCount r n) fieldSize z one)

def clock (k n r B limit : ℕ) :=
  (4+((n+1)^k*k)*6+(3+r*(n+1)*55)+(3+((n+1)^k*k*B)*39)) +
  (20+1204*(((n+1)^k)*B)+356*GridOrderedEdgeRAM.totalWords r n) +
  (10+5*(r*2)+44004*limit)

/-- Registers, ROM labels and public operand slots are shared by all legal
settings, including the all-literal identity setting. -/
theorem hardware (A : Arena) (k n p r B limit fieldSize : ℕ) (z one : Word w) :
    let M := writing A k n p r B limit fieldSize z one
    M.labels+M.registers+M.slots ≤ 100000 := by
  let pre := GridPassageRAMMask.program A.railMap w A.pins.compact k n r B
  let port := GridOrderedPinsRAM.build A.pins B k p r n w
  let eq (part : GridOrderedEdgeRAM.Part) := GridOrderedEdgeRAM.block part A.edges r n w
  let last := GridPaddedCellImage.build (A.finalBanks limit) k (r*2) ((n+1)^k)
    (hiddenCount r n) (edgeCount r n) fieldSize z one
  have preSize : pre.labels+pre.registers+pre.slots ≤ 1000 := by
    change (10+57+41)+(5+18+17)+(0+12+9) ≤ 1000
    decide
  have portSize : port.labels+port.registers+port.slots ≤ 2500 := by
    let e := GridOrderedPinsRAM.program (w:=w) ((n+1)^k) (n+1)
    change 6+e.labels+(4+e.binds)+9 ≤ 2500
    have th := GridOrderedPinsRAM.time_per_port (w:=w) ((n+1)^k) (n+1)
    rw [DescriptorExpr.Term.labels_eq]
    dsimp only [e]
    omega
  have eqSize (part : GridOrderedEdgeRAM.Part) :
      (eq part).labels+(eq part).registers+(eq part).slots ≤ 800 := by
    let lo := A.edges.output+2*GridOrderedEdgeRAM.offset part r n
    let e := GridTopologyRAM.decoded (GridOrderedEdgeRAM.body (w:=w) part) lo (GridOrderedEdgeRAM.middle part n) 2
    change 6+e.labels+(4+e.binds)+4 ≤ 800
    dsimp only [e]
    rw [DescriptorExpr.Term.labels_eq,GridTopologyRAM.binds_decoded]
    have th := GridOrderedEdgeRAM.bind_bound (w:=w) part
    omega
  have lastSize : last.labels+last.registers+last.slots ≤ 90000 := GridPaddedCellImage.text_bound ..
  have hF := eqSize .focus
  have hN := eqSize .neighbor
  have hT := eqSize .through
  have hC := eqSize .center
  dsimp only [writing,prepare,GridOrderedEdgeRAM.build,Procedure.seq]
  dsimp only [pre,port,eq,last] at preSize portSize hF hN hT hC lastSize
  omega

/-- Authentic decoded rail settings include the physical direction and row,
the local data pointer originating in the endpoint scatter, compact X, and
the original rail-bit prefix. -/
structure Raw (A : Arena) (B : ℕ) (pin : Fin (r*2)→Bool) (m original : Memory w) : Prop where
  controller : Input X P code A B m original
  exterior : ∀ i : Fin (r*2),m i.val=bitWord w (pin i)

/-- The full preparatory ROM returns the actual contraction image on its
entire footprint. This is the memory condition consumed directly by the
native weighted evaluator. -/
theorem writing_spec (A : Arena) (B limit : ℕ) (pin : Fin (r*2)→Bool) (original : Memory w)
    (fits : Fits (n:=n) (r:=r) (w:=w) X A B) (selection : A.railMap.Fits w k n r B)
    (padded : GridPaddedCellImage.Fits (w:=w) X (wiring P) (A.finalBanks limit))
    (cap : GridApproximationAdvice.wordCount X ≤ 12*B)
    (installed : P.pass=GridLens.firstPassage P.direction P.row P.touch X.width P.untouched_capacity) :
    (writing A k n p r B limit (Fintype.card F) (code.encode 0) (code.encode 1)).Spec
      (fun m => Raw X P code A B pin m original)
      (fun _ o => ∀ i < BitLayout.footprint ((wiring P).network X.network),
        o i=BitLayout.memory ((wiring P).network X.network) code pin (fun _=>false) i)
      (clock k n r B limit) := by
  classical
  intro pcs regs pubs machine pc reg pub exit rom data cfg m start raw
  obtain ⟨first,loaded⟩ := select X P code A B m original fits selection P.untouched_capacity
    installed cap raw.controller
  let a := A.railMap
  let mid := GridPassageRAMMask.finalMemory P.direction P.row P.touch X.width a B m
  let pre := prepared X P A B mid
  have second : Procedure.Exec _ _ _ _ := execute X P code A B mid original fits loaded
  have both : Procedure.Exec _ _ _ _ := Procedure.Exec.then first second
  have ready := final_mounted X P code A B limit mid original fits cap loaded
  have preserved : ∀ i : Fin (r*2),pre i.val=bitWord w (pin i) := by
    have rail := fits.rails
    have small : r ≤ r*(n+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have state := a.final_correct P.direction P.row P.touch B selection m raw.controller.controller
    intro i
    have iv := i.isLt
    have earlier : mid i.val=m i.val := (GridPassageRAMMask.final_frame P.direction P.row P.touch X.width a B m _
      (.inl (by change i.val < 8*A.J; omega))).trans (state.input _ (by change i.val < 6*A.J; omega))
    have before : pre i.val=mid i.val := by
      dsimp only [pre,prepared,portImage,fillSegment,Arena.pins,Arena.edges]
      rw [ite_eq_right (by omega),ite_eq_right (by omega)]
    exact before.trans (earlier.trans (raw.exterior i))
  have last : (GridPaddedCellImage.build (A.finalBanks limit) k (r*2) ((n+1)^k)
      (hiddenCount r n) (edgeCount r n) (Fintype.card F) (code.encode 0) (code.encode 1)).Spec
      (fun input => GridPaddedCellImage.Mounted X (wiring P) code (A.finalBanks limit) input ∧
        ∀ i : Fin (r*2),input i.val=bitWord w (pin i))
      (fun input out => (∀ i < BitLayout.footprint ((wiring P).network X.network),
          out i=BitLayout.memory ((wiring P).network X.network) code pin (fun _=>false) i) ∧
        ∀ i,limit ≤ i → (i < A.J ∨ A.J+r*2 ≤ i) → out i=input i)
      (10+5*(r*2)+44004*limit) := by
    rw [←wiring_count P]
    exact GridPaddedCellImage.build_spec X (wiring P) code (A.finalBanks limit) padded pin
  have composed : Procedure.Spec _ _ _ _ := Procedure.Spec.seq both last (by
    intro _ out hout
    rw [hout]
    exact ⟨ready,preserved⟩)
  obtain ⟨t,ht,c',out,run,done,_,_,image,_⟩ := composed machine pc reg pub exit rom data cfg m start rfl
  exact ⟨t,ht,c',out,run,done,image⟩


end Hierarchy.GridOrderedSources

end OAI
