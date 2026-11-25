import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.TraceTemplateProgram
import OAI.ThreeFlat.RAM.PhysicalTraceRows

namespace OAI
/-! # A fixed native generator for copied X records and equality records

The operand bank supplies the three source addresses for each local template
row. Pin sources go through the selected cell's port map. Private sources
are rebased into that copy's hidden block. For an equality the same decoder
reads the two programmed endpoint pointers and generates its truth table. -/

namespace Hierarchy.GridOrderedRowRAM
open ThreeFlat
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open RAM RAM.BitLayout RAM.PhysicalProcedure RAM.DescriptorExpr RAM.GuardedDescriptor
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
open scoped BigOperators Fin.CommRing

variable {w : ℕ}

structure Layout where
  output : ℕ
  gate : ℕ
  pin : ℕ
  edge : ℕ

private def operand (i : Fin 10) : Term w 12 1 :=
  ![.result 0,.parameter 0,.parameter 1,.parameter 2,.parameter 3,.parameter 4,.parameter 5,
    .parameter 6,.parameter 7,.parameter 8] i

private def names : Inputs (Fin 10) := ⟨0,1,2,3,4,5,6,7,8,9⟩

private def lookup {v : ℕ} (base stride row col : Term w 12 v) : Term w 12 v :=
  .load (.binary .add (.binary .add base (.binary .mul stride row)) col)

private def lookups : Lookups w 12 10 where
  copy := lookup (.parameter 9) (.literal 11) (.result 1) (.result 0)
  pin := lookup (.parameter 10) (.parameter 1) (.result 1) (.result 0)
  left := lookup (.parameter 11) (.literal 2) (.result 1) (.literal 0)
  right := lookup (.parameter 11) (.literal 2) (.result 1) (.literal 1)

/-- One fixed instruction program; concrete sizes, field codes and bank
pointers all enter through twelve public word operands. -/
def program (w : ℕ) : Term w 12 1 := bindParams names lookups operand

theorem program_size : (program w).binds = 140 := by
  rw [program,binds_bindParams,binds_compile]
  simp [operand,Fin.sum_univ_succ,lookups,lookup,Term.load,Term.literal,Term.binary,
    Term.parameter,Term.binds]

def operands (S : Layout) (q oldCells oldHidden guards p h : ℕ) (z one : Word w) :
    Fin 12 → Word w :=
  ![(S.output:Word w),(q:Word w),(oldCells:Word w),(oldHidden:Word w),(guards:Word w),
    (p:Word w),(h:Word w),z,one,(S.gate:Word w),(S.pin:Word w),(S.edge:Word w)]

private def fetch (m : Memory w) (base stride : ℕ) (row col : Word w) : Word w :=
  m (((base:Word w)+(stride:Word w)*row+col).val)

private def readers (S : Layout) (q : ℕ) (m : Memory w) : Readers w where
  copy := fun _ i col => fetch m S.gate 11 i col
  pin := fun v i => fetch m S.pin q v i
  left := fun v _ => fetch m S.edge 2 v 0
  right := fun v _ => fetch m S.edge 2 v 1

private def interpreted (L : Lookups w 12 10) (data : Fin 12 → Word w) (m : Memory w)
    (vs : Fin 10 → Word w) : Readers w where
  copy block i col := L.copy.eval data m (Fin.cons col (Fin.cons i (Fin.cons block vs)))
  pin block i := L.pin.eval data m (Fin.cons i (Fin.cons block vs))
  left block i := L.left.eval data m (Fin.cons i (Fin.cons block vs))
  right block i := L.right.eval data m (Fin.cons i (Fin.cons block vs))

private theorem eval_generic (L : Lookups w 12 10) (data : Fin 12 → Word w)
    (m : Memory w) (a : ℕ) :
    let vs := fun i => (operand i).eval data m (fun _=>(a:Word w))
    let rr := interpreted L data m vs
    (bindParams names L operand).eval data m (fun _=>(a:Word w)) =
      word (names.map vs) rr.copy rr.pin rr.left rr.right := by
  dsimp only
  simp only [bindParams,Term.eval_instantiate,eval_compile,interpreted]

private theorem eval_program (S : Layout) (q oldCells oldHidden guards p h : ℕ)
    (z one : Word w) (a : ℕ) (m : Memory w) :
    (program w).eval (operands S q oldCells oldHidden guards p h z one) m (fun _ => (a : Word w)) =
      let rr := readers S q m
      word ⟨a,S.output,q,oldCells,oldHidden,guards,p,h,z,one⟩ rr.copy rr.pin rr.left rr.right := by
  let data := operands S q oldCells oldHidden guards p h z one
  let vs := fun i => (operand i).eval data m (fun _ => (a:Word w))
  have params : names.map vs = ⟨(a:Word w),S.output,q,oldCells,oldHidden,guards,p,h,z,one⟩ := by rfl
  have rr : interpreted lookups data m vs = readers S q m := by
    unfold interpreted readers
    congr 1
  calc
    _ = word (names.map vs) (interpreted lookups data m vs).copy (interpreted lookups data m vs).pin
          (interpreted lookups data m vs).left (interpreted lookups data m vs).right :=
      eval_generic lookups data m a
    _ = _ := by rw [params,rr]

private theorem fetch_at (m : Memory w) (base stride i j : ℕ)
    (bound : base+stride*i+j < 2^w) :
    fetch m base stride (i:Word w) (j:Word w) = m (base+stride*i+j) := by
  simp only [fetch,← Nat.cast_mul,← Nat.cast_add,Fin.val_cast_of_lt bound]

theorem entry_lt {b s count : ℕ} (i : Fin count) (j : Fin s) :
    b+s*i.val+j.val < b+s*count := by
  have hx := Nat.mul_le_mul_left s i.isLt
  rw [Nat.mul_succ] at hx
  have hj := j.isLt
  omega

variable {F : Type} [Field F] {q p h L : ℕ}

private def emptyNetwork (F : Type) : BitNetwork F 0 where
  internal := 0
  cells := 0
  source := Fin.elim0
  table := Fin.elim0

/-- Each copied gate loads one word from the compact X image. A port pointer
requires one additional indexed read; no other copy's template is stored. -/
theorem copy_at (S : Layout) (N : BitNetwork F q) (input : Fin L → Fin q → BitSource h p)
    (code : FieldCode F w) (m : Memory w)
    (gates : ∀ u j, m (S.gate+11*u.val+j.val) = record N code u j)
    (ports : ∀ (c : Fin L) (j : Fin q), m (S.pin+q*c.val+j.val) = (sourceAddress (input c j):Word w))
    (gateFit : S.gate+11*N.cells ≤ 2^w) (pinFit : S.pin+q*L ≤ 2^w)
    (sourceFit : 2+q+N.internal < 2^w) (widthFit : N.cells < 2^w) (eleven : 11 < 2^w)
    (c : Fin L) (u : Fin N.cells) (j : Fin 11)
    (fit : recordAddress S.output N.cells 0 c.val u.val j.val < 2^w) :
    (program w).eval (operands S q N.cells N.internal 0 p h (code.encode 0) (code.encode 1)) m
        (fun _ => (recordAddress S.output N.cells 0 c.val u.val j.val : Word w)) =
      if hj : j.val < 3 then Fin.ofNat _ (GuardedRecord.mapped N input c (N.source u ⟨j.val,hj⟩))
      else record N code u j := by
  let rr := readers S q m
  let noEdges : Fin L → Fin 0 → BitSource h p := fun _ => Fin.elim0
  have reads : Reads rr N input noEdges noEdges code := by
    constructor
    · intro _ i col
      exact (fetch_at m _ _ _ _ ((entry_lt i col).trans_le gateFit)).trans (gates i col)
    · intro v i
      exact (fetch_at m _ _ _ _ ((entry_lt v i).trans_le pinFit)).trans (ports v i)
    · intro _ i; exact i.elim0
    · intro _ i; exact i.elim0
  have recordEq := word_copied_record N input noEdges noEdges code rr reads S.output c u j
    sourceFit (by simpa using widthFit) eleven fit
  rw [GuardedRecord.copied_record] at recordEq
  exact (eval_program ..).trans recordEq

/-- Equality rows use two actual ordered endpoint addresses, a fixed zero
third input, and the encoded equality coefficients of the field. -/
theorem edge_at (S : Layout) (left right : Fin L → BitSource h p) (code : FieldCode F w)
    (m : Memory w)
    (lhs : ∀ c : Fin L, m (S.edge+2*c.val+0) = (sourceAddress (left c):Word w))
    (rhs : ∀ c : Fin L, m (S.edge+2*c.val+1) = (sourceAddress (right c):Word w))
    (edgeFit : S.edge+2*L ≤ 2^w) (eleven : 11 < 2^w)
    (c : Fin L) (j : Fin 11) (fit : recordAddress S.output 0 1 c.val 0 j.val < 2^w) :
    (program w).eval (operands S 0 0 0 1 p h (code.encode 0) (code.encode 1)) m
        (fun _ => (recordAddress S.output 0 1 c.val 0 j.val : Word w)) =
      if j.val=0 then Fin.ofNat _ (sourceAddress (left c)) else
      if j.val=1 then Fin.ofNat _ (sourceAddress (right c)) else
      if j.val=2 then 0 else
      if (j.val-3).testBit 0 = (j.val-3).testBit 1 then code.encode 1 else code.encode 0 := by
  let rr := readers S 0 m
  let noPins : Fin L → Fin 0 → BitSource h p := fun _ => Fin.elim0
  let le : Fin L → Fin 1 → BitSource h p := fun i _ => left i
  let ri : Fin L → Fin 1 → BitSource h p := fun i _ => right i
  have reads : Reads rr (emptyNetwork F) noPins le ri code := by
    constructor
    · intro _ u _; exact (u : Fin 0).elim0
    · intro _ i; exact i.elim0
    · intro v _
      exact (fetch_at m _ _ _ 0 ((entry_lt v (0:Fin 2)).trans_le edgeFit)).trans (lhs v)
    · intro v _
      exact (fetch_at m _ _ _ 1 ((entry_lt v (1:Fin 2)).trans_le edgeFit)).trans (rhs v)
  have recordEq := word_guard_record (emptyNetwork F) noPins le ri code rr reads S.output c (0:Fin 1) j
    (by change 0+1 < 2^w; omega) eleven fit
  rw [GuardedRecord.guard_record] at recordEq
  exact (eval_program ..).trans recordEq

/-- Scan into the real word RAM, at one bounded fixed instruction cost per
record word. Any installed caller can continue at its specified exit label. -/
def procedure (S : Layout) (q oldCells oldHidden guards p h words : ℕ) (z one : Word w) : Procedure w :=
  PhysicalInputPhases.writing (program w) (operands S q oldCells oldHidden guards p h z one) S.output words

theorem scan_spec (S : Layout) (q oldCells oldHidden guards p h words : ℕ) (z one : Word w)
    (valid : Memory w → Prop) (rowWord : ℕ → Word w) (stop : S.output+words < 2^w)
    (atWord : ∀ initial, valid initial → ∀ (a : Word w) (m : Memory w),
      S.output ≤ a.val → a.val < S.output+words → DescriptorScan.agreesOutside S.output
        (S.output+words) m initial →
      (program w).eval (operands S q oldCells oldHidden guards p h z one) m (fun _ => a) = rowWord a.val) :
    (procedure S q oldCells oldHidden guards p h words z one).Spec valid
      (fun m o => o=fillSegment S.output words rowWord m) (4+words*(2*(program w).binds+4)) :=
  PhysicalInputPhases.writing_spec _ _ _ _ stop _ _ atWord

end Hierarchy.GridOrderedRowRAM

end OAI
