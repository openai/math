import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # Native emission of triples from accepted protocol descriptors -/

namespace Hierarchy.ProtocolRAMEmit

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

/-- One occurrence on the accepted incidence tape, before reordering or coefficient lookup. -/
structure Row where
  group : ℕ
  endpoint : ℕ
  opposite : ℕ
  link : ℕ
  width : ℕ
  lengthCode : ℕ
  menu : ℕ

def Row.field (r : Row) : Fin 7 → ℕ := ![r.group,r.endpoint,r.opposite,r.link,r.width,r.lengthCode,r.menu]

/-- Endpoint and metric triples share the same link identifier. -/
def endpointFields : Fin 3 → Fin 7 := ![1,2,3]
def metricFields : Fin 3 → Fin 7 := ![3,4,5]
def gateFields : Fin 3 → Fin 7 := ![0,1,6]

variable {w n : ℕ}

def Packed (src : ℕ) (rows : Fin n → Row) (m : Memory w) : Prop :=
  ∀ i j, m (src+7*i.val+j.val) = ((rows i).field j : Word w)

private def offset (w dst : ℕ) : Term w 0 1 := .binary .sub (.result 0) (.literal dst)

private def chooseField (f : Fin 3 → Fin 7) (digit : Term w 0 1) : Term w 0 1 :=
  .select .eq digit (.literal 0) (.literal (f 0).val)
    (.select .eq digit (.literal 1) (.literal (f 1).val) (.literal (f 2).val))

/-- Compute the input address from the current output address and load the selected word. -/
def gather (w src dst : ℕ) (f : Fin 3 → Fin 7) : Term w 0 1 :=
  let i := Term.binary .div (offset w dst) (.literal 3)
  let j := Term.binary .mod (offset w dst) (.literal 3)
  .load (.binary .add (.binary .add (.literal src) (.binary .mul (.literal 7) i)) (chooseField f j))

theorem gather_binds (w src dst : ℕ) (f : Fin 3 → Fin 7) : (gather w src dst f).binds = 25 := by
  simp only [gather,offset,chooseField,Term.select,Term.load,Term.binary,Term.literal,Term.binds_letThen,Term.binds_rename,Term.binds]

def procedure (w src dst n : ℕ) (f : Fin 3 → Fin 7) : Procedure w :=
  PhysicalInputPhases.writing (gather w src dst f) Fin.elim0 dst (3*n)

def tripleWord (rows : Fin n → Row) (f : Fin 3 → Fin 7) (dst a : ℕ) : Word w :=
  if h : (a-dst)/3<n then ((rows ⟨_,h⟩).field (f ⟨(a-dst)%3,Nat.mod_lt _ (by decide)⟩) : Word w)
  else 0

theorem packed_fill {src dst : ℕ} {rows : Fin n → Row} {m : Memory w}
    (h : Packed src rows m) (apart : src+7*n ≤ dst ∨ dst+3*n ≤ src) (v : ℕ → Word w) :
    Packed src rows (fillSegment dst (3*n) v m) := by
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  have away : ¬ (dst ≤ src+7*i.val+j.val ∧ src+7*i.val+j.val < dst+3*n) := by omega
  simpa [fillSegment,away] using h i j

private theorem choose_eval (f : Fin 3 → Fin 7) (digit : Term w 0 1) (j : Fin 3)
    (m : Memory w) (a : Word w) (wide : 7 < 2^w)
    (tag : digit.eval Fin.elim0 m (fun _=>a) = (j.val : Word w)) :
    (chooseField f digit).eval Fin.elim0 m (fun _=>a) = ((f j).val : Word w) := by
  have small {i l : ℕ} (hi : i<2^w) (hl : l<2^w) : ((i:Word w)=(l:Word w)) ↔ i=l := by
    rw [Fin.ext_iff, Fin.val_cast_of_lt hi, Fin.val_cast_of_lt hl]
  have zeroTest : ((j.val : Word w) = 0) ↔ j.val=0 := small (i:=j.val) (l:=0) (by have:=j.isLt;omega) (by omega)
  have oneTest : ((j.val : Word w) = 1) ↔ j.val=1 := small (i:=j.val) (l:=1) (by have:=j.isLt;omega) (by omega)
  simp only [chooseField,Term.eval_select,Term.eval_literal,tag,Comparison.test,beq_iff_eq,zeroTest,oneTest]
  fin_cases j <;> rfl

/-- The RAM itself reads the packed source and fills only the requested triple table.
The same compiled code is used for every row ordinal. -/
theorem procedure_spec (src dst : ℕ) (rows : Fin n → Row) (f : Fin 3 → Fin 7)
    (wide : 7 < 2^w) (inputFit : src+7*n < 2^w) (outputFit : dst+3*n < 2^w)
    (apart : src+7*n ≤ dst ∨ dst+3*n ≤ src) :
    (procedure w src dst n f).Spec (Packed src rows)
      (fun m o => o=fillSegment dst (3*n) (tripleWord rows f dst) m) (4+162*n) := by
  have cost : 4+3*n*(2*(gather w src dst f).binds+4)=4+162*n := by rw [gather_binds];omega
  rw [←cost]
  apply PhysicalInputPhases.writing_spec _ _ _ _ outputFit
  intro input packed a m lo hi frame
  let q := a.val-dst
  let i : Fin n := ⟨q/3,by dsimp [q];omega⟩
  let j : Fin 3 := ⟨q%3,Nat.mod_lt _ (by decide)⟩
  have off : (offset w dst).eval Fin.elim0 m (fun _ => a) = (q : Word w) := by
    have hd : dst<2^w := by omega
    change a - (dst:Word w) = (q:Word w)
    apply Fin.ext
    have le : (dst:Word w)≤a := by change ((dst:Word w).val)≤_;rwa [Fin.val_cast_of_lt hd]
    rw [Fin.sub_val_of_le le,Fin.val_cast_of_lt hd,Fin.val_cast_of_lt (by dsimp [q];have:=a.isLt;omega : q<2^w)]
  have hq : q<2^w := by dsimp [q];have:=a.isLt;omega
  have div : (Term.binary .div (offset w dst) (.literal 3)).eval Fin.elim0 m (fun _=>a) = (i.val:Word w) := by
    simp only [Term.eval_binary, Term.eval_literal,off,BinaryOp.eval,Fin.val_cast_of_lt hq]
    have h3 : (3 : Word w).val=3 := Fin.val_cast_of_lt (by omega : 3<2^w)
    rw [h3];rfl
  have mod : (Term.binary .mod (offset w dst) (.literal 3)).eval Fin.elim0 m (fun _=>a) = (j.val:Word w) := by
    simp only [Term.eval_binary, Term.eval_literal,off,BinaryOp.eval,Fin.val_cast_of_lt hq]
    have h3 : (3 : Word w).val=3 := Fin.val_cast_of_lt (by omega : 3<2^w)
    rw [h3];rfl
  have hsrc : src+7*i.val+(f j).val < src+7*n := by have:=i.isLt;have:=(f j).isLt;omega
  have castAddr : ((src:Word w)+7*(i.val:Word w)+((f j).val:Word w)).val = src+7*i.val+(f j).val := by
    rw [←Nat.cast_ofNat (R:=Word w) (n:=7), ←Nat.cast_mul, ←Nat.cast_add, ←Nat.cast_add, Fin.val_cast_of_lt (hsrc.trans inputFit)]
  unfold gather
  rw [Term.eval_load,Term.eval_binary,Term.eval_binary,Term.eval_literal,Term.eval_binary,Term.eval_literal,div,choose_eval f _ j m a wide mod]
  change m (((src:Word w)+7*(i.val:Word w)+((f j).val:Word w)).val) = _
  rw [castAddr,frame _ (by omega),packed i (f j)]
  unfold tripleWord
  rw [dite_eq_left (show (a.val-dst)/3<n by omega)]

theorem read_triple (dst : ℕ) (rows : Fin n → Row) (f : Fin 3 → Fin 7)
    (m : Memory w) (i : Fin n) (j : Fin 3) :
    fillSegment dst (3*n) (tripleWord rows f dst) m (dst+3*i.val+j.val) = ((rows i).field (f j):Word w) := by
  have hi := i.isLt
  have hj := j.isLt
  have idx : (dst+3*i.val+j.val-dst)/3=i.val := by omega
  have col : (dst+3*i.val+j.val-dst)%3=j.val := by omega
  simp [fillSegment,tripleWord,show dst≤dst+3*i.val+j.val by omega,show dst+3*i.val+j.val<dst+3*n by omega,idx,col,hi]

/-- Three consecutive tables, each with one row of three words per accepted occurrence. -/
def emit (w src dst n : ℕ) : Procedure w :=
  ((procedure w src dst n endpointFields).seq
    (procedure w src (dst+3*n) n metricFields)).seq (procedure w src (dst+6*n) n gateFields)

def emitted (dst : ℕ) (rows : Fin n → Row) (input : Memory w) : Memory w :=
  fillSegment (dst+6*n) (3*n) (tripleWord rows gateFields (dst+6*n))
    (fillSegment (dst+3*n) (3*n) (tripleWord rows metricFields (dst+3*n))
      (fillSegment dst (3*n) (tripleWord rows endpointFields dst) input))

private theorem pass_spec (src dst : ℕ) (rows : Fin n → Row) (f : Fin 3 → Fin 7)
    (wide : 7 < 2^w) (inputFit : src+7*n < 2^w) (outputFit : dst+3*n < 2^w)
    (apart : src+7*n ≤ dst ∨ dst+3*n ≤ src) :
    (procedure w src dst n f).Spec (Packed src rows)
      (fun m o => o=fillSegment dst (3*n) (tripleWord rows f dst) m ∧ Packed src rows o)
      (4+162*n) := by
  intro P R K M pc reg pub exit installed params c m start packed
  obtain ⟨t,ht,out,o,run,hpc,eq⟩ :=
    procedure_spec src dst rows f wide inputFit outputFit apart M pc reg pub exit installed params c m start packed
  subst o
  exact ⟨t,ht,out,_,run,hpc,rfl,packed_fill packed apart _⟩

theorem emit_spec (src dst : ℕ) (rows : Fin n → Row)
    (wide : 7 < 2^w) (inputFit : src+7*n < 2^w) (outputFit : dst+9*n < 2^w)
    (apart : src+7*n ≤ dst ∨ dst+9*n ≤ src) :
    (emit w src dst n).Spec (Packed src rows) (fun m o => o=emitted dst rows m) (12+486*n) := by
  have a : (procedure w src dst n endpointFields).Spec _ _ _ := pass_spec src dst rows endpointFields wide inputFit (by omega) (by omega)
  have b : (procedure w src (dst+3*n) n metricFields).Spec _ _ _ := pass_spec src (dst+3*n) rows metricFields wide inputFit (by omega) (by omega)
  have c : (procedure w src (dst+6*n) n gateFields).Spec _ _ _ := pass_spec src (dst+6*n) rows gateFields wide inputFit (by omega) (by omega)
  have ab : ((procedure w src dst n endpointFields).seq (procedure w src (dst+3*n) n metricFields)).Spec _ _ _ := a.seq b (fun _ _ h=>h.2)
  have abc : (emit w src dst n).Spec _ _ _ := ab.seq c (fun _ _ ⟨_,_,h⟩=>h.2)
  intro P R K M pc reg pub exit rom data cfg m start packed
  obtain ⟨t,ht,out,o,run,stop,b',⟨a',⟨eq₀,_⟩,⟨eq₁,_⟩⟩,eq₂,_⟩ :=
    abc M pc reg pub exit rom data cfg m start packed
  exact ⟨t,by omega,out,o,run,stop,by simp only [emitted,eq₂,eq₁,eq₀]⟩

private theorem fill_away (base len : ℕ) (val : ℕ → Word w) (old : Memory w) {a : ℕ}
    (away : a < base ∨ base+len ≤ a) : fillSegment base len val old a = old a :=
  ite_eq_right (by omega)

theorem emitted_read (dst : ℕ) (rows : Fin n → Row) (m : Memory w) (i : Fin n) (j : Fin 3) :
    emitted dst rows m (dst+3*i.val+j.val) = ((rows i).field (endpointFields j):Word w) ∧
    emitted dst rows m (dst+3*n+3*i.val+j.val) = ((rows i).field (metricFields j):Word w) ∧
    emitted dst rows m (dst+6*n+3*i.val+j.val) = ((rows i).field (gateFields j):Word w) := by
  have hi := i.isLt
  have hj := j.isLt
  constructor
  · unfold emitted
    rw [fill_away _ _ _ _ (by omega),fill_away _ _ _ _ (by omega)]
    exact read_triple ..
  constructor
  · unfold emitted
    rw [fill_away _ _ _ _ (by omega)]
    exact read_triple ..
  · exact read_triple ..

theorem emitted_read_nat (dst : ℕ) (rows : Fin n → Row) (m : Memory w) (i : Fin n) (j : Fin 3)
    (fits : ∀ f, (rows i).field f < 2^w) :
    (emitted dst rows m (dst+3*i.val+j.val)).val = (rows i).field (endpointFields j) ∧
    (emitted dst rows m (dst+3*n+3*i.val+j.val)).val = (rows i).field (metricFields j) ∧
    (emitted dst rows m (dst+6*n+3*i.val+j.val)).val = (rows i).field (gateFields j) := by
  obtain ⟨endpoints,metrics,gates⟩ := emitted_read dst rows m i j
  rw [endpoints,metrics,gates,Fin.val_cast_of_lt (fits _),Fin.val_cast_of_lt (fits _),Fin.val_cast_of_lt (fits _)]
  exact ⟨rfl,rfl,rfl⟩

/-- Zero width represents an inactive entry in the common padded board. -/
def Row.Active (r : Row) : Prop := 0<r.width

theorem emitted_active_iff (dst : ℕ) (rows : Fin n → Row) (m : Memory w) (i : Fin n)
    (bound : (rows i).width < 2^w) :
    0 < (emitted dst rows m (dst+3*n+3*i.val+1)).val ↔ (rows i).Active := by
  have value := (emitted_read dst rows m i (1:Fin 3)).2.1
  change emitted dst rows m (dst+3*n+3*i.val+1) = ((rows i).width:Word w) at value
  rw [value, Fin.val_cast_of_lt bound]
  rfl

/-- The physical group occupancy predicate reads the emitted group and width columns. -/
def occupied (dst n group : ℕ) (m : Memory w) : Prop :=
  ∃ i : Fin n, 0 < (m (dst+3*n+3*i.val+1)).val ∧ (m (dst+6*n+3*i.val)).val = group

theorem emitted_occupied_iff (dst group : ℕ) (rows : Fin n → Row) (m : Memory w)
    (fits : ∀ i, (rows i).width < 2^w ∧ (rows i).group < 2^w) :
    occupied dst n group (emitted dst rows m) ↔ ∃ i, (rows i).Active ∧ (rows i).group=group := by
  unfold occupied
  apply exists_congr
  intro i
  have g := (emitted_read dst rows m i (0:Fin 3)).2.2
  change emitted dst rows m (dst+6*n+3*i.val+0) = ((rows i).group:Word w) at g
  simp only [Nat.add_zero] at g
  rw [emitted_active_iff dst rows m i (fits i).1,g,Fin.val_cast_of_lt (fits i).2]

theorem emitted_outside (dst : ℕ) (rows : Fin n → Row) (m : Memory w) (a : ℕ)
    (away : a<dst ∨ dst+9*n≤a) : emitted dst rows m a = m a := by
  simp [emitted,fillSegment,show ¬ (dst+6*n≤a ∧ a<dst+6*n+3*n) by omega,
    show ¬ (dst+3*n≤a ∧ a<dst+3*n+3*n) by omega,show ¬ (dst≤a ∧ a<dst+3*n) by omega]

/-- Word operations charged at each instruction reached by the native run. -/
def wordWork {P R K : ℕ} (machine : Machine w P R K) (t : ℕ) (c : Config w P R) (m : Memory w) : ℕ :=
  ∑ i : Fin t, match advance machine.program i.val c m with
    | none => 0
    | some (atStep,_) => (machine.code atStep.pc).wordWork

theorem emit_wordWork {P R K : ℕ} (machine : Machine w P R K) (t : ℕ) (c : Config w P R)
    (m : Memory w) (bound : t ≤ 12+486*n) : wordWork machine t c m ≤ 72+2916*n := by
  unfold wordWork
  calc
    _ ≤ ∑ _ : Fin t, 6 := Finset.sum_le_sum fun i _ => by
      split
      · decide
      · exact Instr.wordWork_le _
    _ ≤ 72+2916*n := by simp;omega

theorem emit_size (w src dst n : ℕ) :
    (emit w src dst n).labels=246 ∧ (emit w src dst n).registers=87 ∧ (emit w src dst n).slots=0 := by
  simp [emit, Procedure.seq, procedure, PhysicalInputPhases.writing, Term.labels_eq, gather_binds]

end Hierarchy.ProtocolRAMEmit

end OAI
