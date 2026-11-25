import OAI.Hierarchy.ProtocolRAMRowChoice
import OAI.Hierarchy.ProtocolRAMSchedule
import OAI.ThreeFlat.RAM.EffectSeedProcedure

namespace OAI
/-! # Computing all sparse board writes from the native rank and report columns -/

namespace Hierarchy.TaggedShorterEmitMachine
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open ProtocolRAM
open scoped Fin.CommRing

variable {W R : ℕ}

/-- Source and target tables are absolute regions of the same RAM. The three ordinal
directories are fixed, as are the arithmetic and candidate-address tables. -/
structure Tables where
  owner : Bank
  subslot : Bank
  column : Bank
  metricWidth : Bank
  gateGroup : Bank
  widthClass : Bank
  widthPieces : Bank
  common : Bank
  left : Bank
  right : Bank
  groupBase : Bank
  quotient : Bank
  remainder : Bank
  pointer : Fin 5 → Bank

private abbrev add (a b : Expr) := Expr.op .add a b
private abbrev triple (r : Expr) := add (add r r) r
private abbrev fourth (r : Expr) := add (add r r) (add r r)

def select (A : Tables) (γ : ℕ) (yes no : Expr) : Expr :=
  let r := Expr.lookup A.owner .row
  let z := Expr.lookup A.subslot .row
  let width := Expr.lookup A.metricWidth (triple r)
  .branch .eq (.lookup A.widthClass width) (.lit γ)
    (.branch .lt z (.lookup A.widthPieces width) yes no) no

/-- One occupied flag, the two endpoint masks, and the two packed identifiers,
each emitted as an address followed by its value. -/
def term (A : Tables) (γ sink : ℕ) : Expr :=
  let r := Expr.lookup A.owner .row
  let z := Expr.lookup A.subslot .row
  let g := Expr.lookup A.gateGroup (triple r)
  let rank := add (.lookup A.common (fourth r)) z
  let candidate := add (.lookup A.groupBase g) (.lookup A.quotient rank)
  let ptr (j : Fin 5) := Expr.lookup (A.pointer j) candidate
  let l := add (.lookup A.left r) z
  let t := add (.lookup A.right r) z
  let identifier := Expr.lookup A.remainder rank
  let active := chooseField 10 0
    ![ptr 0,.lit 1,add (ptr 1) l,.lit 1,add (ptr 2) l,identifier,
      add (ptr 3) t,.lit 1,add (ptr 4) t,identifier] (.lookup A.column .row)
  let blank := Expr.branch .eq (.op .mask .row (.lit 1)) (.lit 0) (.lit sink) (.lit 0)
  select A γ active blank

/-- Equations for the precise input reads at a potential transport slot. The two
strides come directly from the emitted descriptor triples and the four-word
native weighted-prefix row. The local side ranks have been scattered to original order. -/
structure Source (A : Tables) (m : Memory W) (a : Word W) (i z j bits g γ pieces cr l r : ℕ) : Prop where
  owner : A.owner.read m a=(i:Word W)
  subslot : A.subslot.read m a=(z:Word W)
  column : (A.column.read m a).val=j
  width : A.metricWidth.read m ((3*i : ℕ):Word W)=(bits:Word W)
  group : A.gateGroup.read m ((3*i : ℕ):Word W)=(g:Word W)
  widthClass : (A.widthClass.read m (bits:Word W)).val=γ
  widthPieces : (A.widthPieces.read m (bits:Word W)).val=pieces
  common : A.common.read m ((4*i : ℕ):Word W)=(cr:Word W)
  left : A.left.read m (i:Word W)=(l:Word W)
  right : A.right.read m (i:Word W)=(r:Word W)

structure Addresses (A : Tables) (m : Memory W) (g rank B : ℕ)
    (ptr : Fin 5 → Word W) where
  /-- Within each public group directory candidates are consecutive. -/
  base : ℕ
  groupBase : A.groupBase.read m (g:Word W)=(base:Word W)
  quotient : A.quotient.read m (rank:Word W)=((rank/B:ℕ):Word W)
  remainder : A.remainder.read m (rank:Word W)=((rank%B:ℕ):Word W)
  pointer : ∀ j, (A.pointer j).read m ((base+rank/B : ℕ):Word W)=ptr j

private theorem three (i : ℕ) : (i:Word W)+(i:Word W)+(i:Word W)=((3*i:ℕ):Word W) := by
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  ring

private theorem four (i : ℕ) : ((i:Word W)+(i:Word W))+((i:Word W)+(i:Word W))=((4*i:ℕ):Word W) := by
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  ring

def recordWords (ptr : Fin 5→Word W) (l r id : Word W) : Fin 10→Word W :=
  ![ptr 0,1,ptr 1+l,1,ptr 2+l,id,ptr 3+r,1,ptr 4+r,id]

theorem term_live (A : Tables) (m : Memory W) (a : Word W)
    (i z bits g γ pieces cr l r B sink : ℕ) (j : Fin 10) (ptr : Fin 5 → Word W)
    (src : Source A m a i z j.val bits g γ pieces cr l r)
    (dst : Addresses A m g (cr+z) B ptr) (small : 10≤2^W)
    (classFits : γ<2^W) (live : z<pieces) (zFit : z<2^W) :
    (term A γ sink).eval m a =
      recordWords ptr ((l+z:ℕ):Word W) ((r+z:ℕ):Word W) (((cr+z)%B:ℕ):Word W) j := by
  have cl : A.widthClass.read m (bits:Word W)=(γ:Word W) :=
    Fin.ext (src.widthClass.trans (Fin.val_cast_of_lt classFits).symm)
  have choose : (z:Word W)<A.widthPieces.read m (bits:Word W) := by
    rw [Fin.lt_def, Fin.val_cast_of_lt zFit,src.widthPieces]
    exact live
  simp only [term,select,Expr.eval,RowOp.opcode,BinaryOp.eval,Comparison.test,beq_iff_eq,
    src.owner,src.subslot,three i,src.width,cl,decide_eq_true_eq,choose,ite_true]
  rw [eval_chooseField 10 0 _ _ m a j (by omega) (by simpa [Expr.eval] using src.column)]
  have t3 : i+i+i=3*i := by omega
  have t4 : i+i+(i+i)=4*i := by omega
  have readGroup : A.gateGroup.read m (3*(i:Word W))=(g:Word W) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using src.group
  have readCommon : A.common.read m (4*(i:Word W))=(cr:Word W) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using src.common
  have addr (j : Fin 5) : (A.pointer j).read m
      (A.groupBase.read m (A.gateGroup.read m (3*(i:Word W)))+
       A.quotient.read m (A.common.read m (4*(i:Word W))+(z:Word W)))=ptr j := by
    rw [readGroup,readCommon,dst.groupBase,←Nat.cast_add,dst.quotient,←Nat.cast_add,dst.pointer]
  have lane : A.remainder.read m (A.common.read m (4*(i:Word W))+(z:Word W))=
      (((cr+z)%B:ℕ):Word W) := by
    rw [readCommon,←Nat.cast_add,dst.remainder]
  fin_cases j <;>
    simp [recordWords,t3,t4,Expr.eval,RowOp.opcode,BinaryOp.eval,src.owner,src.subslot,src.left,src.right,←Nat.cast_add] <;>
    first | exact addr _ | exact lane

theorem term_idle (A : Tables) (m : Memory W) (a : Word W)
    (i z j bits g γ actual pieces cr l r sink : ℕ)
    (src : Source A m a i z j bits g actual pieces cr l r)
    (unused : actual≠γ ∨ pieces≤z) (classFits : γ<2^W) (zFit : z<2^W)
    (parity : (BinaryOp.bitAnd.eval a (1:Word W)).val=j%2) :
    (term A γ sink).eval m a = if j%2=0 then (sink:Word W) else 0 := by
  have cl : A.widthClass.read m (bits:Word W)=(γ:Word W) ↔ actual=γ := by
    rw [Fin.ext_iff,src.widthClass,Fin.val_cast_of_lt classFits]
  have count : (z:Word W)<A.widthPieces.read m (bits:Word W) ↔ z<pieces := by
    rw [Fin.lt_def,Fin.val_cast_of_lt zFit,src.widthPieces]
  have bit : BinaryOp.bitAnd.eval a (1:Word W)=0 ↔ j%2=0 := by
    rw [Fin.ext_iff,parity];rfl
  simp only [term,select,Expr.eval,RowOp.opcode,show (BinaryOp.add.eval : Word W → Word W → Word W)=(·+·) from rfl,
    Comparison.test,beq_iff_eq,decide_eq_true_eq,src.owner,src.subslot,three i,src.width,cl,count]
  rcases unused with h|h
  · simp [h,bit]
  · simp [Nat.not_lt.mpr h,bit]

def procedure (W src R γ sink : ℕ) (A : Tables) : Procedure W :=
  (scan W src (10*R) (term A γ sink)).seq (EffectSeed.scatter W src (5*R))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem term_work (A : Tables) (γ sink : ℕ) : (term A γ sink).work=808 := by
  simp [term,select,chooseField,Expr.work,add,triple,fourth]

theorem procedure_size (A : Tables) (W src R γ sink : ℕ) :
    (procedure W src R γ sink A).labels=2440 ∧
    (procedure W src R γ sink A).registers=817 ∧ (procedure W src R γ sink A).slots=2 := by
  have h := scan_size W src (10*R) (term A γ sink)
  simp only [term_work] at h
  obtain ⟨labels,regs,slots⟩ := h
  change _+9=2440 ∧ _+5=817 ∧ _+2=2
  simp [labels,regs,slots]

/-- The source scans and the nine-label replay form a single deterministic native prefix. -/
theorem exec (A : Tables) (src R γ sink : ℕ) (m : Memory W)
    (fit : (term A γ sink).Fits W src) (room : src+10*R<2^W)
    (writes : List (EffectStream.Record W)) (ln : writes.length=5*R)
    (values : ∀ i : Fin writes.length,
        (term A γ sink).eval m ((2*i.val:ℕ):Word W)=(writes.get i).1 ∧
        (term A γ sink).eval m ((2*i.val+1:ℕ):Word W)=(writes.get i).2)
    (away : EffectStream.Safe src writes) :
    (procedure W src R γ sink A).Exec m
      (after (image src (10*R) (term A γ sink) m) (EffectStream.events writes))
      ((4+(10*R)*(2*(term A γ sink).work+4))+(4+6*(5*R))) := by
  let out := image src (10*R) (term A γ sink) m
  have loaded : EffectStream.Loaded out src writes := by
    rw [EffectStream.loaded_iff]
    intro i
    have er (j : ℕ) (hj : j<10*R) :
        out (src+j)=(term A γ sink).eval m (j:Word W) := by
      simp [out,image,fillSegment,show src+j<src+10*R by omega,Nat.cast_add]
    have hi := i.isLt
    exact ⟨(er _ (by omega)).trans (values i).1,
      by simpa only [Nat.add_assoc] using (er (2*i.val+1) (by omega)).trans (values i).2⟩
  have replay : (EffectSeed.scatter W src writes.length).Exec out
      (after out (EffectStream.events writes)) (4+6*writes.length) :=
    Procedure.Spec.exec (EffectSeed.scatter_spec src writes (by omega) away) out loaded
  rw [ln] at replay
  intro P R' K M pc reg pub exit installed publicData cfg mem start eq
  exact Procedure.Exec.then (scan_exec src (10*R) (term A γ sink) m fit room) replay
    M pc reg pub exit installed publicData cfg mem start eq

end Hierarchy.TaggedShorterEmitMachine

end OAI
