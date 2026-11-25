import OAI.Hierarchy.ProtocolRAMSchedule
import OAI.Hierarchy.TaggedShorterCheapCPU

namespace OAI
/-! # Allowed opcodes at every linked controller instruction -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure

variable {w k n p r : ℕ}

def allowed : BinaryOp → Prop
  | .add | .sub | .bitAnd => True
  | _ => False

def opAllowed : Op w k n → Prop
  | .binary b _ _ => allowed b
  | _ => True

def admissible : {n : ℕ} → Term w k n → Prop
  | _,.result _ => True
  | _,.bind o e => opAllowed o ∧ admissible e

@[simp] theorem allow_rename {s : ℕ} (f : Fin n → Fin s) (o : Op w k n) :
    opAllowed (o.rename f) ↔ opAllowed o := by cases o <;> rfl

@[simp] theorem admissible_rename {s : ℕ} (f : Fin n → Fin s) (e : Term w k n) :
    admissible (e.rename f) ↔ admissible e := by
  induction e generalizing s with
  | result => rfl
  | bind o e ih => simp only [Term.rename,admissible,allow_rename,ih]

@[simp] theorem admissible_let (e : Term w k n) (b : Term w k (n+1)) :
    admissible (e.letThen b) ↔ admissible e ∧ admissible b := by
  induction e with
  | result => simp [Term.letThen,admissible,admissible_rename]
  | bind o e ih => simp only [Term.letThen,admissible,ih,admissible_rename,and_assoc]

theorem good_compile (e : Expr) (w base : ℕ) : admissible (e.compile w base) := by
  induction e with
  | op o x y hx hy => cases o <;> simp [Expr.compile,RowOp.opcode,Term.binary,admissible_let,
      admissible_rename,admissible,opAllowed,allowed,hx,hy]
  | _ => simp_all [Expr.compile,Term.load,Term.literal,Term.binary,Term.select,admissible_let,
      admissible_rename,admissible,opAllowed,allowed]

theorem good_public {K : ℕ} (e : Term w k n) (pub : Fin k → Fin K) :
    admissible (e.mapPublic pub) ↔ admissible e := by
  induction e with
  | result => rfl
  | bind o e ih => cases o <;> simp only [Term.mapPublic,admissible,Op.mapPublic,opAllowed,ih]

private theorem cheap_instruction (o : Op w k n) (ok : opAllowed o)
    (pc : Fin 3 → Fin p) (vs : Fin n → Fin r) (dst : Fin r) (exit : Fin p) (i : Fin 3) :
    TaggedShorterCheapCPU.Cheap (o.instruction pc vs dst exit i) := by
  cases o with
  | binary b x y => cases b <;> fin_cases i <;>
      simp_all [opAllowed,allowed,Op.instruction,TaggedShorterCheapCPU.Cheap]
  | select c x y a b => cases c <;> fin_cases i <;> trivial
  | _ => fin_cases i <;> trivial

private theorem cheap_term (e : Term w k n) (valid : admissible e)
    (loc : Fin e.labels → Fin p) (vs : Fin n → Fin r) (tmp : Fin e.binds → Fin r)
    (out : Fin r) (exit : Fin p) (i : Fin e.labels) :
    TaggedShorterCheapCPU.Cheap (e.emit loc vs tmp out exit i) := by
  induction e with
  | result => trivial
  | bind o e ih =>
    induction i using Fin.addCases with
    | left i =>
      simp only [Term.emit,Fin.addCases_left]
      exact cheap_instruction o valid.1 _ _ _ _ i
    | right i =>
      simp only [Term.emit,Fin.addCases_right]
      exact ih valid.2 _ _ _ i

def CheapCode (A : Procedure w) : Prop :=
  ∀ {P R K : ℕ} (pc : Fin A.labels ↪ Fin P) (reg : Fin A.registers ↪ Fin R)
    (pub : Fin A.slots → Fin K) (exit : Fin P) (i : Fin A.labels),
    TaggedShorterCheapCPU.Cheap (A.block.emit pc reg pub exit i)

theorem cheap_seq {A B : Procedure w} (a : CheapCode A) (b : CheapCode B) : CheapCode (A.seq B) := by
  intro P R K pc reg pub exit i
  induction i using Fin.addCases with
  | left j =>
    simp only [Procedure.seq,ContinuationLink.Block.seq,ContinuationLink.Block.reindex,Fin.addCases_left]
    exact a _ _ _ _ j
  | right j =>
    simp only [Procedure.seq,ContinuationLink.Block.seq,ContinuationLink.Block.reindex,Fin.addCases_right]
    exact b _ _ _ _ j

theorem cheap_frame (e : Term w k 1) (valid : admissible e) (A : PhysicalScan.Frame e p r)
    (lo hi : ℕ) (j : Fin (6+e.labels)) : TaggedShorterCheapCPU.Cheap (A.emit lo hi j) := by
  induction j using Fin.addCases with
  | left z =>
    simp only [PhysicalScan.Frame.emit,Fin.addCases_left]
    fin_cases z <;> trivial
  | right z =>
    simp only [PhysicalScan.Frame.emit,Fin.addCases_right]
    exact cheap_term e valid _ _ _ _ _ z

theorem writing_cheap (e : Term w k 1) (pub : Fin k → Word w) (out len : ℕ) (ok : admissible e) :
    CheapCode (PhysicalInputPhases.writing e pub out len) := by
  intro P R K pc reg data exit j
  let φ : Fin k → Fin K := data
  let pcs : Fin (6+e.labels) ↪ Fin P := pc
  let regs : Fin (4+e.binds) ↪ Fin R := reg
  let A := PhysicalScan.linkedFrame e pcs regs φ exit
  let j' : Fin (6+e.labels) := j
  exact cheap_frame (e.mapPublic φ) ((good_public e φ).mpr ok) A out (out+len)
    (j'.cast (by simp only [Term.labels_mapPublic]))

theorem scan_cheap (w out n : ℕ) (e : Expr) : CheapCode (scan w out n e) :=
  writing_cheap _ _ _ _ (good_compile e w out)

theorem program_cheap (w : ℕ) (ps : List Pass) : CheapCode (program w ps) := by
  induction ps with
  | nil =>
    intro P R K pc reg pub exit i
    exact scan_cheap w 0 0 (.lit 0) pc reg pub exit i
  | cons p ps ih => exact cheap_seq (scan_cheap w p.out p.rows p.term) ih


end Hierarchy.ProtocolRAM

end OAI
