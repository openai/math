import OAI.Computability.VPVNP.CompressorFlatRowWorker
import OAI.Computability.VPVNP.CompressorShrinkABSliceTable

/-!
# Whole-level calendar visits for the shrinking AB slice bank

Each fixed field count or rank pair contributes one catalog visit. The global
cursor ranges over assigned bundles. Register operands are computed from
that ordinal and the level's four sorted width/offset heads.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkABSliceRecipe

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PhaseRecipe BlockPlanner
open IndexedStarts ShrinkABSliceTable SliceRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Layout scalars read by the online planner. -/
structure Inputs where
  /-- Recipe expression for the number of bundle rows visited in each whole-level AB scan. -/
  rows : Expr
  /-- Base-address expression of the old thick fields' starting offsets. -/
  oldStarts : Expr
  /-- Base-address expression of the sorted old thick-field widths. -/
  oldWidths : Expr
  /-- Distance in words between consecutive bundle rows of the old width and start columns. -/
  oldStride : Expr
  /-- Base-address expression of the starting offsets of the new AB pieces. -/
  newStarts : Expr
  /-- Base-address expression of the new AB piece widths. -/
  newWidths : Expr
  /-- Distance in words between consecutive bundle rows of the AB width and start columns. -/
  newStride : Expr
  /-- Recipe expression for the address of the first bundle's intersection and
  endpoint-reference bank. -/
  firstBank : Expr

/-- Global-row address and stride of one local operand. All AB reads use
direct affine operands, so the worker prologue itself uses zero probes. -/
abbrev Affine := Expr × Expr

/-- Represent a constant flat-row operand by its literal base and a zero bundle stride. -/
def constant (x : ℕ) : Affine := (.lit x,.lit 0)
/-- An operand at a fixed offset inside each bundle's AB bank, with the full bank capacity as
its inter-bundle stride. -/
def bankField (I : Inputs) (m n off : ℕ) : Affine := (I.firstBank.add (.lit off),.lit (capacity m n))

/-- Encode the local affine operands and fixed field cursor as flat-row prologue parameters,
with a base, stride and zero bias for each. -/
def arguments {k : ℕ} (localParams : Fin k → Affine) (cursor : ℕ) : Fin (FlatRows.Params k) → Expr :=
  fun j =>
    let digit := finProdFinEquiv.symm j
    let e := Fin.snoc (α := fun _ => Affine) localParams (constant cursor) digit.1
    ![e.1,e.2,.lit 0] digit.2

/-- Compile a local AB worker into a visit that scans every bundle at one fixed local cursor. -/
def flat {r p k : ℕ} (core : Template p r k) (I : Inputs) (par : Fin k → Affine) (cursor : ℕ) : Visit :=
  ⟨⟨_,_,_,FlatRows.compile core (fun _ => false)⟩,.lit 0,I.rows,arguments par cursor⟩

/-- The per-bundle base address from which the clearing worker zeros the endpoint counts. -/
def clearParams (I : Inputs) (m n : ℕ) : Fin 1 → Affine := fun _ => bankField I m n 0

/-- Operands for computing a field-pair intersection, including the new field count, both
width/start column pairs, and the frame destination. -/
def pairParams (I : Inputs) (m n : ℕ) : Fin 6 → Affine :=
  ![constant n,(I.oldStarts,I.oldStride),(I.oldWidths,I.oldStride),(I.newStarts,I.newStride),
    (I.newWidths,I.newStride),bankField I m n (m+n)]

/-- The field counts, intersection frames, endpoint counts and reference arrays used to link
positive intersections into the two directories. -/
def refParams (I : Inputs) (m n : ℕ) : Fin 7 → Affine :=
  ![constant n,constant m,bankField I m n (m+n),bankField I m n 0,
    bankField I m n (m+n+3*(m*n)),bankField I m n m,bankField I m n (m+n+4*(m*n))]

/-- One indexed whole-bundle scan that clears endpoint counts, computes an intersection frame
or appends its endpoint references. -/
inductive Stage (m n : ℕ)
  | clear (i : Fin (m+n))
  | pair (i : Fin (m*n))
  | refs (i : Fin (m*n))

/-- Select the clear, pair or reference worker and build its whole-level visit at the specified
local index. -/
def stage {m n : ℕ} (I : Inputs) : Stage m n → Visit
  | .clear i => flat (template clearOps 0) I (clearParams I m n) i.val
  | .pair i => flat IndexedPair.table I (pairParams I m n) i.val
  | .refs i => flat adjTemplate I (refParams I m n) i.val

/-- The AB execution order, clearing every endpoint count before computing all field-pair
frames and then linking their references. -/
def phases (m n : ℕ) : List (Stage m n) :=
  ((List.finRange (m+n)).map .clear ++ (List.finRange (m*n)).map .pair) ++ (List.finRange (m*n)).map .refs

/-- The catalog visits implementing the complete AB schedule for the given input columns and
field counts. -/
def visits (I : Inputs) (m n : ℕ) : List Visit := (phases m n).map (stage I)

theorem visits_length (I : Inputs) (m n : ℕ) : (visits I m n).length = m+n+2*(m*n) := by
  simp [visits,phases]; omega

variable (I : Inputs) (pub : Fin 5 → Word w) (s : Word w) (mem : Memory w)

/-- The recipe expressions evaluate to the actual row count, bank origin, and old and AB column
heads and strides. -/
structure Describes (t p : Fin 5 → Word w) (rows first : ℕ) : Prop where
  rowsAt : I.rows.eval pub s mem = (rows : Word w)
  start : I.firstBank.eval pub s mem = (first : Word w)
  oldStarts : I.oldStarts.eval pub s mem = t 3
  oldWidths : I.oldWidths.eval pub s mem = t 2
  oldStride : I.oldStride.eval pub s mem = t 1
  newStarts : I.newStarts.eval pub s mem = p 4
  newWidths : I.newWidths.eval pub s mem = p 3
  newStride : I.newStride.eval pub s mem = p 1

/-- The flat worker's concrete public words obtained by evaluating its affine parameter
expressions and fixed local index in the reference memory. -/
def evaluated {k : ℕ} (par : Fin k → Affine) (localIdx : ℕ) : FlatRows.Public k w :=
  fun j => (arguments par localIdx j).eval pub s mem


private theorem affine {k : ℕ} (par : Fin k → Affine) (j : Fin k) (id : ℕ) (row : Word w) (m : Memory w) :
    FlatRows.value (fun _ => false) (evaluated pub s mem par id) row m j.castSucc =
      (par j).1.eval pub s mem+row*(par j).2.eval pub s mem := by
  simp [FlatRows.value,FlatRows.addr,evaluated,arguments,FlatRows.field,Expr.eval]

private theorem local_val {k : ℕ} (par : Fin k → Affine) (id : ℕ) (row : Word w) (m : Memory w) :
    FlatRows.value (fun _ => false) (evaluated pub s mem par id) row m (Fin.last k) = (id : Word w) := by
  simp [FlatRows.value,FlatRows.addr,evaluated,arguments,FlatRows.field,Expr.eval,constant]

private theorem bank_add (B i cap offset : ℕ) :
    (B : Word w)+(offset : Word w)+(i : Word w)*(cap : Word w) = Fin.ofNat _ (B+i*cap+offset) := by
  change _ = ((B+i*cap+offset : ℕ) : Word w)
  push_cast; ring

variable {t p : Fin 5 → Word w} {rows first : ℕ}
variable (D : Describes I pub s mem t p rows first)
include D

theorem clear_operands (m n id row : ℕ) (m' : Memory w) :
    (fun j : Fin 1 => FlatRows.value (fun _ => false) (evaluated pub s mem (clearParams I m n) id)
      (row : Word w) m' j.castSucc) = (fun _ => bank first m n row) := by
  funext j
  rw [affine]
  change I.firstBank.eval pub s mem+0+(row : Word w)*((capacity m n : ℕ) : Word w) = _
  rw [D.start,add_zero]
  change _ = ((first+row*capacity m n : ℕ) : Word w)
  push_cast; rfl

theorem pair_operands {m n : ℕ} (L : Layout t p rows m n first) (id : ℕ) (i : Fin rows) (m' : Memory w) :
    (fun j : Fin 6 => FlatRows.value (fun _ => false) (evaluated pub s mem (pairParams I m n) id)
      (i.val : Word w) m' j.castSucc) = IndexedStarts.pair (columns t p i.val) (bank first m n i.val) m n := by
  funext j
  rw [affine]
  have hb := bank_val L i
  fin_cases j
  · simp [pairParams,constant,IndexedStarts.pair,Expr.eval]
  · change I.oldStarts.eval pub s mem+_ * I.oldStride.eval pub s mem = Fin.ofNat _ ((t 3).val+i.val*(t 1).val)
    rw [D.oldStarts,D.oldStride]; change _ = (((t 3).val+i.val*(t 1).val : ℕ) : Word w); push_cast; rfl
  · change I.oldWidths.eval pub s mem+_ * I.oldStride.eval pub s mem = Fin.ofNat _ ((t 2).val+i.val*(t 1).val)
    rw [D.oldWidths,D.oldStride]; change _ = (((t 2).val+i.val*(t 1).val : ℕ) : Word w); push_cast; rfl
  · change I.newStarts.eval pub s mem+_ * I.newStride.eval pub s mem = Fin.ofNat _ ((p 4).val+i.val*(p 1).val)
    rw [D.newStarts,D.newStride]; change _ = (((p 4).val+i.val*(p 1).val : ℕ) : Word w); push_cast; rfl
  · change I.newWidths.eval pub s mem+_ * I.newStride.eval pub s mem = Fin.ofNat _ ((p 3).val+i.val*(p 1).val)
    rw [D.newWidths,D.newStride]; change _ = (((p 3).val+i.val*(p 1).val : ℕ) : Word w); push_cast; rfl
  · change I.firstBank.eval pub s mem+((m+n : ℕ) : Word w)+(i.val : Word w)*((capacity m n : ℕ) : Word w) =
      Fin.ofNat _ ((bank (w := w) first m n i.val).val+m+n)
    rw [D.start,hb,bank_add]; congr 1; omega

theorem refs_operands {m n : ℕ} (L : Layout t p rows m n first) (id : ℕ) (i : Fin rows) (m' : Memory w) :
    (fun j : Fin 7 => FlatRows.value (fun _ => false) (evaluated pub s mem (refParams I m n) id)
      (i.val : Word w) m' j.castSucc) = IndexedStarts.adj (bank first m n i.val) m n := by
  funext j
  rw [affine]
  have hb := bank_val L i
  have fieldVal (o : ℕ) : (bankField I m n o).1.eval pub s mem+(i.val : Word w)*(bankField I m n o).2.eval pub s mem =
      Fin.ofNat (2^w) ((bank (w := w) first m n i.val).val+o) := by
    change I.firstBank.eval pub s mem+(o : Word w)+(i.val : Word w)*(capacity m n : Word w) = _
    rw [D.start,bank_add,hb]
  fin_cases j
  · change (n : Word w)+(i.val : Word w)*0 = Fin.ofNat _ n; simp
  · change (m : Word w)+(i.val : Word w)*0 = Fin.ofNat _ m; simp
  · apply (fieldVal (m+n)).trans; congr 1; omega
  · apply (fieldVal 0).trans; exact Fin.ext (Nat.mod_eq_of_lt (bank (w := w) first m n i.val).isLt)
  · apply (fieldVal (m+n+3*(m*n))).trans; congr 1; omega
  · exact fieldVal m
  · apply (fieldVal (m+n+4*(m*n))).trans; congr 1; omega

end CompressorRecords.ShrinkABSliceRecipe

end VPVNP
end Computability
end OAI
