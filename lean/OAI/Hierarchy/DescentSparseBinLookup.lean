import OAI.Hierarchy.DescentSparseBinRAM
import OAI.Hierarchy.DescentFirstColonyRAM

namespace OAI
/-! # Physical header reads and inverse lookups in the bounded bin directory -/

noncomputable section
namespace Hierarchy.DescentPacking.SparseBinRAM
open ProtocolRAM DescentFirstColonyRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
variable {w : ℕ}

/-- A zero head denotes an empty geometric colony. An occupied head is the
one-based original site address, whose exclusive prefix is its true directory
rank. The sentinel lies above every occupied global ordinal. -/
def header (L : Chart) (cell : Expr) (sentinel : ℕ) : Expr :=
  let head := Expr.lookup L.heads cell
  .branch .eq head (.lit 0) (.lit sentinel) (.lookup L.starts (.op .sub head (.lit 1)))

theorem header_empty (L : Chart) (cell : Expr) (sentinel : ℕ) (m : Memory w) (x : Word w)
    (h : L.heads.read m (cell.eval m x)=0) :
    (header L cell sentinel).eval m x=(sentinel:Word w) := by
  simp [header,Expr.eval,h,Comparison.test]

theorem header_hit (L : Chart) (cell : Expr) (sentinel first name : ℕ) (m : Memory w) (x : Word w)
    (head : L.heads.read m (cell.eval m x)=((first+1:ℕ):Word w)) (live : first+1<2^w)
    (span : first<L.starts.size) (start : m (L.starts.base+first)=(name:Word w)) :
    (header L cell sentinel).eval m x=(name:Word w) := by
  have nonzero : ((first+1:ℕ):Word w)≠0 := by
    intro eqn
    have val := congrArg Fin.val eqn
    rw [Fin.val_cast_of_lt live] at val
    simp at val
  have sub : (((first+1:ℕ):Word w)-1)=(first:Word w) := by push_cast; ring
  have found : L.starts.read m (first : Word w) = (name : Word w) := by
    simpa only [Bank.read, Fin.val_cast_of_lt (by omega : first < 2^w), Nat.mod_eq_of_lt span] using start
  simpa only [header, Expr.eval, Comparison.test, beq_iff_eq, head, Nat.cast_zero, Nat.cast_one,
    ite_eq_right nonzero, RowOp.opcode, BinaryOp.eval, sub] using found

theorem header_fits (L : Chart) (cell : Expr) (sentinel cut : ℕ)
    (h : L.heads.Fits w cut) (s : L.starts.Fits w cut) (c : cell.Fits w cut) :
    (header L cell sentinel).Fits w cut := ⟨⟨h,c⟩,trivial,trivial,⟨s,⟨⟨h,c⟩,trivial⟩⟩⟩

theorem header_work (L : Chart) (cell : Expr) (sentinel : ℕ) :
    (header L cell sentinel).work=2*cell.work+20 := by simp [header,Expr.work];omega

/-- Compute the global bank offset for a public stride without a binary
multiplication opcode. The expression reads only the current original edge. -/
def scale (stride : ℕ) (x : Expr) : Expr :=
  match stride with
  | 0 => .lit 0
  | n+1 => .op .add (scale n x) x

theorem scale_eval (stride : ℕ) (x : Expr) (m : Memory w) (r : Word w) :
    (scale stride x).eval m r=(stride:Word w)*(x.eval m r) := by
  induction stride with
  | zero => simp [scale,Expr.eval]
  | succ n ih => simp [scale,Expr.eval,RowOp.opcode,BinaryOp.eval,ih,add_mul]

theorem scale_fits (stride : ℕ) (x : Expr) {out : ℕ} (h : x.Fits w out) :
    (scale stride x).Fits w out := by
  induction stride with
  | zero => trivial
  | succ n ih => exact ⟨ih,h⟩

theorem scale_work (stride : ℕ) (x : Expr) : (scale stride x).work=1+stride*(x.work+1) := by
  induction stride with
  | zero => simp only [scale, Expr.work, Nat.zero_mul, Nat.add_zero]
  | succ n ih => simp [scale,Expr.work,ih,Nat.succ_mul];omega

private def search (tags : Bank) (base target : Expr) (missing : ℕ) : List ℕ→Expr
  | []=>.lit missing
  | j::js=>.branch .eq (.lookup tags (.op .add base (.lit j))) target (.lit j) (search tags base target missing js)

def localTarget (slots : ℕ) (tags : Bank) (base target : Expr) :=
  search tags base target slots (List.range slots)

theorem localTarget_eval (slots : ℕ) (tags : Bank) (base target : Expr) (m : Memory w) (r : Word w)
    (off wanted : ℕ) (keys : ℕ→ℕ) (baseRead : base.eval m r=(off:Word w)) (targetRead : (target.eval m r).val=wanted)
    (fit : off+slots≤tags.size) (word : tags.size<2^w)
    (input : ∀i<slots,(m (tags.base+off+i)).val=keys i) :
    (localTarget slots tags base target).eval m r=
      (((List.range slots).find? (fun j=>decide (keys j=wanted))).getD slots:Word w) := by
  have go (xs : List ℕ) (inside : ∀j∈xs,j<slots) : (search tags base target slots xs).eval m r =
      ((xs.find? fun j=>decide (keys j=wanted)).getD slots:Word w) := by
    induction xs with
    | nil => rfl
    | cons j js ih =>
      have hj := inside j List.mem_cons_self
      have lo : off+j<tags.size := by omega
      have tap : (tags.read m (base.eval m r+(j:Word w))).val=keys j := by
        simpa [baseRead,←Nat.cast_add,Bank.read,Fin.val_cast_of_lt (lo.trans word),Nat.mod_eq_of_lt lo,Nat.add_assoc] using input j hj
      have tail := ih (fun i hi=>inside i (List.mem_cons_of_mem _ hi))
      simp only [search,Expr.eval,RowOp.opcode,BinaryOp.eval,Comparison.test,beq_iff_eq,List.find?_cons]
      change (if tags.read m (base.eval m r+(j:Word w))=target.eval m r then _ else _) = _
      by_cases eqn : keys j=wanted
      · have agree := Fin.ext (tap.trans (eqn.trans targetRead.symm))
        simp [agree,eqn]
      · have different : tags.read m (base.eval m r+(j:Word w))≠target.eval m r :=
          fun same=>eqn (tap.symm.trans ((congrArg Fin.val same).trans targetRead))
        simp [different,eqn,tail]
  exact go _ (fun _ h=>List.mem_range.mp h)

theorem localTarget_fits (slots : ℕ) (tags : Bank) (base target : Expr) {out : ℕ}
    (a : tags.Fits w out) (b : base.Fits w out) (c : target.Fits w out) :
    (localTarget slots tags base target).Fits w out := by
  unfold localTarget
  induction List.range slots with
  | nil => trivial
  | cons j js ih => exact ⟨⟨a,b,trivial⟩,c,trivial,ih⟩

theorem localTarget_work (slots : ℕ) (tags : Bank) (base target : Expr) :
    (localTarget slots tags base target).work=1+slots*(base.work+target.work+9) := by
  have go (xs : List ℕ) : (search tags base target slots xs).work=1+xs.length*(base.work+target.work+9) := by
    induction xs with
    | nil => simp only [search, Expr.work, List.length_nil, Nat.zero_mul, Nat.add_zero]
    | cons j js ih => simp [search,Expr.work,ih,Nat.succ_mul];omega
  simpa [localTarget] using go (List.range slots)

end Hierarchy.DescentPacking.SparseBinRAM

end
end OAI
