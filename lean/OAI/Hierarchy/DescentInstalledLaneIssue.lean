import OAI.Hierarchy.DescentResetPointerFields
import OAI.Hierarchy.DescentBundleBank
import OAI.Hierarchy.DescentResetLaneScan

namespace OAI
/-! # Actual installed gate reads from the issued block pointers and residual digit fields -/

namespace Hierarchy.DescentInstalledLaneIssue
open DescentKernelHistory DescentBundleHistory DescentLaneGates DescentOrderedWords
open DescentResetPointerFields DescentNamedContact DescentRouterBank DescentResetAttachments Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {n d L p Y : ℕ} {P H Q F : Type} [Fintype H] [Fintype Q] {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
variable (hp : 0<p) (whole : ∀e,p∣N.width e) (v : R.Site)
local notation "M" => DescentResetTrunks.network N home group R
variable (units : Boundary R v→ℕ) (multiple : ∀a,boundaryWidth R v a=units a*p)
variable (prg : Program Y p (boundaryWidth R v)) (node : prg.Node) (j : Fin (prg.op node).arity)

/-- Each physical request is a start-block ordinal plus a small candidate number. -/
def sourceBlock {B : Type} {width : B→ℕ} {p : ℕ} (units : B→ℕ) (multiple : ∀a,width a=units a*p)
    (hp : 0<p) (l : Lane p width) (i : Fin (l.count units)) : BlockRef p width where
  port := l.port
  block := l.bundleStart+i.val
  fits := by
    rw [multiple]
    exact Nat.mul_le_mul_right p (l.block units multiple hp i).isLt

def installedBlock (i : Fin (((prg.op node).arg j).count units)) : BlockRef p (boundaryWidth (M) (.inr v)) :=
  bankField hp N home group R key whole v (sourceBlock units multiple hp ((prg.op node).arg j) i)

omit [Fintype Q] in
theorem installed_digit (i : Fin (((prg.op node).arg j).count units)) (digit : Fin p) :
    (installedBlock N home group R key hp whole v units multiple prg node j i).atBit digit=
      trunkBankBit N home group R key v (((prg.op node).arg j).blockBit units multiple hp i digit) :=
  bank_read hp N home group R key whole v _ digit

omit [Fintype Q] in
theorem assigned_digit (a : (M).Assignment) (ext : Ports bits) (i : Fin (((prg.op node).arg j).count units)) (digit : Fin p) :
    let b:=(installedBlock N home group R key hp whole v units multiple prg node j i).atBit digit
    let src:=((prg.op node).arg j).blockBit units multiple hp i digit
    boundaryRead (M) a ext (.inr v) b.1 b.2=
      boundaryRead R (DescentResetTrunks.Ordered.decode N home group R key a).2.2
        (DescentResetTrunks.Ordered.public N group key (DescentResetTrunks.Ordered.decode N home group R key a).1)
        v src.1 src.2 := by
  let read : BitRef (boundaryWidth (M) (.inr v)) → Bool :=
    fun b => boundaryRead (M) a ext (.inr v) b.1 b.2
  exact (congrArg read (installed_digit N home group R key hp whole v units multiple prg node j i digit)).trans
    (trunkBankBit_read N home group R key a ext v _)

/-- Decode the whole operand with one call to the installed assignment per covered block.
The residual digit and stride are shared by all p positions of that operand. -/
def operand (a : (M).Assignment) (ext : Ports bits) : Word p :=
  ((prg.op node).arg j).reconstruct units multiple hp fun i digit=>
    let b:=(installedBlock N home group R key hp whole v units multiple prg node j i).atBit digit
    boundaryRead (M) a ext (.inr v) b.1 b.2

omit [Fintype Q] in
theorem operand_read (a : (M).Assignment) (ext : Ports bits) :
    operand N home group R key hp whole v units multiple prg node j a ext=
      ((prg.op node).arg j).word (fun z=>boundaryRead R (DescentResetTrunks.Ordered.decode N home group R key a).2.2
        (DescentResetTrunks.Ordered.public N group key (DescentResetTrunks.Ordered.decode N home group R key a).1) v z.1 z.2) := by
  let read : BitRef (boundaryWidth R v) → Bool := fun z =>
    boundaryRead R (DescentResetTrunks.Ordered.decode N home group R key a).2.2
      (DescentResetTrunks.Ordered.public N group key (DescentResetTrunks.Ordered.decode N home group R key a).1)
      v z.1 z.2
  refine Eq.trans ?_ (((prg.op node).arg j).reconstruct_read units multiple hp read)
  apply congrArg (((prg.op node).arg j).reconstruct units multiple hp)
  funext i digit
  exact assigned_digit N home group R key hp whole v units multiple prg node j a ext i digit

omit [Fintype Q] in
theorem op_read (a : (M).Assignment) (ext : Ports bits) (scalar : DescentResetGates.CanonicalTag Y→List (List Bool)→F) :
    scalar (prg.op node).tag (List.ofFn fun i=>wordList (operand N home group R key hp whole v units multiple prg node i a ext))=
      (prg.op node).value scalar (fun z=>boundaryRead R (DescentResetTrunks.Ordered.decode N home group R key a).2.2
        (DescentResetTrunks.Ordered.public N group key (DescentResetTrunks.Ordered.decode N home group R key a).1) v z.1 z.2) := by
  simp only [operand_read,Op.value]

omit [Fintype Q] in
/-- The same pointers absorb every genuine old payload born before this reset. -/
theorem old_assigned (a : (M).Assignment) (ext : Ports bits) (u : N.Site) (b : BlockRef p (boundaryWidth N u)) (digit : Fin p) :
    let o:=(oldField hp N home group R key whole u b).atBit digit
    let z:=b.atBit digit
    boundaryRead (M) a ext (.inl (false,home u)) o.1 o.2=
      boundaryRead N (oldRows N (DescentResetTrunks.Ordered.original N home group R key a) u) ext u z.1 z.2 := by
  dsimp only
  rw [old_read]
  exact trunkOldBit_read N home group R key a ext u _

end
end Hierarchy.DescentInstalledLaneIssue

end OAI
