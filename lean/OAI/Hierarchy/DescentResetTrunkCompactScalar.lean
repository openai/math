import OAI.Hierarchy.DescentResetTrunkPhases

namespace OAI
/-! # Measure the trunk descriptor in the actual compact actor order -/
namespace Hierarchy.DescentResetTrunkCompactScalar
open DescentSixParty.Chronology DescentSIMDLookup DescentDyadicSpan DescentPackedZip DescentPackedColony
open DescentResetFieldAssembler ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w H N used b : ℕ}

def tested (number inverse : Bank) (scalar : Expr):Expr:=
  .branch .lt .row (.lookup number (.lit 0)) (scalar.atRow (.lookup inverse .row)) (.lit 0)

def phase (w H base : ℕ) (number inverse : Bank) (scalar : Expr):NativePhase w:=
  let e:=tested number inverse scalar
  ⟨scan w base H e,4+H*(2*e.work+4),ProtocolRAM.image base H e,@scan_cheap _ _ _ _⟩

theorem operand_fits (number inverse : Bank) (scalar : Expr) {base : ℕ}
    (now : number.Fits w base) (replace : inverse.Fits w base) (ready : scalar.Fits w base):
    (tested number inverse scalar).Fits w base:=by
  have sub (x : Expr) (f : x.Fits w base) : (x.atRow (.lookup inverse .row)).Fits w base:=by
    induction x <;> simp_all only [Expr.Fits,Expr.atRow] <;> tauto
  exact ⟨trivial, ⟨now, trivial⟩, sub _ ready, trivial⟩

theorem cost (number inverse : Bank) (scalar : Expr) : (tested number inverse scalar).work≤8*scalar.work+10:=by
  have sub (x j : Expr) : (x.atRow j).work≤x.work*(j.work+1):=by
    induction x <;> simp only [Expr.atRow,Expr.work,Nat.add_mul,Nat.one_mul] at * <;> omega
  have q:= sub scalar (.lookup inverse .row)
  change _≤ scalar.work*8 at q
  change 2+6+_+1+1≤_
  omega

theorem any (H base : ℕ) (number inverse : Bank) (scalar : Expr) (m : Memory w)
    (now : number.Fits w base) (replace : inverse.Fits w base) (ready : scalar.Fits w base) (word : base+H<2^w) :
    let p:=phase w H base number inverse scalar
    p.Runs m ∧ (∀a,a<base ∨ base+H≤a→p.image m a=m a) ∧
      DescentStaticWordColumn.names p.program≤11+4*(8*scalar.work+10) ∧
      p.ticks≤4+H*(2*(8*scalar.work+10)+4):=by
  intro p
  have small:=cost number inverse scalar
  refine ⟨scan_exec _ _ _ _ (operand_fits _ _ _ now replace ready) word,
    ProtocolRAMGeneratedWrite.frame_image base H (tested number inverse scalar) m, ?_, ?_⟩
  · rw [show DescentStaticWordColumn.names p.program=11+4*(tested number inverse scalar).work from
      DescentStaticWordColumn.names_scan ..];omega
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left H (Nat.add_le_add_right (Nat.mul_le_mul_left 2 small) 4)) 4

def value (here : Fin used→Fin N) (shape : Fin N→Meta) (r : Fin H):Meta:=
  if live : r.val<used then shape (here ⟨_,live⟩) else .blank

/-- Only the selected part of the actual inverse table is read. A vacant
compact address writes the literal seven-zero word, whatever its old contents. -/
theorem words (base : ℕ) (number inverse : Bank) (scalar : Expr) (m : Memory w)
    (now : number.Fits w base) (replace : inverse.Fits w base) (n : used≤ inverse.size)
    (cap : used≤H) (room : base+H<2^w) (counted : m number.base=(used:Word w))
    (here : Fin used→Fin N) (shape : Fin N→Meta)
    (names : ∀r : Fin used,m (inverse.base+r.val)=((here r).val:Word w))
    (actual : ∀r : Fin N,scalar.eval m (r.val:Word w)=((raw b (shape r)).val:Word w))
    (i : Fin H) :
    (phase w H base number inverse scalar).image m (base+i.val)=((raw b (value here shape i)).val:Word w):=by
  rw [show (phase w H base number inverse scalar).image m (base+i.val)=(tested number inverse scalar).eval m (i.val:Word w)
    from ProtocolRAMGeneratedWrite.read_image _ _ _ _ i]
  have Hw : H<2^w:=(Nat.le_add_left ..).trans_lt room
  have same : (i.val:Word w)<(used:Word w) ↔ i.val<used:=by
    change ((i.val:Word w).val<(used:Word w).val) ↔ _
    rw [Fin.val_cast_of_lt (i.isLt.trans Hw),Fin.val_cast_of_lt (cap.trans_lt Hw)]
  have cnt : number.read m (0:Word w)=(used:Word w):=by
    simpa using (bank_read number m now.1 now).trans (show m (number.base+0)=(used:Word w) by simpa using counted)
  by_cases yes : i.val<used
  · let j : Fin used:=⟨i.val,yes⟩
    have inv : inverse.read m (i.val:Word w)=((here j).val:Word w):=(bank_read _ _ (yes.trans_le n) replace).trans (names j)
    simpa [tested,Expr.eval,cnt,Comparison.test,(same.mpr yes),eval_atRow,inv,value,yes] using actual (here j)
  · simp [tested,Expr.eval,cnt,Comparison.test,mt same.mp yes,value,yes,DescentResetTrunkIssue.zero_raw]

end
end Hierarchy.DescentResetTrunkCompactScalar

end OAI
