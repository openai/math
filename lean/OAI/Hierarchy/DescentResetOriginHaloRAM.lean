import OAI.Hierarchy.DescentClosedPeerTable
import OAI.Hierarchy.DescentPeerRankFits
import OAI.Hierarchy.ProtocolRAMHistogram
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Measuring every old source's compact position in the receiver's closed halo -/
namespace Hierarchy.DescentResetOriginHaloRAM
open DescentPackedColony DescentPackedZip DescentSortedRoster
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {H D w : ℕ}

def opened (roster : Bank) (j : Fin D) : Expr :=
  .lookup roster (.op .add (scale D .row) (.lit j.val))

def columns (roster : Bank) : Fin (D+1)→Expr := Fin.lastCases .row (opened roster)

def asked (H : ℕ) (x : Expr) : Expr:=.branch .lt x (.lit H) x .row

def op (H : ℕ) (roster : Bank) (j : Fin (D+1)) : Expr :=
  calculate (columns (D := D) roster) (asked H (columns roster j))

theorem present_closed (p : Fin H→Fin D→Option (Fin H)) (v : Fin H) :
    present (closed p) v=insert v (present p v):=by
  ext x
  simp only [present,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨j,hit⟩
    induction j using Fin.lastCases with
    | last=>exact Or.inl (Option.some.inj (by simpa only [closed,Fin.lastCases_last] using hit)).symm
    | cast j=>exact Or.inr ⟨j,by simpa only [closed,Fin.lastCases_castSucc] using hit⟩
  · rintro (rfl|⟨j,hit⟩)
    · exact ⟨Fin.last _,by simp [closed]⟩
    · exact ⟨j.castSucc,by simpa only [closed,Fin.lastCases_castSucc] using hit⟩

theorem op_fits (roster : Bank) (j : Fin (D+1)) (out : ℕ) (fit : roster.Fits w out) :
    (op H roster j).Fits w out:=by
  have scaled (n : ℕ) : (scale n .row).Fits w out:=by
    induction n with
    | zero=>trivial
    | succ n ih=>exact ⟨trivial,ih⟩
  have bank (i : Fin D) : (opened roster i).Fits w out:=⟨fit,scaled D,trivial⟩
  have cols (i : Fin (D+1)) : (columns roster i).Fits w out:=by
    induction i using Fin.lastCases with
    | last=>simp only [columns,Fin.lastCases_last]; exact trivial
    | cast i=>simpa only [columns,Fin.lastCases_castSucc] using bank i
  have query : (asked H (columns roster j)).Fits w out := ⟨cols j,trivial,cols j,trivial⟩
  exact DescentResetSourceClassRAM.rank_fits (columns (D := D) roster) _ cols query

theorem op_eval (roster : Bank) (p : Fin H→Fin D→Option (Fin H)) (j : Fin (D+1)) (out : ℕ) (m : Memory w)
    (fit : roster.Fits w out) (extent : H*D≤roster.size)
    (original : ∀v i,m (roster.base+(v.val*D+i.val))=(target (p v i):Word w))
    (high : H<2^w) (_degree : D+1<2^w) (v : Fin H) :
    (op H roster j).eval m (v.val:Word w)=(before (closed p) v ((closed p v j).getD v):Word w):=by
  have read (v : Fin H) (i : Fin (D+1)) : (columns roster i).eval m (v.val:Word w)=(target (closed p v i):Word w):=by
    induction i using Fin.lastCases with
    | last=>simp only [columns,closed,Fin.lastCases_last]; rfl
    | cast i=>
      simp only [columns,closed,Fin.lastCases_castSucc]
      change roster.read m ((scale D .row).eval m (v.val:Word w)+(i.val:Word w))=(target (p v i):Word w)
      rw [eval_scale]
      change roster.read m ((D:Word w)*(v.val:Word w)+(i.val:Word w))=_
      have below : v.val*D+i.val<H*D:=(Nat.add_lt_add_left i.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
      rw [mul_comm (D:Word w),←Nat.cast_mul,←Nat.cast_add,bank_read _ _ (below.trans_le extent) fit]
      exact original v i
  apply rank_read (closed p) m (v.val:Word w) (columns (D := D) roster) v high (read v)
    (asked H (columns roster j)) ((closed p v j).getD v)
  simp only [asked,Expr.eval,read v j,Comparison.test]
  cases closed p v j with
  | none=>simp [target,Nat.mod_eq_of_lt (v.isLt.trans high)]
  | some a=>
    have below : (a.val:Word w)<(H:Word w) := by
      rw [Fin.lt_def,Fin.val_cast_of_lt (a.isLt.trans high),Fin.val_cast_of_lt high]
      exact a.isLt
    simp [target,below,Fin.val_cast_of_lt (a.isLt.trans high)]

theorem run (roster : Bank) (p : Fin H→Fin D→Option (Fin H)) (j : Fin (D+1)) (out : ℕ) (m : Memory w)
    (fit : roster.Fits w out) (extent : H*D≤roster.size)
    (original : ∀v i,m (roster.base+(v.val*D+i.val))=(target (p v i):Word w))
    (high : H<2^w) (degree : D+1<2^w) (output : out+H<2^w) :
    let e:=op H roster j
    let final:=image out H e m
    (scan w out H e).Exec m final (4+H*(2*e.work+4)) ∧
    (∀v : Fin H,final (out+v.val)=(before (closed p) v ((closed p v j).getD v):Word w)) ∧
    (∀a,a<out ∨ out+H≤a→final a=m a) ∧ DescentStaticWordColumn.names (scan w out H e)=11+4*e.work ∧ CheapCode (scan w out H e):=by
  intro e final
  refine ⟨scan_exec _ _ _ _ (op_fits roster j out fit) output,?_,fun a safe=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a safe,
    DescentStaticWordColumn.names_scan ..,@scan_cheap _ _ _ _⟩
  intro v
  apply (ProtocolRAMGeneratedWrite.read_image out H e m v).trans
  exact op_eval roster p j out m fit extent original high degree v

end
end Hierarchy.DescentResetOriginHaloRAM

end OAI
