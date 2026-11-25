import OAI.ThreeFlat.Diagonal.RefreshPartyBounds
import OAI.ThreeFlat.Diagonal.RefreshPartyLookup
import OAI.ThreeFlat.RAM.HeaderScanProcedure

namespace OAI
/-! # Native execution of the fixed refresh-party pin descriptor -/

namespace ThreeFlat.Diagonal.RefreshParty

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.MotifRows
open CompressorPacking.Native RefreshDemandRows RefreshTies
open scoped Fin.CommRing
noncomputable section

variable {W v a t h pad : ℕ} (memory : Memory W) (regs : Fin 7 → Word W)
open private valueAt fitsAt from OAI.ThreeFlat.Diagonal.RefreshPartyBounds

theorem run (f : F) (fit : fitsAt memory regs f) {n : ℕ} (value : valueAt memory regs f=n) :
    (closed f).eval Fin.elim0 memory regs=(n:Word W) := by
  rw [eval_closed]
  simpa only [Nat.cast_zero,Fin.cast_val_eq_self,value] using Formula.value_eq_natural f (fun _=>0) (fun i=>(memory i).val) (fun i=>(regs i).val) fit

private theorem member_fit (l : Location F) (bound : 2<2^W)
    (f : fitsAt memory regs l.scope ∧ fitsAt memory regs l.child ∧ fitsAt memory regs l.half ∧ fitsAt memory regs l.bit) : fitsAt memory regs (member l) := by
  have b := (regs 6).isLt
  refine ⟨trivial,trivial,b,Nat.two_pow_pos _,?_⟩
  split
  · exact f.1
  · refine ⟨trivial,trivial,b,(by change 1<2^W; omega),?_⟩
    split
    · exact f.2.1
    · refine ⟨trivial,trivial,b,bound,?_⟩
      split <;> first | exact f.2.2.1 | exact f.2.2.2

variable {memory regs} {G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t)}
    {C : SlotImage.Columns} {split : ℕ} {w : SlotImage.RefreshInput v a t → ℕ}
    (S : Source memory regs G C split w)

include S in
theorem Source.dense_member (z : Block v t) (block : (memory (regs 2).val).val=blockId z)
    (dir side : Bool) (p j : Fin (mPort a)) (other : F) (fp : (regs 3).val=p.val)
    ( fj : valueAt memory regs other=j.val) (fo : fitsAt memory regs other) (mf : mPort a<2^W) (lf : 2^t<2^W) (degree : ℕ) :
    fitsAt memory regs (member (denseLoc (mPort a) degree dir side other)) := by
  let i := if side then j else p
  let s := if side then p else j
  let ix : F := if side then other else .reg 3
  let sl : F := if side then .reg 3 else other
  have pi : valueAt memory regs ix=i.val := by cases side <;> assumption
  have ps : valueAt memory regs sl=s.val := by cases side <;> assumption
  have ti : fitsAt memory regs ix := by cases side <;> first | exact fo | trivial
  have ts : fitsAt memory regs sl := by cases side <;> first | exact fo | trivial
  let row := coordinates (mPort a) inputs (stageField 8) (.load (.reg 2)) dir ix sl
  have bounds := S.address_and_prefix z block dir ix sl i s ti ts pi ps mf lf
  have fl : fitsAt memory regs (.load row) := ⟨bounds.1,bounds.2.1⟩
  apply member_fit _ _ _ (by have := S.header; omega)
  refine ⟨⟨trivial,fl,(regs 5).isLt,(memory _).isLt,?_⟩,trivial,?_,?_⟩
  · split <;> split <;> trivial
  · cases side <;> first | trivial
  · cases side <;> first | trivial | exact ⟨bounds.2.2,trivial,trivial⟩

include S in
theorem demand_native (z : Block v t) (block : (memory (regs 2).val).val=blockId z)
    (p j : Fin (mPort a)) (dir side : Bool) (party : (regs 3).val=p.val)
    (edge : (regs 4).val=((if dir then 2 else 0)+(if side then 1 else 0))*mPort a+j.val)
    (banks : 3*mPort a<2^W) (lf : 2^t<2^W) :
    (closed (lookup (mPort a) h pad false)).eval Fin.elim0 memory regs =
      (component (demandLocation (h:=h) (pad:=pad) (arrival G (tagOrdinal a).symm)
        (SlotImage.demandWidth w) z p (denseEnds p (dir,side,j)) (regs 5).val) (regs 6).val:Word W) := by
  let partner := Formula.op .mod (.reg 4 : F) (.lit (mPort a))
  have pr : valueAt memory regs partner=j.val := by
    change (regs 4).val%mPort a=j.val
    rw [edge,Nat.mul_comm _ (mPort a),Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]
  have pf : fitsAt memory regs partner := ⟨trivial,trivial,(regs 4).isLt,(by change mPort a<_; omega)⟩
  have good b side' := S.dense_member z block b side' p j partner party pr pf (by omega) lf (1+h+pad)
  apply run memory regs
  · refine ⟨trivial,trivial,(regs 4).isLt,(by change mPort a<_; omega),?_⟩
    split
    · exact good false false
    · refine ⟨trivial,trivial,(regs 4).isLt,(by change 2*mPort a<_; omega),?_⟩
      split
      · exact good false true
      · refine ⟨trivial,trivial,(regs 4).isLt,banks,?_⟩
        split
        · exact good true false
        · exact good true true
  · exact demand_lookup (fun _=>0) (fun i=>(memory i).val) (fun i=>(regs i).val) G _ S.demands z S.remain block p j dir side party edge

include S in
theorem supply_native (siteCount : ℕ) (site : (regs 1).val<siteCount) (slot : Fin h) (side : Bool)
    (key : (regs 4).val=(if side then h else 0)+slot.val) (physicalWidth : ℕ)
    (row : (memory (valueAt memory regs (stageField 40)+((regs 1).val*(2*(1+h+pad))+
      (1+(if side then 1+h+pad else 0)+slot.val))*4+2)).val=physicalWidth)
    (span : valueAt memory regs (stageField 40)+siteCount*(2*(1+h+pad))*4≤2^W) (hfit : h<2^W) :
    (closed (lookup (mPort a) h pad true)).eval Fin.elim0 memory regs = (component
      ⟨if (regs 5).val<physicalWidth then 2 else 0,0,1+(if side then 1+h+pad else 0)+slot.val,(regs 5).val⟩
      (regs 6).val:Word W) := by
  let D := 1+h+pad
  let digit := Formula.op .mod (.reg 4 : F) (.lit h)
  have val : valueAt memory regs digit=slot.val := by
    change (regs 4).val%h=slot.val
    cases side <;> simp [key,Nat.add_mod_left,Nat.mod_eq_of_lt slot.isLt]
  have df : fitsAt memory regs digit := ⟨trivial,trivial,(regs 4).isLt,hfit⟩
  have field (b : Bool) : fitsAt memory regs (member (sparseLoc D b digit)) := by
    let half := plus (.lit (1+(if b then D else 0))) digit
    let flat := plus (.op .mul (.reg 1) (.lit (2*D))) half
    let word := readColumn (stageField 40) (plus (.op .mul flat (.lit 4)) (.lit 2))
    have hhalf : fitsAt memory regs half := ⟨trivial,df,trivial⟩
    have far : fitsAt memory regs flat := ⟨⟨trivial,trivial,trivial⟩,hhalf,trivial⟩
    have hi : valueAt memory regs half < 2*D := by
      change 1+(if b then D else 0)+valueAt memory regs digit<_
      have := slot.isLt
      cases b <;> dsimp [D] at * <;> omega
    have cap := Nat.mul_le_mul_right (2*D) site
    rw [Nat.succ_mul] at cap
    have addr : fitsAt memory regs word := by
      refine ⟨⟨S.field 40 (by decide),⟨⟨far,trivial,trivial⟩,trivial,trivial⟩,trivial⟩,?_⟩
      change valueAt memory regs (stageField 40)+(((regs 1).val*(2*D)+valueAt memory regs half)*4+2)<_
      change valueAt memory regs (stageField 40)+siteCount*(2*D)*4≤2^W at span
      omega
    apply member_fit _ _ _ (by have := S.header; omega)
    refine ⟨⟨trivial,addr,(regs 5).isLt,(memory _).isLt,?_⟩,trivial,hhalf,trivial⟩
    split <;> split <;> trivial
  apply run memory regs
  · refine ⟨trivial,trivial,(regs 4).isLt,hfit,?_⟩
    split
    · exact field false
    · exact field true
  · exact supply_lookup (a:=a) (pad:=pad) (fun _=>0) (fun i=>(memory i).val) (fun i=>(regs i).val) D slot side physicalWidth key row rfl


end
end ThreeFlat.Diagonal.RefreshParty

end OAI
