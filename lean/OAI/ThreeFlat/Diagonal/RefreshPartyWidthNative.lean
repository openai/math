import OAI.ThreeFlat.Diagonal.RefreshPartyWidth

namespace OAI
/-! # Widths produced by the installed per-party RAM address expression -/
namespace ThreeFlat.Diagonal.RefreshParty

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.MotifRows
open CompressorPacking.Native RefreshDemandRows RefreshTies
open scoped Fin.CommRing
noncomputable section

variable {W v a t h pad : ℕ} (memory : Memory W) (regs : Fin 7 → Word W)
open private valueAt fitsAt from OAI.ThreeFlat.Diagonal.RefreshPartyBounds

variable {memory regs} {G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t)}
    {C : SlotImage.Columns} {split : ℕ} {w : SlotImage.RefreshInput v a t → ℕ}
    (S : Source memory regs G C split w)

include S in
theorem Source.dense_width_fit (z : Block v t) (block : (memory (regs 2).val).val=blockId z)
    (dir side : Bool) (p j : Fin (mPort a)) (other : F) (fp : (regs 3).val=p.val)
    ( fj : valueAt memory regs other=j.val) (fo : fitsAt memory regs other) (mf : mPort a<2^W) (lf : 2^t<2^W) :
    fitsAt memory regs (denseWidth (mPort a) dir side other) := by
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
  exact fl

include S in
theorem demand_width_native (z : Block v t) (block : (memory (regs 2).val).val=blockId z)
    (p j : Fin (mPort a)) (dir side : Bool) (party : (regs 3).val=p.val)
    (edge : (regs 4).val=((if dir then 2 else 0)+(if side then 1 else 0))*mPort a+j.val)
    (banks : 3*mPort a<2^W) (lf : 2^t<2^W) :
    (closed (width (mPort a) h pad false)).eval Fin.elim0 memory regs =
      (SlotImage.demandWidth w (addr (arrival G (tagOrdinal a).symm) z (denseEnds p (dir,side,j)).1.1):Word W) := by
  let partner := Formula.op .mod (.reg 4 : F) (.lit (mPort a))
  have pr : valueAt memory regs partner=j.val := by
    change (regs 4).val%mPort a=j.val
    rw [edge,Nat.mul_comm _ (mPort a),Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]
  have pf : fitsAt memory regs partner := ⟨trivial,trivial,(regs 4).isLt,(by change mPort a<_; omega)⟩
  have good b side' := S.dense_width_fit z block b side' p j partner party pr pf (by omega) lf
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
  · exact dense_width_read (fun _=>0) (fun i=>(memory i).val) (fun i=>(regs i).val) G _ S.demands z S.remain block p j dir side party edge

include S in
theorem supply_width_native (siteCount : ℕ) (site : (regs 1).val<siteCount) (slot : Fin h) (side : Bool)
    (key : (regs 4).val=(if side then h else 0)+slot.val) (physicalWidth : ℕ)
    (row : (memory (valueAt memory regs (stageField 40)+((regs 1).val*(2*(1+h+pad))+
      (1+(if side then 1+h+pad else 0)+slot.val))*4+2)).val=physicalWidth)
    (span : valueAt memory regs (stageField 40)+siteCount*(2*(1+h+pad))*4≤2^W) (hfit : h<2^W) :
    (closed (width (mPort a) h pad true)).eval Fin.elim0 memory regs = (physicalWidth:Word W) := by
  let D := 1+h+pad
  let digit := Formula.op .mod (.reg 4 : F) (.lit h)
  have val : valueAt memory regs digit=slot.val := by
    change (regs 4).val%h=slot.val
    cases side <;> simp [key,Nat.add_mod_left,Nat.mod_eq_of_lt slot.isLt]
  have df : fitsAt memory regs digit := ⟨trivial,trivial,(regs 4).isLt,hfit⟩
  have field (b : Bool) : fitsAt memory regs (sparseWidth D b digit) := by
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
    exact addr
  apply run memory regs
  · refine ⟨trivial,trivial,(regs 4).isLt,hfit,?_⟩
    split
    · exact field false
    · exact field true
  · exact (sparse_width_read (a:=a) (pad:=pad) (fun _=>0) (fun i=>(memory i).val) (fun i=>(regs i).val) slot side key).trans row


end
end ThreeFlat.Diagonal.RefreshParty

end OAI
