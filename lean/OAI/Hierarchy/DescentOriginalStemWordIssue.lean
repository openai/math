import OAI.Hierarchy.DescentResetNumberStem

namespace OAI
/-! # Reading a published packed stem numeral from the original scheduled writer -/
namespace Hierarchy.DescentResetNumberStem.Layout
open DescentSIMDLookup DescentPackedZip DescentResetOriginalSlots
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing
noncomputable section
variable {X J K H G w : ℕ} (L : Layout X J K)

theorem issued_one (ready : L.Room w) (m : Memory w) (rows : L.rows=H*chunks G L.M)
    (dead : ∀s,L.laws s (fun _=>0)=0)
    (x : Fin X) (j : Fin J) (values : Fin H→Fin G→Fin 6→Cell L.field)
    (issued : ∀t,Source (L.src x j t) (fun h g=>values h g t) L.M m) :
    Source (.lookup (bank L.original L.rows K x.val (L.shelf j).val) .row)
      (fun h g=>L.laws (L.side j) (values h g)) L.M (L.image m) :=by
  let t:=finProdFinEquiv (x,j)
  have sep : L.header+DescentOperandPairBook.words 6 L.field L.M≤L.original:=ready.separate
  have interval:=range L.shelf L.original L.rows t
  have start : L.original≤finish L.original L.rows X K:=Nat.le_add_right ..
  have size : H*chunks G L.M≤L.endAddress:=by
    rw [←rows]
    change _≤finish L.original L.rows X K
    omega
  have tableRoom:=sep.trans_lt (start.trans_lt ready.fits)
  have hit:=DescentOperandPairBook.issued L.laws dead (L.side j) L.header (L.src x j) m values
    (ready.input x j) issued tableRoom
  have termFit : (L.term t).Fits w L.original:=by
    simpa only [t,term,Equiv.symm_apply_apply] using ProtocolRAMGeneratedWrite.fits_mono _ sep hit.1
  let installed:=DescentOperandPairBook.memory L.laws L.M L.header m
  have termRead : Source (L.term t) (fun h g=>L.laws (L.side j) (values h g)) L.M installed:=by
    simpa only [installed,term,t,Equiv.symm_apply_apply] using hit.2
  intro r
  have rowFit:=(row H G L.M r).isLt
  have small:=rowFit.trans (size.trans_lt ready.fits)
  have bankRoom : (row H G L.M r).val<(bank L.original L.rows K x.val (L.shelf j).val).size:=by
    exact (rowFit.trans_le rows.ge).trans_le (rows_le _)
  change L.image m ((bank L.original L.rows K x.val (L.shelf j).val).base+
    ((row H G L.M r).val:Word w).val%(bank L.original L.rows K x.val (L.shelf j).val).size)=_
  rw [Fin.val_cast_of_lt small,Nat.mod_eq_of_lt bankRoom]
  simpa only [image,jobs,rows,bank] using slot_read L.shelf L.original L.term installed x j
    (fun h g=>L.laws (L.side j) (values h g)) termFit termRead r


theorem issued_words (ready : L.Room w) (m : Memory w) (rows : L.rows=H*chunks G L.M)
    (dead : ∀s,L.laws s (fun _=>0)=0)
    (values : Fin X→Fin J→Fin H→Fin G→Fin 6→Cell L.field)
    (issued : ∀x j t,Source (L.src x j t) (fun h g=>values x j h g t) L.M m)
    (x : Fin X) (j : Fin J) :
    Source (.lookup (bank L.original L.rows K x.val (L.shelf j).val) .row)
      (fun h g=>L.laws (L.side j) (values x j h g)) L.M (L.image m) :=L.issued_one ready m rows dead x j (values x j) (issued x j)

end
end Hierarchy.DescentResetNumberStem.Layout

end OAI
