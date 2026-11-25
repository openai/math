import OAI.Hierarchy.DescentTerminalSiteShelves
import OAI.Hierarchy.DescentTerminalShelfControl
import OAI.Hierarchy.DescentTerminalDenseWindow
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # Two true packed source words and one immutable selector table per paid row -/
namespace Hierarchy.DescentTerminalSiteShelves
open DescentKernelHistory (Recipe)
open DescentTerminalRowBooks DescentTerminalRecipeRows DescentTerminalScalarHeader
open DescentTerminalChronologicalBooks DescentTerminalBinPack DescentTerminalDenseWindow
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w V B W : ℕ}
local notation "Hcode" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)
local notation "C" => Control q t H N A w V

/-- The count in the stream directory permits unpadded variable-length site books.
Both clipped source words may simultaneously contain bits of several neighbors. -/
def window (skip : Fin B) (live : Fin (B+1)) (lo hi : Word B) : Word B :=
  (wordBits _).symm fun j=>if j.val<live.val then two lo hi (skip.val+j.val) else false

theorem window_read (bp : 0<B) (start : ℕ) (live : Fin (B+1)) (z : Word B) (stream : ℕ→Bool)
    (size : z.val<2^live.val) (source : ∀i : Fin live.val,stream (start+i.val)=z.val.testBit i.val) :
    window ⟨start%B,Nat.mod_lt _ bp⟩ live (dense B stream (start/B)) (dense B stream (start/B+1))=z := by
  apply (wordBits _).injective
  funext j
  rw [window,Equiv.apply_symm_apply]
  by_cases h : j.val<live.val
  · have off:=Nat.mod_lt start bp
    have col := j.isLt
    rw [ite_eq_left h,two_dense _ _ _ (by dsimp;omega),←Nat.add_assoc,Nat.div_add_mod']
    exact (source ⟨j.val,h⟩).trans (Computability.VPVNP.LiveHeader.testBit_wordBits z j)
  · rw [ite_eq_right h,←Computability.VPVNP.LiveHeader.testBit_wordBits]
    exact (Nat.testBit_lt_two_pow (size.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt h)))).symm

def mode (site : Site) (r : Fin (site.rows q)) (fit : site.rows q≤W) : Fin (W+1) :=
  if h : r.val<site.portRows q then 0 else ⟨r.val-site.portRows q+1,by have:=r.isLt;omega⟩

def selectMode (z : Hcode) (qp : 0<q) (which : Fin (W+1)) : Option C :=
  if which.val=0 then none else DescentTerminalChronologicalIssue.present (selectRow z qp 0 (which.val-1))

theorem selected_mode (site : Site) (qp : 0<q) (recipes : ∀v : Fin site.nodes,Recipe (Fin t) (Fin (site.arity v)))
    (birth : Birth recipes) (hH : ∀v,Fintype.card (recipes v).Hidden≤H) (hN : ∀v,Fintype.card (recipes v).Node≤N)
    (hA : ∀v j,(recipes v).arity j≤A) (hw : ∀v j,(recipes v).width j≤w)
    (sitesFit : site.nodes≤V) (short : ∀v,site.arity v≤q) (fit : site.rows q≤W) (r : Fin (site.rows q)) :
    selectMode (actual site recipes birth hH hN hA hw sitesFit short) qp (mode site r fit)=
      DescentTerminalChronologicalIssue.present (DescentTerminalChronologicalBooks.control qp recipes birth hH hN hA hw sitesFit r) := by
  let data:=actual site recipes birth hH hN hA hw sitesFit short
  have equal:=selected site qp recipes birth hH hN hA hw sitesFit short r
  rw [load_store] at equal
  rw [←equal]
  by_cases port : r.val<site.portRows q
  · have noRows : (selectRow (actual site recipes birth hH hN hA hw sitesFit short)
        qp (site.portRows q) r.val).1.val = 0 := by
      dsimp only [selectRow,actual,DescentTerminalChronologicalBooks.select]
      let owns (v : Fin site.nodes) := site.portRows q + place site.arity qp v = r.val
      have empty : IsEmpty {v : Fin site.nodes // owns v} :=
        ⟨fun v => by have owned := v.property; dsimp only [owns] at owned; omega⟩
      let owners := @Subtype.fintype (Fin site.nodes) owns
        (fun i => Classical.propDecidable (owns i)) (Fin.fintype site.nodes)
      exact @Fintype.card_eq_zero _ owners empty
    rw [mode,dite_eq_left port]
    simp [selectMode,DescentTerminalChronologicalIssue.present,noRows]
  · simp only [mode,dite_eq_right port,Fin.val_mk,selectMode,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel]
    congr 1
    unfold selectRow
    dsimp only [actual]
    have both : (fun v : Fin site.nodes=>0+place site.arity qp v=r.val-site.portRows q)=
        (fun v=>site.portRows q+place site.arity qp v=r.val) := by
      funext v;apply propext;omega
    rw [both]

/-- A gate for a site knows only its local output-row mode, two clipped words, and the
offset/length of the true chronological site-book code. Mode zero always has zero weight. -/
def slots (B W : ℕ) := (W+1)*((B+1)*(B*((2^B)*(2^B))))
def address (which : Fin (W+1)) (size : Fin (B+1)) (skip : Fin B) (lo hi : Word B) : Fin (slots B W) :=
  finProdFinEquiv (which,finProdFinEquiv (size,finProdFinEquiv (skip,finProdFinEquiv (lo,hi))))

def weight (qp : 0<q) (i : Fin (slots B W)) : ℕ :=
  let x:=finProdFinEquiv.symm i
  let y:=finProdFinEquiv.symm x.2
  let k:=finProdFinEquiv.symm y.2
  let z:=finProdFinEquiv.symm k.2
  let clipped:=window k.1 y.1 z.1 z.2
  if h : clipped.val<range q t H N A w V then
    DescentTerminalLeafFold.code (selectMode (load ⟨clipped.val,h⟩) qp x.1 : Option C)
  else 0

theorem weight_read (qp : 0<q) (bp : 0<B) (start : ℕ) (size : Fin (B+1)) (z : Hcode) (which : Fin (W+1)) (stream : ℕ→Bool)
    (packed : (store z).val<2^size.val) (source : ∀i : Fin size.val,stream (start+i.val)=(store z).val.testBit i.val) :
    weight (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) qp (address which size ⟨start%B,Nat.mod_lt _ bp⟩
      (dense B stream (start/B)) (dense B stream (start/B+1)))=DescentTerminalLeafFold.code (selectMode z qp which) := by
  let x : Word B := ⟨(store z).val,packed.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ size.isLt))⟩
  have found:=window_read bp start size x stream packed source
  simp [weight,address,found,x,(store z).isLt,load_store]

theorem weight_blank (qp : 0<q) (size : Fin (B+1)) (skip : Fin B) (lo hi : Word B) :
    weight (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) qp (address (0:Fin (W+1)) size skip lo hi)=0 := by
  simp [weight,address,selectMode,DescentTerminalLeafFold.code]

theorem price (h : ℕ) (small : Nat.clog 2 (W+1)+Nat.clog 2 (B+1)+Nat.clog 2 B+2*B≤h/2) :
    slots B W≤2^(h/2) := by
  have cap (n : ℕ) : n≤2^(Nat.clog 2 n):=Nat.le_pow_clog (by decide) n
  have bound:=Nat.mul_le_mul (cap (W+1)) (Nat.mul_le_mul (cap (B+1)) (Nat.mul_le_mul (cap B) (le_refl ((2^B)*(2^B)))))
  unfold slots
  apply bound.trans
  simp only [←pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

end
end Hierarchy.DescentTerminalSiteShelves

end OAI
