import OAI.Hierarchy.DescentResetStemProjectExpr
import OAI.Hierarchy.DescentResetDenseOperand
import OAI.Hierarchy.DescentContactWidthPage

namespace OAI
/-! A measured old field is recoded and retiled once for each donor slot.
All positive socket requests can then read it through the compact actor directory. -/
namespace Hierarchy.DescentResetOriginalDonors
open DescentSIMDLookup DescentPackedZip DescentResetStemProject
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
structure Panel where
  sparseHosts : ℕ
  groups : ℕ
  blocks : ℕ
  lanes : ℕ
  fields : ℕ
  oldBits : ℕ
  bits : ℕ
namespace Panel
variable (P : Panel) (base : ℕ)
def cut := DescentContactWidthPage.endAddress base P.oldBits P.lanes
def endAddress := DescentResetStemProject.endAddress (P.cut base) P.fields P.sparseHosts P.groups P.blocks
  P.bits P.lanes P.lanes
def bank (j : Fin P.fields) (x : Fin P.blocks) := DescentResetStemProject.bank (P.cut base) P.fields
  P.sparseHosts P.groups P.blocks P.bits P.lanes P.lanes j x
def expanded (term : Fin P.fields→Expr) (j : Fin P.fields) :=
  DescentContactWidthPage.expr base P.oldBits P.bits P.lanes (term j)

theorem extent : P.endAddress base=base+P.endAddress 0 := by
  rw [endAddress,DescentResetStemProject.extent]
  change (base+DescentContactWidthPage.words P.oldBits P.lanes)+_=base+_
  rw [endAddress,DescentResetStemProject.extent (P.cut 0)]
  simp [cut,DescentContactWidthPage.endAddress,Nat.add_assoc]

theorem bounds : base≤P.cut base ∧ P.cut base≤P.endAddress base := by
  refine ⟨Nat.le_add_right ..,?_⟩
  rw [endAddress,DescentResetStemProject.extent]
  exact Nat.le_add_right ..

variable (src : Fin P.fields→Expr) {w : ℕ}
local notation "castMem" m => DescentContactWidthPage.image base P.oldBits P.bits P.lanes m
local notation "prefix" w => DescentContactWidthPage.program base P.oldBits P.bits P.lanes w
local notation "post" w => DescentResetStemProjectExpr.program (P.cut base) P.sparseHosts P.groups P.blocks
  P.bits P.lanes P.lanes (P.expanded base src) w

def program (w : ℕ) := (prefix w).seq (post w)
def after (m : Memory w) :=
  DescentResetStemProjectExpr.image (P.cut base) P.sparseHosts P.groups P.blocks P.bits P.lanes P.lanes
    (P.expanded base src) (castMem m)
def ticks := DescentContactWidthPage.clock P.oldBits P.lanes+
  DescentResetStemProjectExpr.ticks (P.cut base) P.sparseHosts P.groups P.blocks P.bits P.lanes P.lanes
    (P.expanded base src)

theorem any (m : Memory w) (lanes : 0<P.lanes) (blocks : 0<P.blocks)
    (inputs : ∀j,(src j).Fits w base) (room : P.endAddress base<2^w) :
    (P.program base src w).Exec m (P.after base src m) (P.ticks base src) ∧
    CheapCode (P.program base src w) ∧ ∀a,a<base ∨ P.endAddress base≤a→P.after base src m a=m a := by
  obtain ⟨low,high⟩:=P.bounds base
  have C:=DescentContactWidthPage.any base P.oldBits P.bits P.lanes m (high.trans_lt room)
  have T:=DescentResetStemProjectExpr.any (P.cut base) P.sparseHosts P.groups P.blocks P.bits P.lanes P.lanes
    (P.expanded base src) (castMem m) lanes blocks (fun j=>DescentContactWidthPage.fits _ _ _ _ _
      (inputs j) (high.trans_lt room)) room
  refine ⟨?_,@cheap_seq w _ _ (@C.2.1) (@T.2.2),?_⟩
  · intro pcCount regCount publicCount machine pc reg pub exit installed params cfg mem entry initial
    exact Procedure.Exec.then (A:=prefix w) (B:=post w) (a:=m) (b:=castMem m)
      (c:=P.after base src m) (ca:=DescentContactWidthPage.clock P.oldBits P.lanes)
      (cb:=DescentResetStemProjectExpr.ticks (P.cut base) P.sparseHosts P.groups P.blocks
        P.bits P.lanes P.lanes (P.expanded base src))
      C.1 T.1 machine pc reg pub exit installed params cfg mem entry initial
  intro a outside
  exact (T.2.1 a (outside.imp (fun h=>h.trans_le low) id)).trans
    (C.2.2 a (outside.imp id (fun h=>high.trans h)))

theorem rows (m : Memory w) (values : Fin P.fields→Fin P.sparseHosts→Fin (P.groups*P.blocks)→Cell P.oldBits)
    (lanes : 0<P.lanes) (blocks : 0<P.blocks) (inputs : ∀j,(src j).Fits w base)
    (seen : ∀j,Source (src j) (values j) P.lanes m) (room : P.endAddress base<2^w) :
    ∀j x,(P.bank base j x).Fits w (P.endAddress base) ∧
      Source (.lookup (P.bank base j x) .row)
        (fun h g=>DescentContactWidthPage.recode P.bits (values j h (finProdFinEquiv (g,x)))) P.lanes (P.after base src m) := by
  have enough:=(P.bounds base).2.trans_lt room
  let converted (j : Fin P.fields) (v : Fin P.sparseHosts) (g : Fin (P.groups*P.blocks)) :=
    DescentContactWidthPage.recode P.bits (values j v g)
  have T:=DescentResetStemProjectExpr.run (P.cut base) P.sparseHosts P.groups P.blocks P.bits P.lanes P.lanes
    (P.expanded base src) (castMem m) converted lanes lanes blocks
    (fun j=>DescentContactWidthPage.fits _ _ _ _ _ (inputs j) enough)
    (fun j=>DescentContactWidthPage.posted _ _ _ _ m enough _ _ (inputs j) (seen j)) room
  exact fun j x=>⟨T.2.2.1 j x,T.2.1 j x⟩

end Panel
end
end Hierarchy.DescentResetOriginalDonors

end OAI
