import OAI.Hierarchy.DescentSharedSelectedColumns
import OAI.Hierarchy.DescentExteriorLookup
import OAI.Hierarchy.DescentColonyLayout

namespace OAI
/-! # Original donor-group rank, original low block, and zero-group flag -/
namespace Hierarchy.DescentStemCoordinateBook
open DescentSIMDLookup DescentColonies DescentGL DescentPackedZip DescentSharedSelectedColumns
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Shape where
  dim : ℕ
  fine : ℕ
  residual : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  width : ℕ

namespace Shape
variable (C : Shape)
abbrev Slot:=Fin 3×(Block C.fine×Block C.residual)
def count:=3*((2^C.fine)*(2^C.residual))
def number : C.Slot≃Fin C.count:=((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)
def layout : DescentSharedSelectedColumns.Layout:=⟨C.hosts,C.groups,C.lanes,C.width,C.dim*C.dim,C.count⟩
def coarse (g : Fin C.groups) (x : Block C.fine) :=g.val*2^C.fine+x.val
def original (μ : DescentGL.Layout C.dim) (g : Fin C.groups) (x : Block C.fine) (l : Block C.residual) : Block C.dim :=
  (rearrange μ).symm ⟨(C.coarse g x*2^C.residual+l.val)%2^C.dim,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

def value (μ : DescentGL.Layout C.dim) (j : Fin 3) (x : Block C.fine) (l : Block C.residual) (g : Fin C.groups) : ℕ :=
  if j=0 then
    let gr:=fun t : Block C.residual=>(C.original μ g x t).val/2^C.fine
    ((Finset.univ.image gr).filter (·<gr l)).card
  else if j=1 then (C.original μ g x l).val%2^C.fine else (decide (C.coarse g x=0)).toNat

def fields : C.layout.Fields :=fun j key g=>
  let q:=C.number.symm j
  (C.value (DescentExterior.storedLayout C.dim key) q.1 q.2.1 q.2.2 g:Cell C.width)

def src (base : ℕ) (saved : Bank) (j : Fin 3) (x : Block C.fine) (l : Block C.residual) : Expr :=
  C.layout.src base saved (C.number (j,x,l))
def program (base w : ℕ) :=C.layout.program base C.fields w
def image {w : ℕ} (base : ℕ) (m : Memory w) :=C.layout.image base C.fields m
def ticks:=C.layout.clock
def endAddress (base : ℕ) :=C.layout.endAddress base

theorem any {w : ℕ} (base : ℕ) (m : Memory w) (room : C.endAddress base<2^w) :
    (C.program base w).Exec m (C.image base m) C.ticks ∧ CheapCode (C.program base w) ∧
      ∀u,u<base ∨ C.endAddress base≤u→C.image base m u=m u :=
  C.layout.any base C.fields m room

theorem read {w : ℕ} (base : ℕ) (saved : Bank) (m : Memory w) (μ : DescentGL.Layout C.dim)
    (chosen : m saved.base=((DescentExterior.matrixCode μ).val:Word w)) (low : saved.Fits w base)
    (room : C.endAddress base<2^w) (j : Fin 3) (x : Block C.fine) (l : Block C.residual) :
    (C.src base saved j x l).Fits w (C.endAddress base) ∧
    Source (C.src base saved j x l) (fun (_:Fin C.hosts) g=>(C.value μ j x l g:Cell C.width)) C.lanes (C.image base m) := by
  refine ⟨C.layout.src_fits base saved _ low room,?_⟩
  simpa only [src,fields,Equiv.symm_apply_apply,DescentExterior.stored_matrixCode,image,layout]
    using C.layout.read base saved C.fields m (C.number (j,x,l)) (DescentExterior.matrixCode μ) chosen low room

theorem extent (base : ℕ) : C.endAddress base=base+C.endAddress 0 := by
  simp [endAddress,DescentSharedSelectedColumns.Layout.endAddress,DescentSharedSelectedColumns.Layout.tableBase,Nat.add_assoc]

theorem size_le :
    C.endAddress 0≤2*(C.hosts*chunks C.groups C.lanes)+1+
      C.count*(2^(C.dim*C.dim)*(2*chunks C.groups C.lanes+1)) := by
  change 0+2^(Nat.clog 2 (C.hosts*chunks C.groups C.lanes))+
    C.count*(2^(C.dim*C.dim+Nat.clog 2 (chunks C.groups C.lanes)))≤_
  rw [Nat.zero_add,pow_add]
  exact Nat.add_le_add (DescentDyadicSpan.span_le _) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (DescentDyadicSpan.span_le _)))

end Shape
end
end Hierarchy.DescentStemCoordinateBook

end OAI
