import OAI.Hierarchy.DescentResetStemProjectExpr
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Transposing the original narrow seed census before expanding its printed tokens -/
namespace Hierarchy.DescentSeedTokenTransposition.Narrow
open DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (base O G X a A M : ℕ) (old : Bank)

def source (old : Bank) : Fin 1→Expr :=fun _=>.lookup old .row
def cut := DescentResetStemProject.endAddress base 1 O G X a A M
def page (x : Fin X) := DescentResetStemProject.bank base 1 O G X a A M 0 x
def program (w : ℕ) := DescentResetStemProjectExpr.program base O G X a A M (source old) w
def ticks := DescentResetStemProjectExpr.ticks base O G X a A M (source old)
def image (m : Memory w) := DescentResetStemProjectExpr.image base O G X a A M (source old) m

/-- Changing the displayed census cardinality preserves the physical word at every packed row. -/
theorem reindex_reads {R : ℕ} (eqn : R=G*X) (m : Memory w) (ys : Fin O→Fin R→Cell a)
    (read : Reads old ys A m) : Reads old (fun h (i : Fin (G*X))=>ys h (i.cast eqn.symm)) A m :=by
  subst R
  exact read

theorem cut_eq : cut base O G X a A M=base+cut 0 O G X a A M :=
  DescentResetStemProject.extent ..

theorem page_fits (x : Fin X) (room : cut base O G X a A M<2^w) :
    (page base O G X a A M x).Fits w (cut base O G X a A M) ∧ O*chunks G M≤(page base O G X a A M x).size :=
  ⟨DescentResetStemProject.page_fits (q:=(0:Fin 1)) (x:=x) room,
    DescentResetStemProject.page_capacity (q:=(0:Fin 1)) (x:=x)⟩

theorem any (m : Memory w) (lanes : 0<M) (blocks : 0<X) (fit : old.Fits w base)
    (room : cut base O G X a A M<2^w) :
    (program base O G X a A M old w).Exec m (image base O G X a A M old m) (ticks base O G X a A M old) ∧
    (∀i,i<base ∨ cut base O G X a A M ≤ i → image base O G X a A M old m i=m i) ∧
      CheapCode (program base O G X a A M old w) :=
  DescentResetStemProjectExpr.any base O G X a A M (source old) m lanes blocks (fun _=>⟨fit,trivial⟩) room

theorem issued (m : Memory w) (ys : Fin O→Fin (G*X)→Cell a) (oldLanes : 0<A) (lanes : 0<M)
    (blocks : 0<X) (fit : old.Fits w base) (capacity : O*chunks (G*X) A≤old.size)
    (read : Reads old ys A m) (room : cut base O G X a A M<2^w) :
    let last:=image base O G X a A M old m
    (program base O G X a A M old w).Exec m last (ticks base O G X a A M old) ∧
      (∀x,Reads (page base O G X a A M x) (fun h g=>ys h (finProdFinEquiv (g,x))) M last) ∧
      (∀i,i<base ∨ cut base O G X a A M ≤ i → last i=m i) ∧ CheapCode (program base O G X a A M old w) :=by
  have input : Source (.lookup old .row) ys A m:=fun p=>
    (bank_read old m ((row O (G*X) A p).isLt.trans_le capacity) fit).trans (read p)
  obtain ⟨cpu,stored,_,frame,affordable⟩:=DescentResetStemProjectExpr.run base O G X a A M (source old) m
    (fun _=>ys) oldLanes lanes blocks (fun _=>⟨fit,trivial⟩) (fun _=>input) room
  refine ⟨cpu,?_,frame,@affordable⟩
  intro x p
  have bank:=page_fits base O G X a A M x room
  exact (bank_read (page base O G X a A M x) _ ((row O G M p).isLt.trans_le bank.2) bank.1).symm.trans
    (stored (0:Fin 1) x p)

end
end Hierarchy.DescentSeedTokenTransposition.Narrow

end OAI
