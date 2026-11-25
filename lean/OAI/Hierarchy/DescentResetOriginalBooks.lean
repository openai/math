import OAI.Hierarchy.DescentResetMixedWordIssued
import OAI.Hierarchy.DescentResetOriginalSlots

namespace OAI
/-! # One twelve-page dictionary for the full public original-word sheet -/
namespace Hierarchy.DescentResetMixedWordRAM.OriginalBooks
open DescentPackedZip DescentSIMDLookup DescentOrdinaryAtomFieldRAM.ROM DescentResetFieldAssembler
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {b z u t o M w : ℕ}
abbrev WordFn:=ℕ→ℕ→ℕ→ℕ→ℕ
def ix (s : Fin 2) (j : Fin 6) : Fin 12:=finProdFinEquiv (s,j)
def pages (b z u t o M : ℕ) (f : Fin 2→WordFn) (j : Fin 12) : Page :=
  let p : Fin 2×Fin 6:=finProdFinEquiv.symm j
  Book.pages b z u t o M (f p.1) p.2

local notation "width"=>Book.unit b z u t*M
variable (f : Fin 2→WordFn)
local notation "P"=>pages b z u t o M f
def afterHeader (b z u t M base : ℕ):=base+12*2^(Book.unit b z u t*M)

def chart (b z u t o M base : ℕ) (f : Fin 2→WordFn) (s : Fin 2) : Charts:=
  let read:=fun i=>joined (pages b z u t o M f) (Book.unit b z u t*M) base (fun j=>ix s (Book.index i j))
  ⟨read 0,read 1,read 2⟩

theorem page_at (s : Fin 2) (j : Fin 6) : P (ix s j)=Book.pages b z u t o M (f s) j:=by simp [pages,ix]
theorem page_bound (j : Fin 12) : (P j).bits≤width:=Book.bits _ _

theorem installed (base : ℕ) (m : Memory w) (room : afterHeader b z u t M base<2^w) :
    let dst:=after P width base m
    let charts:=chart b z u t o M base f
    (mount P width w base).Exec m dst (4+10*(12*2^width)) ∧
      (∀s,Static (charts s).mask (head (b:=b) (z:=z)) M dst ∧ Static (charts s).args (couple u t) M dst ∧
        Static (charts s).word (result (u:=u) (t:=t) (o:=o) (f s)) M dst) ∧
      (∀j,j<base ∨ afterHeader b z u t M base≤j→dst j=m j) ∧ CheapCode (mount P width w base) ∧
      DescentStaticWordColumn.names (mount P width w base)=15*(12*2^width+1):=by
  obtain ⟨exec,names⟩:=DescentOrdinaryAtomFieldRAM.ROM.run P width base m room
  refine ⟨exec,?_,frame P width base m,cheap P width w base,names⟩
  intro s
  refine ⟨?_,?_,?_⟩
  · apply binary_mounted _ M P width base m (page_bound f) (fun j=>ix s (Book.index 0 j))
    intro j;simp [page_at,Book.pages,Book.index]
  · apply binary_mounted _ M P width base m (page_bound f) (fun j=>ix s (Book.index 1 j))
    intro j;simp [page_at,Book.pages,Book.index]
  · apply binary_mounted _ M P width base m (page_bound f) (fun j=>ix s (Book.index 2 j))
    intro j;simp [page_at,Book.pages,Book.index]

theorem fits (base at_ : ℕ) (early : afterHeader b z u t M base≤at_) (space : at_<2^w) (s : Fin 2)
    («meta» zero halo arg : Expr) (m : «meta».Fits w at_) (q : zero.Fits w at_) (h : halo.Fits w at_) (v : arg.Fits w at_) :
    let C:=chart b z u t o M base f s
    Fits C.mask «meta» zero (b*7) z M at_ w ∧ Fits C.args halo arg u t M at_ w ∧
      Fits C.word (C.mask.read «meta» zero) (C.args.read halo arg) 2 (u+t) M at_ w:=by
  intro C
  have bank_ (i : Fin 3) (j : Fin 2) : (bank P width base (ix s (Book.index i j))).Fits w at_:=bank_room P width base at_ _ (page_bound f _) early space
  have bits_n (i : Fin 3) (j : Fin 2) : (P (ix s (Book.index i j))).bits=(Book.pages b z u t o M (f s) (Book.index i j)).bits:=congrArg Page.bits (page_at f s _)
  have first : Fits C.mask «meta» zero (b*7) z M at_ w:=⟨m,q,bank_ 0 0,bank_ 0 1,bits_n 0 0,bits_n 0 1⟩
  have second : Fits C.args halo arg u t M at_ w:=⟨h,v,bank_ 1 0,bank_ 1 1,bits_n 1 0,bits_n 1 1⟩
  exact ⟨first,second,⟨by simp [Tables.read,Expr.Fits,first.left,first.right,first.shift,first.apply],
    by simp [Tables.read,Expr.Fits,second.left,second.right,second.shift,second.apply],bank_ 2 0,bank_ 2 1,bits_n 2 0,bits_n 2 1⟩⟩

end
end Hierarchy.DescentResetMixedWordRAM.OriginalBooks

end OAI
