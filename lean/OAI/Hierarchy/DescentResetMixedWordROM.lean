import OAI.Hierarchy.DescentResetMixedWordRAM
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # The fixed shared six-page initializer and original mixed parent-word tariff -/
namespace Hierarchy.DescentResetMixedWordRAM.Book
open DescentPackedZip DescentSIMDLookup DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {b z u t o M H G w : ℕ} (f : ℕ→ℕ→ℕ→ℕ→ℕ)

def unit (b z u t : ℕ) :=max (b*7+z) (2+(u+t))
def index (i : Fin 3) (j : Fin 2) : Fin 6:=finProdFinEquiv (i,j)
def pages (b z u t o M : ℕ) (fn : ℕ→ℕ→ℕ→ℕ→ℕ) (j : Fin 6) : Page :=
  let x : Fin 3×Fin 2:=finProdFinEquiv.symm j
  (![binary (head (b:=b) (z:=z)) M,binary (couple u t) M,binary (result (u:=u) (t:=t) (o:=o) fn) M] x.1) x.2

local notation "P"=>pages b z u t o M f
local notation "width"=>unit b z u t*M

def chart (b z u t o M base : ℕ) (f : ℕ→ℕ→ℕ→ℕ→ℕ) : Charts :=
  let get:=fun i=>joined (pages b z u t o M f) (unit b z u t*M) base (index i)
  ⟨get 0,get 1,get 2⟩

theorem bits (j : Fin 6) : (P j).bits≤width:=by
  obtain ⟨⟨n,k⟩,rfl⟩:=(finProdFinEquiv (m:=3) (n:=2)).surjective j
  have a:=Nat.le_max_left (b*7+z) (2+(u+t))
  have c:=Nat.le_max_right (b*7+z) (2+(u+t))
  fin_cases n <;> fin_cases k <;> apply Nat.mul_le_mul_right M <;> change _≤ max _ _ <;> omega

theorem setup (base : ℕ) (m : Memory w) (room : base+6*2^width<2^w) :
    let done:=after P width base m
    let C:=chart b z u t o M base f
    (mount P width w base).Exec m done (4+10*(6*2^width)) ∧
      Static C.mask (head (b:=b) (z:=z)) M done ∧ Static C.args (couple u t) M done ∧ Static C.word (result (u:=u) (t:=t) (o:=o) f) M done ∧
      (∀j,j<base ∨ base+6*2^width≤j→done j=m j) ∧ CheapCode (mount P width w base) ∧
      DescentStaticWordColumn.names (mount P width w base)=15*(6*2^width+1):=by
  intro done C
  obtain ⟨run,names⟩:=DescentOrdinaryAtomFieldRAM.ROM.run P width base m room
  refine ⟨run,?_,?_,?_,frame P width base m,cheap P width w base,names⟩
  · apply binary_mounted _ M P width base m (bits f) (index 0)
    intro j;simp [pages,index]
  · apply binary_mounted _ M P width base m (bits f) (index 1)
    intro j;simp [pages,index]
  · apply binary_mounted _ M P width base m (bits f) (index 2)
    intro j;simp [pages,index]

theorem gates (base at_ : ℕ) (early : base+6*2^width≤at_) (room : at_<2^w) («meta» zero halo arg : Expr)
    (m : «meta».Fits w at_) (q : zero.Fits w at_) (h : halo.Fits w at_) (v : arg.Fits w at_) :
    let C:=chart b z u t o M base f
    Fits C.mask «meta» zero (b*7) z M at_ w ∧ Fits C.args halo arg u t M at_ w ∧
      Fits C.word (C.mask.read «meta» zero) (C.args.read halo arg) 2 (u+t) M at_ w:=by
  intro C
  have pageFit (i : Fin 3) (j : Fin 2) : (bank P width base (index i j)).Fits w at_:=bank_room P width base at_ _ (bits f _) early room
  have low : Fits C.mask «meta» zero (b*7) z M at_ w:=⟨m,q,pageFit 0 0,pageFit 0 1,rfl,rfl⟩
  have high : Fits C.args halo arg u t M at_ w:=⟨h,v,pageFit 1 0,pageFit 1 1,rfl,rfl⟩
  exact ⟨low,high,⟨by simp [Tables.read,Expr.Fits,low.left,low.right,low.shift,low.apply],
    by simp [Tables.read,Expr.Fits,high.left,high.right,high.shift,high.apply],pageFit 2 0,pageFit 2 1,rfl,rfl⟩⟩

theorem work (C : Charts) («meta» zero halo arg : Expr) :
    (operation C «meta» zero halo arg).work=«meta».work+zero.work+halo.work+arg.work+33:=by
  simp only [operation,DescentPackedZip.work];omega

theorem hardware (base : ℕ) (C : Charts) («meta» zero halo arg : Expr) (out N : ℕ) :
    DescentStaticWordColumn.names ((mount P width w base).seq (scan w out N (operation C «meta» zero halo arg)))=
      15*(6*2^width+1)+(11+4*(«meta».work+zero.work+halo.work+arg.work+33)):=by
  rw [DescentStaticWordColumn.names_seq, DescentOrdinaryAtomFieldRAM.ROM.mount,
    DescentStaticWordColumn.names_mount, DescentStaticWordColumn.names_scan, work]

end
end Hierarchy.DescentResetMixedWordRAM.Book

end OAI
