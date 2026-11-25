import OAI.Hierarchy.DescentExteriorMatrixUpdate

namespace OAI
/-! # Printing the shared matrix-composition advice into the common input image -/
namespace Hierarchy.DescentExteriorMatrixUpdate
open DescentGL DescentExterior Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {w k h n : ℕ}
local notation "A" => 2^(k*k)
local notation "B" => 2^(h*h)

def rom (ext : Layout h→Layout k) : Fin (A+A*B)→Word w := fun i=>
  (finSumFinEquiv.symm i).elim (fun u=>((u.val*B:ℕ):Word w))
    (fun u=>let p : Word (k*k)×Word (h*h):=finProdFinEquiv.symm u
            ((entry ext p.1 p.2).val:Word w))

theorem rom_offset (ext : Layout h→Layout k) (x : Word (k*k)) :
    rom (w:=w) ext (finSumFinEquiv (.inl x))=((x.val*B:ℕ):Word w) := by simp [rom]

theorem rom_entry (ext : Layout h→Layout k) (x : Word (k*k)) (y : Word (h*h)) :
    rom (w:=w) ext (finSumFinEquiv (.inr (finProdFinEquiv (x,y))))=((entry ext x y).val:Word w) := by
  simp only [rom, Equiv.symm_apply_apply, Sum.elim_inr]

def offsetBank (origin k : ℕ) : Bank := ⟨origin,k*k⟩
def tableBank (origin k h : ℕ) : Bank := ⟨origin+2^(k*k),k*k+h*h⟩

theorem mounted (origin : ℕ) (ext : Layout h→Layout k) (old : Fin n→Layout k)
    (step : Fin n→Layout h) (m : Memory w) (a b : Bank)
    (left : ∀i:Fin n,m (a.base+i.val)=((matrixCode (old i)).val:Word w))
    (right : ∀i:Fin n,m (b.base+i.val)=((matrixCode (step i)).val:Word w))
    (loaded : ∀i:Fin (A+A*B),m (origin+i.val)=rom ext i) :
    Inputs a b (offsetBank origin k) (tableBank origin k h) ext old step m := by
  refine ⟨left,right,fun x=>?_,fun x y=>?_⟩
  · exact (loaded (finSumFinEquiv (.inl x))).trans (rom_offset ext x)
  · have got := (loaded (finSumFinEquiv (.inr (finProdFinEquiv (x,y))))).trans (rom_entry ext x y)
    change m (origin+(A+(y.val+B*x.val)))=_ at got
    change m (origin+A+(x.val*B+y.val))=_
    rw [show origin+A+(x.val*B+y.val)=origin+(A+(y.val+B*x.val)) by ring]
    exact got

theorem run_mounted (origin out : ℕ) (ext : Layout h→Layout k) (old : Fin n→Layout k)
    (step : Fin n→Layout h) (a b : Bank) (fa : a.Fits w out) (fb : b.Fits w out)
    (na : n≤a.size) (nb : n≤b.size) (gap : origin+A+A*B≤out) (endFit : out+n<2^w) :
    let c:=offsetBank origin k
    let d:=tableBank origin k h
    (scan w out n (phase a b c d)).Spec (fun m=>
      (∀i:Fin n,m (a.base+i.val)=((matrixCode (old i)).val:Word w)) ∧
      (∀i:Fin n,m (b.base+i.val)=((matrixCode (step i)).val:Word w)) ∧
      (∀i:Fin (A+A*B),m (origin+i.val)=rom ext i))
      (fun m dst=>dst=ProtocolRAM.image out n (phase a b c d) m ∧ ∀i:Fin n,dst (out+i.val)=
        ((matrixCode ((old i).trans (ext (step i)))).val:Word w)) (4+54*n) ∧
      CheapCode (scan w out n (phase a b c d)) := by
  intro c d
  have hc : c.size=A := rfl
  have hd : d.size=A*B := by simp [d,tableBank,Bank.size,pow_add]
  have cp : 0<A:=Nat.two_pow_pos _
  have dp : 0<A*B:=Nat.mul_pos cp (Nat.two_pow_pos _)
  have cf : c.Fits w out := by
    change 0<c.size ∧ c.size<2^w ∧ origin+c.size≤out
    rw [hc];omega
  have df : d.Fits w out := by
    change 0<d.size ∧ d.size<2^w ∧ origin+A+d.size≤out
    rw [hd];omega
  obtain ⟨r,cheap⟩:=run a b c d out fa fb cf df na nb hc.ge hd.ge endFit ext old step
  refine ⟨?_,@cheap⟩
  intro P X V machine pc reg pub exit inst shared cfg m atPC data
  exact r machine pc reg pub exit inst shared cfg m atPC
    (mounted origin ext old step m a b data.1 data.2.1 data.2.2)

end
end Hierarchy.DescentExteriorMatrixUpdate

end OAI
