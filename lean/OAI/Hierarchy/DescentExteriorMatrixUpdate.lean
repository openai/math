import OAI.Hierarchy.DescentExteriorCoordinates
import OAI.Hierarchy.DescentExteriorLookup
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Native cumulative GF(2) matrix update at a recorded reset or ordinary phase -/
namespace Hierarchy.DescentExteriorMatrixUpdate
open DescentGL DescentExterior Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {w k h n : ℕ}

/-- All slabs and histories use this same numbered finite coefficient-free table. -/
def entry (ext : Layout h→Layout k) (old : Word (k*k)) (step : Word (h*h)) : Word (k*k) :=
  matrixCode ((storedLayout k old).trans (ext (storedLayout h step)))

@[simp] theorem entry_read (ext : Layout h→Layout k) (old : Layout k) (step : Layout h) :
    entry ext (matrixCode old) (matrixCode step)=matrixCode (old.trans (ext step)) := by
  simp [entry]

def phase (old step offsets table : Bank) : Expr :=
  .lookup table (.op .add (.lookup offsets (.lookup old .row)) (.lookup step .row))

theorem phase_work (a b c d : Bank) : (phase a b c d).work=25 := rfl

def Inputs (a b c d : Bank) (ext : Layout h→Layout k) (old : Fin n→Layout k)
    (step : Fin n→Layout h) (m : Memory w) : Prop :=
  (∀i:Fin n,m (a.base+i.val)=((matrixCode (old i)).val:Word w)) ∧
  (∀i:Fin n,m (b.base+i.val)=((matrixCode (step i)).val:Word w)) ∧
  (∀x:Word (k*k),m (c.base+x.val)=((x.val*2^(h*h):ℕ):Word w)) ∧
  (∀(x:Word (k*k)) (y:Word (h*h)),m (d.base+(x.val*2^(h*h)+y.val))=((entry ext x y).val:Word w))

private theorem atBank {w out : ℕ} (b : Bank) (m : Memory w) (a : ℕ) (small : a<b.size)
    (fit : b.Fits w out) : b.read m (a:Word w)=m (b.base+a) := by
  simp [Bank.read,Fin.val_cast_of_lt (small.trans fit.2.1),Nat.mod_eq_of_lt small]

theorem read (a b c d : Bank) (out : ℕ) (fa : a.Fits w out) (fb : b.Fits w out)
    (fc : c.Fits w out) (fd : d.Fits w out)
    (na : n≤a.size) (nb : n≤b.size) (nc : 2^(k*k)≤c.size) (nd : 2^(k*k)*2^(h*h)≤d.size)
    (ext : Layout h→Layout k) (old : Fin n→Layout k) (step : Fin n→Layout h)
    (m : Memory w) (data : Inputs a b c d ext old step m) (i : Fin n) :
    (phase a b c d).eval m (i.val:Word w)=((matrixCode ((old i).trans (ext (step i)))).val:Word w) := by
  obtain ⟨prior,selected,offset,table⟩:=data
  let x:=matrixCode (old i)
  let y:=matrixCode (step i)
  have bound : x.val*2^(h*h)+y.val<2^(k*k)*2^(h*h) := by
    have s:=x.isLt
    have p:=Nat.mul_le_mul_right (2^(h*h)) (Nat.succ_le_of_lt s)
    have q:=y.isLt
    rw [Nat.succ_mul] at p
    omega
  simp only [phase,Expr.eval,RowOp.opcode,BinaryOp.eval]
  rw [atBank a m _ (i.isLt.trans_le na) fa,prior,atBank b m _ (i.isLt.trans_le nb) fb,selected,
    atBank c m _ (x.isLt.trans_le nc) fc,offset,←Nat.cast_add,
    atBank d m _ (bound.trans_le nd) fd,table,entry_read]

theorem run (a b c d : Bank) (out : ℕ) (fa : a.Fits w out) (fb : b.Fits w out)
    (fc : c.Fits w out) (fd : d.Fits w out) (na : n≤a.size) (nb : n≤b.size)
    (nc : 2^(k*k)≤c.size) (nd : 2^(k*k)*2^(h*h)≤d.size) (endFit : out+n<2^w)
    (ext : Layout h→Layout k) (old : Fin n→Layout k) (step : Fin n→Layout h) :
    (scan w out n (phase a b c d)).Spec (Inputs a b c d ext old step)
      (fun m dst=>dst=image out n (phase a b c d) m ∧ ∀i:Fin n,dst (out+i.val)=
        ((matrixCode ((old i).trans (ext (step i)))).val:Word w)) (4+54*n) ∧
      CheapCode (scan w out n (phase a b c d)) := by
  refine ⟨?_,@scan_cheap _ _ _ _⟩
  have fit : (phase a b c d).Fits w out := ⟨fd,⟨fc,fa,trivial⟩,fb,trivial⟩
  intro P X A machine pc reg pub exit rom shared cfg m start hs
  obtain ⟨cnt,tick,done,after,adv,stop,eq⟩:=scan_exec out n (phase a b c d) m fit endFit
    machine pc reg pub exit rom shared cfg m start rfl
  refine ⟨cnt,by simpa [phase_work,Nat.mul_comm] using tick,done,after,adv,stop,eq,?_⟩
  intro i
  rw [eq]
  simpa [ProtocolRAM.image,fillSegment,show out≤out+i.val ∧ out+i.val<out+n by have:=i.isLt;omega,Nat.cast_add]
    using read a b c d out fa fb fc fd na nb nc nd ext old step m hs i

/-- The whole advice is printed once regardless of the number of exterior
slabs and the number of visits to this fixed stage format. -/
theorem advice_words (room : k*k+h*h≤w/2) :
    2^(k*k)+2^(k*k)*2^(h*h)≤2*2^(w/2) := by
  have a : 2^(k*k)≤2^(w/2) := Nat.pow_le_pow_right (by decide) (by omega)
  have b : 2^(k*k+h*h)≤2^(w/2) := Nat.pow_le_pow_right (by decide) room
  rw [pow_add] at b
  omega

/-- The resulting ordinal names the full genuine history layout, including
the static permutations of already retained coordinates. -/
theorem recorded {E : Type} {before middle after : E→Bits k} {r : ℕ}
    (arity : k=h+r) (into out : Equiv.Perm (Fin k)) (old : Record before middle)
    (step : Layout h) (next : Record middle after) (trueStep : next.layout=promote arity into out step) :
    entry (promote arity into out) (matrixCode old.layout) (matrixCode step)=
      matrixCode (old.then next).layout := by simp [Record.then,trueStep]

end
end Hierarchy.DescentExteriorMatrixUpdate

end OAI
