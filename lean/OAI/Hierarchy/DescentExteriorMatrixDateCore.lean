import OAI.Hierarchy.DescentExteriorMatrixROM
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # A single native cumulative binary matrix, shared by all exterior slabs -/
namespace Hierarchy.DescentExteriorMatrixUpdate
open DescentGL DescentColonies DescentExterior
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w k h : ℕ}

structure Cell where
  old : Bank
  rotation : Bank
  offsets : Bank
  products : Bank
  updated : ℕ

def Cell.expr (L : Cell) := phase L.old L.rotation L.offsets L.products
def Cell.program (L : Cell) (w : ℕ) := scan w L.updated 1 L.expr
def Cell.after (L : Cell) (m : Memory w) := ProtocolRAM.image L.updated 1 L.expr m

structure Cell.Room (L : Cell) (w k h : ℕ) : Prop where
  prior : L.old.Fits w L.updated
  selected : L.rotation.Fits w L.updated
  offsets : L.offsets.Fits w L.updated
  lookup : L.products.Fits w L.updated
  scale : 2^(k*k)≤L.offsets.size
  entries : 2^(k*k)*2^(h*h)≤L.products.size
  address : L.updated+1<2^w

theorem Cell.run (L : Cell) (R : L.Room w k h) (m : Memory w) :
    (L.program w).Exec m (L.after m) 58 ∧ CheapCode (L.program w) := by
  have fits:L.expr.Fits w L.updated:=by
    exact ⟨R.lookup,⟨R.offsets,R.prior,trivial⟩,R.selected,trivial⟩
  exact ⟨scan_exec _ _ _ _ fits R.address,@scan_cheap w L.updated 1 L.expr⟩

/-- All fields read by the native update. The last two columns are static ROM.
`local` contains the measured matrix produced at this date. -/
def Cell.Shelf (L : Cell) (m : Memory w) (ext:Layout h→Layout k) (selected:Layout h) : Prop :=
  m L.rotation.base=((matrixCode selected).val:Word w) ∧
    (∀x:Word (k*k),m (L.offsets.base+x.val)=((x.val*2^(h*h):ℕ):Word w)) ∧
    (∀(x:Word (k*k)) (y:Word (h*h)),m (L.products.base+(x.val*2^(h*h)+y.val))=((entry ext x y).val:Word w))

theorem Cell.read (L : Cell) (R : L.Room w k h) (m : Memory w)
    (ext:Layout h→Layout k) (old:Layout k) (rot:Layout h)
    (prior:m L.old.base=((matrixCode old).val:Word w)) (shelf:L.Shelf m ext rot) :
    L.after m L.updated=((matrixCode (old.trans (ext rot))).val:Word w) := by
  obtain ⟨sel,offsets,table⟩:=shelf
  have input:Inputs L.old L.rotation L.offsets L.products ext (fun _:Fin 1=>old) (fun _=>rot) m:=
    ⟨fun i=>by obtain rfl : i=0 := Subsingleton.elim _ _; simpa using prior,
     fun i=>by obtain rfl : i=0 := Subsingleton.elim _ _; simpa using sel,offsets,table⟩
  have result:=DescentExteriorMatrixUpdate.read L.old L.rotation L.offsets L.products L.updated
    R.prior R.selected R.offsets R.lookup R.prior.1 R.selected.1 R.scale R.entries ext
    (fun _:Fin 1=>old) (fun _=>rot) m input (0:Fin 1)
  simpa [Cell.after,Cell.expr,ProtocolRAM.image,fillSegment] using result

/-- A single common height/age-indexed encoding contains the complete bounded list
of product tables. They are installed once independently of external arity. -/
theorem all_tables {a k h w : ℕ} (space:k*k+h*h+a+1≤w/2) :
    2^a*(2^(k*k)+2^(k*k)*2^(h*h))≤2^(w/2) := by
  have sub:2^(k*k)≤2^(k*k+h*h):=Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)
  rw [←pow_add]
  calc
    _ ≤ 2^a*(2^(k*k+h*h)+2^(k*k+h*h)) := Nat.mul_le_mul_left _ (Nat.add_le_add_right sub _)
    _ = 2^(k*k+h*h+a+1) := by rw [pow_succ,pow_add];ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) space

end
end Hierarchy.DescentExteriorMatrixUpdate

/-! # Fixed native dates for recomposing the measured exterior linear maps -/
namespace Hierarchy.DescentExteriorMatrixUpdate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w : ℕ} (cell:ℕ→Cell)

def dated (w:ℕ) : ℕ→Procedure w
  | 0=>scan w 0 0 .row
  | t+1=>(dated w t).seq ((cell t).program w)
def reached (m:Memory w) : ℕ→Memory w
  | 0=>m
  | t+1=>(cell t).after (reached m t)

theorem execution (m:Memory w) (a k:ℕ) (size:ℕ→ℕ) (fits:∀t<a,(cell t).Room w k (size t)) :
    (dated cell w a).Exec m (reached cell m a) (4+58*a) ∧ CheapCode (dated cell w a) := by
  induction a with
  | zero=>
    have empty : (scan w 0 0 Expr.row).Exec m (ProtocolRAM.image 0 0 Expr.row m) (4+0*(2*Expr.row.work+4)) :=
      scan_exec (w:=w) 0 0 Expr.row m trivial (by simp)
    have same : ProtocolRAM.image 0 0 Expr.row m=m:=by
      funext a
      simp [ProtocolRAM.image,fillSegment]
    rw [same] at empty
    refine ⟨?_,@scan_cheap w 0 0 Expr.row⟩
    intro P R K machine
    exact empty machine
  | succ t ih=>
    have old:=ih (fun i hi=>fits i (by omega))
    have now:=(cell t).run (fits t (Nat.lt_succ_self _)) (reached cell m t)
    refine ⟨?_,cheap_seq old.2 now.2⟩
    change ((dated cell w t).seq ((cell t).program w)).Exec m
      ((cell t).after (reached cell m t)) (4+58*(t+1))
    rw [show 4+58*(t+1)=(4+58*t)+58 by omega]
    intro P R K machine
    exact Procedure.Exec.then old.1 now.1 machine

end
end Hierarchy.DescentExteriorMatrixUpdate

end OAI
