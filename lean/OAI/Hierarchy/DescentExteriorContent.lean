import OAI.Hierarchy.DescentExteriorShelfOperands
import OAI.Hierarchy.DescentExteriorShelfStore

namespace OAI
/-! # The literal ROM, payload, and proposal words in the exterior shelf -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentExteriorFetch DescentGL Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {j r t e w : ℕ}
local notation "R" => 2^(j+r)
local notation "n" => e*R
local notation "k" => j+(j+r)
local notation "K" => 2^(keyBits j r)
local notation "D" => 2^(2^j*t)
local notation "H" => span j r t e
local notation "I" => Fin n

def padWord {length : ℕ} (f : Fin length→Word w) (addr : ℕ) : Word w :=
  if hi : addr<length then f ⟨addr,hi⟩ else 0

@[simp] theorem padWord_at {length : ℕ} (f : Fin length→Word w) (a : Fin length) :
    padWord f a.val=f a := by simp [padWord,a.isLt]

def dir (s : Fin 3) : ℕ→Word w :=
  padWord (fun a : Fin K=>((source j r s ((keyIndex j r).symm a)).val:Word w))

def permROM (s : Fin 3) : ℕ→Word w :=
  padWord (fun u : Fin (K*D)=>
    let pair:=finProdFinEquiv.symm u
    ((entry j r t s ((keyIndex j r).symm pair.1) pair.2).val:Word w))

def columnWords (M : Fin e→Layout k) (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool)
    : Fin 17→ℕ→Word w :=
  let raw (s : Fin 3) := padWord (fun i : I=>((pack (fun a=>passInputs x z s (slab i) (a,dest i))).val:Word w))
  let guess (s : Fin 2) := padWord (fun i : I=>((gathered z (phase s,false,slab i,dest i)).val:Word w))
  ![padWord (fun i:I=>((slab i).val:Word w)),padWord (fun a:Fin e=>((matrixCode (M a)).val:Word w)),
    padWord (fun a:Word (k*k)=>((a.val*R:ℕ):Word w)),padWord (fun i:I=>((rowOrd j r (dest i)).val:Word w)),
    padWord (fun i:I=>(((slab i).val*R:ℕ):Word w)),
    dir (j:=j) (r:=r) 0,dir (j:=j) (r:=r) 1,dir (j:=j) (r:=r) 2,
    padWord (fun a:Fin K=>((a.val*D:ℕ):Word w)),raw 0,raw 1,raw 2,
    permROM (j:=j) (r:=r) (t:=t) 0,permROM (j:=j) (r:=r) (t:=t) 1,
    permROM (j:=j) (r:=r) (t:=t) 2,guess 0,guess 1]

theorem fixed_except_matrix (M L : Fin e→Layout k) (x : Fin e→Plane j r→Fin t→Bool)
    (z : Hidden e j r t→Bool) (i : Fin 17) (foreign : i≠1) :
    columnWords (w:=w) M x z i=columnWords L x z i := by
  fin_cases i <;> first | contradiction | rfl

theorem permROM_read (s : Fin 3) (a : Fin K) (u : Word (2^j*t)) :
    permROM (w:=w) (j:=j) (r:=r) (t:=t) s (a.val*D+u.val)=
      ((entry j r t s ((keyIndex j r).symm a) u).val:Word w) := by
  let both:=finProdFinEquiv (a,u)
  have addr : a.val*D+u.val=both.val := by change _=u.val+D*a.val;ring
  rw [addr]
  unfold permROM
  rw [padWord_at]
  simp only [both,Equiv.symm_apply_apply]

def staged (origin : ℕ) (M : Fin e→Layout k) (x : Fin e→Plane j r→Fin t→Bool)
    (z : Hidden e j r t→Bool) (m : Memory w) :=
  store j r t e origin m (fun i u=>columnWords M x z i u.val)

def Loaded (origin : ℕ) (M : Fin e→Layout k) (x : Fin e→Plane j r→Fin t→Bool)
    (z : Hidden e j r t→Bool) (m : Memory w) :=
  ∀(i : Fin 17) (u : ℕ),u<H→m ((bank j r t e origin i.val).base+u)=columnWords M x z i u

theorem staged_loaded (origin : ℕ) (M : Fin e→Layout k) (x : Fin e→Plane j r→Fin t→Bool)
    (z : Hidden e j r t→Bool) (m : Memory w) : Loaded origin M x z (staged origin M x z m) :=
  fun i u live=>store_read j r t e origin m _ i ⟨u,live⟩

/-- The raw static shelf and the true selected matrix may be produced
separately. No other data word or dictionary depends on that selection. -/
theorem install (origin : ℕ) (M L : Fin e→Layout k) (x : Fin e→Plane j r→Fin t→Bool)
    (z : Hidden e j r t→Bool) (m actual : Memory w) (old : Loaded origin L x z m)
    (preserve : ∀(i : Fin 17),i≠1→∀u<H,actual ((bank j r t e origin i.val).base+u)=m ((bank j r t e origin i.val).base+u))
    (matrices : ∀u<H,actual ((bank j r t e origin 1).base+u)=
      padWord (fun a:Fin e=>((matrixCode (M a)).val:Word w)) u) :
    Loaded origin M x z actual := by
  intro i u hu
  by_cases ctrl : i=1
  · subst i;exact matrices u hu
  · rw [preserve i ctrl u hu,old i u hu,fixed_except_matrix L M x z i ctrl]

end
end Hierarchy.DescentExteriorShelf

end OAI
