import OAI.Hierarchy.DescentTerminalBookRadices
import OAI.Hierarchy.DescentTerminalLocalPortBook

namespace OAI
/-! # Literal bounded radices for the common terminal incidence book -/
namespace Hierarchy.DescentTerminalLocalPortBook
open Computability.VPVNP.BurstRAM DescentTerminalRouteRows
open scoped Classical BigOperators
noncomputable section
namespace Book
variable {G V M A a W q : ℕ}
def flat {k c : ℕ} (x : Fin k→Fin c) := finFunctionFinEquiv x
def portFile {k n c : ℕ} (x : Fin k→Fin n→Fin c) := flat (fun i=>flat (x i))
def cols (u : Book G V M A a) :=
  (u.groupCount,u.nodeCount,flat u.groupSize,flat u.nodeArity,portFile u.portName,portFile u.operand)
def packCols {g v gs va edges args : ℕ} (u : Fin g×Fin v×Fin gs×Fin va×Fin edges×Fin args) :=
  finProdFinEquiv (u.1,finProdFinEquiv (u.2.1,finProdFinEquiv (u.2.2.1,
      finProdFinEquiv (u.2.2.2.1,finProdFinEquiv u.2.2.2.2))))
def uncols {g v gs va edges args : ℕ} (i : Fin (g*(v*(gs*(va*(edges*args)))))) :
    Fin g×Fin v×Fin gs×Fin va×Fin edges×Fin args :=
  let v₁ :=finProdFinEquiv.symm i
  let v₂ :=finProdFinEquiv.symm v₁.2
  let v₃ :=finProdFinEquiv.symm v₂.2
  let v₄ :=finProdFinEquiv.symm v₃.2
  ⟨v₁.1,v₂.1,v₃.1,v₄.1,finProdFinEquiv.symm v₄.2⟩
def bytes (u : Book G V M A a) := packCols (cols u)
def readFile {k n c : ℕ} (z : Fin ((c^n)^k)) : Fin k→Fin n→Fin c :=
  fun i=>finFunctionFinEquiv.symm (finFunctionFinEquiv.symm z i)
private theorem read_portFile {k n c : ℕ} (x : Fin k → Fin n → Fin c) :
    readFile (portFile x) = x := by
  funext i
  simp only [readFile,portFile,flat,Equiv.symm_apply_apply]

def fromBytes {G V M A a : ℕ} (z : Fin ((G+1)*((V+1)*((M+1)^G*((A+1)^V*(((2^a)^M)^G*((2^a)^A)^V)))))) :
    Book G V M A a :=
  let u:=uncols z
  ⟨u.1,u.2.1,finFunctionFinEquiv.symm u.2.2.1,finFunctionFinEquiv.symm u.2.2.2.1,readFile u.2.2.2.2.1,readFile u.2.2.2.2.2⟩
theorem bytes_read (u : Book G V M A a) : fromBytes (bytes u)=u := by
  cases u
  simp only [bytes,fromBytes,cols,packCols,uncols,read_portFile,flat,Equiv.symm_apply_apply]

def request (owner whereAt : Fin W) (u : Book G V M A a) : Fin (W*(W*Bytes G V M A a)) :=
  finProdFinEquiv (owner,finProdFinEquiv (whereAt,bytes u))
def menu {G V M A a W : ℕ} (q : ℕ) (j : Fin (W*(W*Bytes G V M A a))) :=
  let u:=finProdFinEquiv.symm j
  let hdr:=finProdFinEquiv.symm u.2
  Book.emit (fromBytes hdr.2 : Book G V M A a) q hdr.1.val u.1
theorem menu_read (u : Book G V M A a) (owner whereAt : Fin W) :
    menu q (request owner whereAt u)=u.emit q whereAt.val owner := by simp [menu,request,bytes_read]
theorem request_val (u : Book G V M A a) (owner whereAt : Fin W) :
    (request owner whereAt u).val=(bytes u).val + Bytes G V M A a*whereAt.val +
      W*Bytes G V M A a*owner.val:=rfl
theorem room {w z h : ℕ} (cap : W≤2^z) (document : Bytes G V M A a≤2^h) (short : z+z+h≤w/2) :
    W*(W*Bytes G V M A a)≤2^(w/2) := by
  calc
    _ ≤ 2^z*(2^z*2^h) := Nat.mul_le_mul cap (Nat.mul_le_mul cap document)
    _ = 2^(z+z+h) := by rw [Nat.pow_add,Nat.pow_add];ac_rfl
    _ ≤ _ := Nat.pow_le_pow_right (by decide) short

end Book
end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
