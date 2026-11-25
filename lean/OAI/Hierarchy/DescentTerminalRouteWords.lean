import OAI.Hierarchy.DescentTerminalRouteDimensions
import OAI.Computability.VPVNP.RAMSerialization
import Mathlib.Data.Fintype.Prod

namespace OAI
/-! # Binary serialization of the two short port lists in a bin row -/
namespace Hierarchy.DescentTerminalRouteRows
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization
open scoped Classical
noncomputable section
variable {W q a : ℕ}

/-- Index one is the operand name on a table row and zero the cable name on a port row. -/
abbrev Row (q a : ℕ) := Fin 2→Fin q→Option (Word a)

def encodeField (z : Option (Word a)) (j : Fin (a+1)) : Bool :=
  Fin.cases z.isSome (fun k=>z.elim false (fun x=>wordBits a x k)) j
def decodeField (b : Fin (a+1)→Bool) : Option (Word a) :=
  if b 0 then some ((wordBits a).symm (fun j=>b j.succ)) else none
theorem field_back (z : Option (Word a)) : decodeField (encodeField z)=z := by
  cases z with
  | none=>rfl
  | some z=>simp [decodeField,encodeField]

def pack (x : Row q a) : Word (rowBits q a) :=
  (wordBits _).symm (fun b=>
    let ij:Fin 2×Fin (q*(a+1)):=finProdFinEquiv.symm b
    let jd:Fin q×Fin (a+1):=finProdFinEquiv.symm ij.2
    encodeField (x ij.1 jd.1) jd.2)
def unpack (x : Word (rowBits q a)) : Row q a :=
  fun side j=>decodeField (fun d=>wordBits _ x (finProdFinEquiv (side,finProdFinEquiv (j,d))))
theorem row_back (x : Row q a) : unpack (pack x)=x := by
  funext side j
  simp only [unpack,pack,Equiv.apply_symm_apply,Equiv.symm_apply_apply,field_back]

def packBin (x : Fin W→Word a) : Word (W*a) :=
  (wordBits _).symm (fun u=>wordBits _ (x (finProdFinEquiv.symm u).1) (finProdFinEquiv.symm u).2)
def unpackBin (x : Word (W*a)) (i : Fin W) : Word a :=
  (wordBits _).symm (fun j=>wordBits _ x (finProdFinEquiv (i,j)))
theorem bin_back (x : Fin W→Word a) (i : Fin W) : unpackBin (packBin x) i=x i := by
  simp only [unpackBin,packBin,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
theorem bin_inj {x y : Word (W*a)} (h : ∀i:Fin W,unpackBin x i=unpackBin y i) : x=y := by
  apply (wordBits _).injective;funext j
  obtain ⟨⟨i,k⟩,rfl⟩:=finProdFinEquiv.surjective j
  simpa [unpackBin] using congrArg (fun z=>wordBits a z k) (h i)


end
end Hierarchy.DescentTerminalRouteRows

end OAI
