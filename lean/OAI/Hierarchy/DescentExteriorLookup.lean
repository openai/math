import OAI.Hierarchy.DescentExteriorTableBits
import OAI.Hierarchy.DescentExteriorProposals
import OAI.Hierarchy.DescentColonyLayout
import OAI.Computability.VPVNP.RAMSerialization
import Mathlib.LinearAlgebra.StdBasis

namespace OAI
/-! # Literal binary-addressed tables for the exterior chunk services -/
namespace Hierarchy.DescentExterior
open DescentGL Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section

def matrixCode {k : ℕ} (M : Layout k) : Word (k*k) :=
  (wordBits _).symm (fun t=>
    let ij:=finProdFinEquiv.symm t
    finTwoEquiv (M ((Pi.basisFun (ZMod 2) (Fin k)) ij.1) ij.2))

theorem matrixCode_injective (k : ℕ) : Function.Injective (matrixCode (k:=k)) := by
  intro M L eq
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Fin k)).ext
  intro a
  funext b
  apply finTwoEquiv.injective
  simpa only [matrixCode,Equiv.apply_symm_apply,Equiv.symm_apply_apply,LinearEquiv.coe_coe,LinearEquiv.coe_toLinearMap] using
    congrFun (congrArg (wordBits (k*k)) eq) (finProdFinEquiv (a,b))

def storedLayout (k : ℕ) (a : Word (k*k)) : Layout k :=
  Function.extend matrixCode id (fun _ => LinearEquiv.refl _ _) a

@[simp] theorem stored_matrixCode {k : ℕ} (M : Layout k) : storedLayout k (matrixCode M)=M :=
  (matrixCode_injective k).extend_apply _ _ M

def chunkOrd (j : ℕ) : Bits j ≃ Fin (2^j) :=
  DescentColonies.address j

def rowOrd (j r : ℕ) : Rows j r ≃ Fin (2^(j+r)) :=
  (splitRows j r).symm.toEquiv.trans (DescentColonies.address (j+r))

def pos (j t : ℕ) : Bits j×Fin t ≃ Fin (2^j*t) :=
  ((chunkOrd j).prodCongr (Equiv.refl _)).trans finProdFinEquiv

def pack {j t : ℕ} (x : Bits j→Fin t→Bool) : Word (2^j*t) :=
  (wordBits _).symm (fun i=>x ((pos j t).symm i).1 ((pos j t).symm i).2)

theorem pack_bit {j t : ℕ} (x : Bits j→Fin t→Bool) (p : Bits j) (b : Fin t) :
    wordBits _ (pack x) (pos j t (p,b))=x p b := by simp [pack]

def pass {j r : ℕ} (M : Layout (j+(j+r))) (s : Fin 3) : Stage j r :=
  ![(plan M).first,(plan M).middle,(plan M).last] s

abbrev Key (j r : ℕ) := Word ((j+(j+r))*(j+(j+r))) × Fin (2^(j+r))
def key {j r : ℕ} (M : Layout (j+(j+r))) (row : Rows j r) : Key j r := (matrixCode M,rowOrd j r row)

def stageOf (j r : ℕ) (s : Fin 3) (a : Key j r) := pass (storedLayout _ a.1) s

def source (j r : ℕ) (s : Fin 3) (a : Key j r) : Fin (2^(j+r)) :=
  rowOrd j r ((stageOf j r s a).row.symm ((rowOrd j r).symm a.2))

def entry (j r t : ℕ) (s : Fin 3) (a : Key j r) (x : Word (2^j*t)) : Word (2^j*t) :=
  let c:=stageOf j r s a
  let src:=c.row.symm ((rowOrd j r).symm a.2)
  pack (fun p b=>wordBits _ x (pos j t ((c.slot src).symm p,b)))

theorem source_key {j r : ℕ} (M : Layout (j+(j+r))) (s : Fin 3) (v : Rows j r) :
    source j r s (key M v)=rowOrd j r ((pass M s).row.symm v) := by
  simp [source,stageOf,key]

theorem entry_key {j r t : ℕ} (M : Layout (j+(j+r))) (s : Fin 3) (x : Plane j r→Fin t→Bool)
    (v : Rows j r) :
    entry j r t s (key M v) (pack (fun p=>x (p,(pass M s).row.symm v))) =
      pack (fun p=>push (pass M s) x (p,v)) := by
  unfold entry
  simp only [stageOf,key,stored_matrixCode,Equiv.symm_apply_apply,pack_bit]
  rfl


def keyIndex (j r : ℕ) : Key j r ≃ Fin (2^(keyBits j r)) :=
  finProdFinEquiv.trans (Fin.castOrderIso (by simp [keyBits,pow_add])).toEquiv

/-- Three fixed ROMs, one per factor. A single selected input chunk and
one matrix-plus-row control key determine every output bit. -/
theorem image_words (j r t word : ℕ) (room : keyBits j r+(2^j)*t≤word/2) :
    3*(2^(keyBits j r)*2^(2^j*t))+3*2^(keyBits j r)≤6*2^(word/2) := by
  have keys : 2^(keyBits j r)≤2^(word/2) := Nat.pow_le_pow_right (by decide) (by omega)
  have joint : 2^(keyBits j r)*2^(2^j*t)≤2^(word/2) := by
    rw [←pow_add];exact Nat.pow_le_pow_right (by decide) room
  omega

end
end Hierarchy.DescentExterior

end OAI
