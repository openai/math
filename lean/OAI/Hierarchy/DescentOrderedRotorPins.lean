import OAI.Hierarchy.DescentOrderedRotorItems
import OAI.Hierarchy.DescentTrivalentRotor
import OAI.Hierarchy.DescentRotorSliceRecords

namespace OAI
/-! # Configured physical rotor coefficients at sorted original occurrence slots -/

namespace Hierarchy.DescentRotor.Ordered
open DescentRotor.Physical DescentBaseProfile Computability.BorderVNP.Crossing
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped BigOperators Classical
noncomputable section
variable {E K : Type*} [Fintype E] [Field K] {n h C w u N D : ℕ} (G : Graph n h)
  {hw : 0<w} {src dst : E→Fin (2^n)} {pay : ℝ} (P : BaseCircuit K G C w u hw src dst pay) (key : E↪Fin N)
local notation "ord" => orderedAddress key src dst hw
local notation "perm" => permutation key src dst

private theorem packets_reindex (x : E→Fin u→Bool) :
    packetWord ord x = packetWord (packetAddress src dst hw) (x ∘ (perm).symm) :=
  funext (packetWord_reindex key src dst hw x)

variable {G} in
/-- Each of the two words is generated in the same order in each real
bundle cell, before placing its packets into the chosen host layer. -/
def actualPins (x y : E→Fin u→Bool) : Ports (fun _ : Pin (2^n)=>P.layers*(u*w)) :=
  pinValues
    (fun r v=>fillRows 0 (fun q=>(P.choose q,q.1)) (packetWord ord x) (r,v))
    (fun r v=>fillRows 0 (fun q=>(P.choose q,q.2.1)) (packetWord ord y) (r,v))

theorem actualPins_eq (x y : E→Fin u→Bool) : actualPins P key x y =
    Physical.actualPins P (x ∘ (perm).symm) (y ∘ (perm).symm) := by
  let pack (a b : Packet w (matrixOfBundles src dst) → Fin u → Fin (2^w)) :=
    pinValues
      (fun r v => fillRows 0 (fun q => (P.choose q,q.1)) a (r,v))
      (fun r v => fillRows 0 (fun q => (P.choose q,q.2.1)) b (r,v))
  exact congrArg₂ pack (packets_reindex (hw:=hw) (src:=src) (dst:=dst) key x)
    (packets_reindex (hw:=hw) (src:=src) (dst:=dst) key y)

private theorem all_eq (x y : E→Fin u→Bool) :
    (∀e,(x ∘ (perm).symm) e=(y ∘ (perm).symm) e) ↔ ∀e,x e=y e :=
  ⟨fun rel e=>by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using rel (perm e),
    fun rel e=>rel _⟩

/-- The fixed rotor and all its actual configured scalar tables are identical
throughout the readdressing. Vacant packet digits agree as well. -/
theorem actual_value (x y : E→Fin u→Bool) :
    (rotor G P D).value (rotorTables G P D) (actualPins P key x y)=if ∀e,x e=y e then 1 else 0 := by
  rw [actualPins_eq,rotor_value]
  simp only [all_eq key x y]

def sliceAddress (x y : E→Fin u→Bool) (z : BaseCircuit.Hidden P) (s : BaseCircuit.Slice P) :
    Fin (Fintype.card (Entry G.arcs C w)) :=
  let r:=s.1
  let v:=s.2.1
  let k:=s.2.2
  DescentRotor.key G.arcs C w (P.rotation r,⟨v,
    fillRows 0 (fun q=>(P.choose q,q.1)) (packetWord ord x) (r,v) k,
    fillRows 0 (fun q=>(P.choose q,q.2.1)) (packetWord ord y) (r,v) k,
    fun p=>z r p.val.1 k⟩)

theorem slice_read (x y : E→Fin u→Bool) (z : BaseCircuit.Hidden P) (s : BaseCircuit.Slice P) :
    sliceAddress G P key x y z s=P.address (x ∘ (perm).symm) (y ∘ (perm).symm) z s := by
  let fetch (a b : Packet w (matrixOfBundles src dst) → Fin u → Fin (2^w)) :=
    DescentRotor.key G.arcs C w (P.rotation s.1,⟨s.2.1,
      fillRows 0 (fun q => (P.choose q,q.1)) a (s.1,s.2.1) s.2.2,
      fillRows 0 (fun q => (P.choose q,q.2.1)) b (s.1,s.2.1) s.2.2,
      fun p => z s.1 p.val.1 s.2.2⟩)
  exact congrArg₂ fetch (packets_reindex (hw:=hw) (src:=src) (dst:=dst) key x)
    (packets_reindex (hw:=hw) (src:=src) (dst:=dst) key y)

theorem lookup_contraction (x y : E→Fin u→Bool) :
    (∑ z : BaseCircuit.Hidden P,∏ s : BaseCircuit.Slice P,
      rom G.arcs C w (fixedTable P.menu) (sliceAddress G P key x y z s))=if ∀e,x e=y e then 1 else 0 := by
  simp only [slice_read,BaseCircuit.lookup_contraction,all_eq key x y]

end
end Hierarchy.DescentRotor.Ordered

end OAI
