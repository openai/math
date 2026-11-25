import OAI.Hierarchy.DescentDatedNodeMetadata
import OAI.Hierarchy.DescentMetadataInputCore

namespace OAI
/-! # Recovering and checkpointing real node arities after an ordinary or reset venue is funded -/
namespace Hierarchy.DescentDatedNodeMetadata.Chart
open DescentSIMDLookup DescentPackedColony DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w K : ℕ} (v : DescentDatedNodeMetadata.Chart)

abbrev Counts :=Fin v.blocks→Expr
abbrev Spans (K : ℕ) :=Fin v.blocks→Fin v.nodes→Fin K→Expr

def metaFields (base a b : ℕ) (paid : v.Counts) (f6 : v.Spans K) : v.Input:=
  DescentResetMetadataInputs.exprs base v.nodes a b v.bits v.lanes paid f6

def metadataProgram (base a b w : ℕ) (paid : v.Counts) (f6 : v.Spans K) :=
  (DescentResetMetadataInputs.program base v.nodes a b v.bits v.lanes w).seq
    (v.program (v.inputsEnd base a b) w (v.metaFields base a b paid f6))

def metadataTime (base a b : ℕ) (paid : v.Counts) (f6 : v.Spans K) :=
  DescentResetMetadataInputs.clock v.nodes a b v.bits v.lanes+v.ticks (v.inputsEnd base a b) (v.metaFields base a b paid f6)

def metadataImage (base a b : ℕ) (paid : v.Counts) (f6 : v.Spans K) (m : Memory w) :=
  v.image (v.inputsEnd base a b) (v.metaFields base a b paid f6) (DescentResetMetadataInputs.image base v.nodes a b v.bits v.lanes m)

theorem metadataAny (base a b : ℕ) (paid : v.Counts) (f6 : v.Spans K) (m : Memory w)
    (payFits : ∀x,(paid x).Fits w base) (srcFits : ∀x n j,(f6 x n j).Fits w base) (room : v.metadataEnd base a b<2^w) :
    (v.metadataProgram base a b w paid f6).Exec m (v.metadataImage base a b paid f6 m) (v.metadataTime base a b paid f6) ∧
    (∀t,t<base ∨ v.metadataEnd base a b≤t→v.metadataImage base a b paid f6 m t=m t) ∧
    CheapCode (v.metadataProgram base a b w paid f6) :=by
  have le : v.inputsEnd base a b≤v.metadataEnd base a b:=by
    unfold metadataEnd;rw [v.translate];exact Nat.le_add_right ..
  have lut:=DescentResetMetadataInputs.any base v.nodes a b v.bits v.lanes m (le.trans_lt room)
  have run:=v.any (v.inputsEnd base a b) _ (DescentResetMetadataInputs.image base v.nodes a b v.bits v.lanes m)
    (DescentResetMetadataInputs.expr_fits base v.nodes a b v.bits v.lanes paid f6 payFits srcFits (le.trans_lt room)) room
  refine ⟨?_,?_,cheap_seq lut.2.1 run.2.2⟩
  · intro P R slots machine
    exact Procedure.Exec.then lut.1 run.1 machine
  · intro t h
    exact (run.2.1 t (h.imp_left (fun k=>k.trans_le (Nat.le_add_right ..)))).trans (lut.2.2 t (h.imp_right (le.trans ·)))

theorem metadataRead (base a b : ℕ) (paid : v.Counts) (f6 : v.Spans K) (m : Memory w)
    (amount : Fin v.blocks→Fin v.hosts→Fin v.groups→Cell a)
    (spans : Fin v.blocks→Fin v.nodes→Fin K→Fin v.hosts→Fin v.groups→Cell b)
    (arity : Fin v.blocks→Fin v.nodes→Fin v.hosts→Fin v.groups→ℕ)
    (bounded : ∀x n h g,arity x n h g≤K)
    (live : ∀x n j h g,spans x n j h g≠0 ↔ n.val<(amount x h g).val ∧ j.val<arity x n h g)
    (payFits : ∀x,(paid x).Fits w base) (srcFits : ∀x n j,(f6 x n j).Fits w base)
    (payRead : ∀x,Source (paid x) (amount x) v.lanes m) (spanRead : ∀x n j,Source (f6 x n j) (spans x n j) v.lanes m)
    (room : v.metadataEnd base a b<2^w) (f : Fin 2) (x : Fin v.blocks) :
    Reads (v.bank (v.inputsEnd base a b) f x) (fun h g=>encode v.bits v.nodes (fun n=>
      if n.val<(amount x h g).val then if f=0 then (1:Cell v.bits) else (arity x n h g:Cell v.bits) else 0))
      v.lanes (v.metadataImage base a b paid f6 m) :=by
  have le : v.inputsEnd base a b≤v.metadataEnd base a b:=by
    unfold metadataEnd;rw [v.translate];exact Nat.le_add_right ..
  have printed:=DescentResetMetadataInputs.issued_exact base v.nodes a b v.bits v.lanes m paid f6 amount spans arity bounded live
    payFits srcFits payRead spanRead (le.trans_lt room)
  exact v.issued (v.inputsEnd base a b) (v.metaFields base a b paid f6) _ (fun f x n=>(printed f x n).1) room
    _ (fun f x n=>(printed f x n).2) f x

end
end Hierarchy.DescentDatedNodeMetadata.Chart

end OAI
