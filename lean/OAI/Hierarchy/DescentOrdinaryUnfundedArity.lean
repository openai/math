import OAI.Hierarchy.DescentDatedNodeMetadataOrdinary
import OAI.Hierarchy.DescentPackedNodeDigit

namespace OAI
/-! # Flattened arity at every archived node, including unfunded exterior nodes -/
namespace Hierarchy.DescentDatedNodeMetadata.Chart
open DescentOrdinaryAtomFieldRAM DescentSIMDLookup DescentPackedZip DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w K : ℕ} (v : DescentDatedNodeMetadata.Chart)

theorem metadataPair (base a b : ℕ) (paid : v.Counts) (f6 : v.Spans K) (m : Memory w)
    (amount : Fin v.blocks→Fin v.hosts→Fin v.groups→Cell a)
    (spans : Fin v.blocks→Fin v.nodes→Fin K→Fin v.hosts→Fin v.groups→Cell b)
    (arity : Fin v.blocks→Fin v.nodes→Fin v.hosts→Fin v.groups→ℕ)
    (bounded : ∀x n h g,arity x n h g≤K)
    (live : ∀x n j h g,spans x n j h g≠0 ↔ j.val<arity x n h g)
    (payFits : ∀x,(paid x).Fits w base) (srcFits : ∀x n j,(f6 x n j).Fits w base)
    (payRead : ∀x,Source (paid x) (amount x) v.lanes m) (spanRead : ∀x n j,Source (f6 x n j) (spans x n j) v.lanes m)
    (room : v.metadataEnd base a b<2^w) (f : Fin 2) (x : Fin v.blocks) :
    Reads (v.bank (v.inputsEnd base a b) f x) (fun h g=>encode v.bits v.nodes (fun n=>
      if f=0 then (if n.val<(amount x h g).val then 1 else 0) else (arity x n h g:Cell v.bits)))
      v.lanes (v.metadataImage base a b paid f6 m) :=by
  have le : v.inputsEnd base a b≤v.metadataEnd base a b:=by
    unfold metadataEnd;rw [v.translate];exact Nat.le_add_right ..
  have printed:=DescentResetMetadataInputs.issued base v.nodes a b v.bits v.lanes m paid f6 amount spans
    payFits srcFits payRead spanRead (le.trans_lt room)
  have indexed:=v.issued (v.inputsEnd base a b) (v.metaFields base a b paid f6) _ (fun f x n=>(printed f x n).1) room
    _ (fun f x n=>(printed f x n).2) f x
  have tall (n) (h) (g) := DescentResetMetadataInputs.count_exact (fun j=>spans x n j h g)
    (arity x n h g) (bounded x n h g) (fun j=>live x n j h g)
  unfold metadataImage
  simp only [DescentResetMetadataInputs.occupied,tall] at indexed
  exact indexed

theorem metadataArity (base a b : ℕ) (paid : v.Counts) (f6 : v.Spans K) (m : Memory w)
    (amount : Fin v.blocks→Fin v.hosts→Fin v.groups→Cell a)
    (spans : Fin v.blocks→Fin v.nodes→Fin K→Fin v.hosts→Fin v.groups→Cell b)
    (arity : Fin v.blocks→Fin v.nodes→Fin v.hosts→Fin v.groups→ℕ)
    (bounded : ∀x n h g,arity x n h g≤K)
    (live : ∀x n j h g,spans x n j h g≠0 ↔ j.val<arity x n h g)
    (payFits : ∀x,(paid x).Fits w base) (srcFits : ∀x n j,(f6 x n j).Fits w base)
    (payRead : ∀x,Source (paid x) (amount x) v.lanes m) (spanRead : ∀x n j,Source (f6 x n j) (spans x n j) v.lanes m)
    (room : v.metadataEnd base a b<2^w) (x : Fin v.blocks) :
    Reads (v.bank (v.inputsEnd base a b) 1 x) (fun h g=>encode v.bits v.nodes (fun n=>
      (arity x n h g:Cell v.bits)))
      v.lanes (v.metadataImage base a b paid f6 m) :=by
  simpa only [show (1:Fin 2)≠0 by decide,ite_false] using
    v.metadataPair base a b paid f6 m amount spans arity bounded live payFits srcFits payRead spanRead room 1 x

theorem ordinaryPair (base a b : ℕ) (paid : v.Counts) (src : v.Vectors K) (m : Memory w)
    (amount : Fin v.blocks→Fin v.hosts→Fin v.groups→Cell a)
    (words : Fin v.blocks→Fin K→Fin v.hosts→Fin v.groups→Cell (b*v.nodes))
    (arity : Fin v.blocks→Fin v.nodes→Fin v.hosts→Fin v.groups→ℕ) (bounded : ∀x n h g,arity x n h g≤K)
    (live : ∀x n j h g,ScalarOperand.take (a:=b) n (words x j h g)≠0 ↔ j.val<arity x n h g)
    (payFits : ∀x,(paid x).Fits w base) (srcFits : ∀x j,(src x j).Fits w base)
    (payRead : ∀x,Source (paid x) (amount x) v.lanes m)
    (roomRows : ∀x j,v.rows≤(src x j).size) (old : ∀x j,Reads (src x j) (words x j) v.lanes m)
    (room : v.ordinaryEnd base a b<2^w) (f : Fin 2) (x : Fin v.blocks) :
    Reads (v.bank (v.inputsEnd (v.digitEnd base b) a b) f x) (fun h g=>encode v.bits v.nodes (fun n=>
      if f=0 then (if n.val<(amount x h g).val then 1 else 0) else (arity x n h g:Cell v.bits)))
      v.lanes (v.ordinaryImage base a b paid src m) :=by
  have lim:=v.digitRoom base a b room
  let mid:=v.digitImage base b m
  have prior (t : ℕ) (lo : t<base) : mid t=m t:=ROM.frame _ _ _ _ t (.inl lo)
  have counts (x : Fin v.blocks) : Source (paid x) (amount x) v.lanes mid:=by
    intro u;exact (eval_below _ _ m mid (payFits x) prior).trans (payRead x u)
  have source (x : Fin v.blocks) (n : Fin v.nodes) (j : Fin K) : Source (v.scalarSpan base b src x n j)
      (fun h g=>ScalarOperand.take (a:=b) n (words x j h g)) v.lanes mid:=by
    have earlier:=source_column _ base (srcFits x j) m _ (roomRows x j) (old x j)
    have kept : Source (.lookup (src x j) .row) (words x j) v.lanes mid:=by
      intro u;exact (eval_below (.lookup (src x j) .row) _ m mid ⟨srcFits x j,trivial⟩ prior).trans (earlier u)
    exact ScalarOperand.fetched (ScalarOperand.chart base b v.nodes v.lanes) (.lookup (src x j) .row) n
      (v.digitEnd base b) mid (words x j) kept (v.scalarFit base b src srcFits lim x n j).1 rfl
      (ScalarOperand.initialized base b v.nodes v.lanes m n)
  exact v.metadataPair (v.digitEnd base b) a b paid (v.scalarSpan base b src) mid amount _ arity bounded live
    (fun x=>ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (payFits x))
    (v.scalarFit base b src srcFits lim) counts source room f x

theorem ordinaryArity (base a b : ℕ) (paid : v.Counts) (src : v.Vectors K) (m : Memory w)
    (amount : Fin v.blocks→Fin v.hosts→Fin v.groups→Cell a)
    (words : Fin v.blocks→Fin K→Fin v.hosts→Fin v.groups→Cell (b*v.nodes))
    (arity : Fin v.blocks→Fin v.nodes→Fin v.hosts→Fin v.groups→ℕ) (bounded : ∀x n h g,arity x n h g≤K)
    (live : ∀x n j h g,ScalarOperand.take (a:=b) n (words x j h g)≠0 ↔ j.val<arity x n h g)
    (payFits : ∀x,(paid x).Fits w base) (srcFits : ∀x j,(src x j).Fits w base)
    (payRead : ∀x,Source (paid x) (amount x) v.lanes m)
    (roomRows : ∀x j,v.rows≤(src x j).size) (old : ∀x j,Reads (src x j) (words x j) v.lanes m)
    (room : v.ordinaryEnd base a b<2^w) (x : Fin v.blocks) :
    Reads (v.bank (v.inputsEnd (v.digitEnd base b) a b) 1 x) (fun h g=>encode v.bits v.nodes (fun n=>
      (arity x n h g:Cell v.bits)))
      v.lanes (v.ordinaryImage base a b paid src m) :=by
  simpa only [show (1:Fin 2)≠0 by decide,ite_false] using
    v.ordinaryPair base a b paid src m amount words arity bounded live payFits srcFits payRead roomRows old room 1 x

end
end Hierarchy.DescentDatedNodeMetadata.Chart

end OAI
