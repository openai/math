import OAI.Hierarchy.DescentDatedNodeMetadataOrdinary
import OAI.Hierarchy.DescentPackedNodeDigit

namespace OAI
/-! # Numeric metadata rows from the paid column and arbitrary normalized span digits -/
namespace Hierarchy.DescentDatedNodeMetadata.Chart
open DescentOrdinaryAtomFieldRAM DescentSIMDLookup DescentPackedZip DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w K : ℕ} (v : DescentDatedNodeMetadata.Chart)

private theorem metadataPacked (base a b : ℕ) (paid : v.Counts) (f6 : v.Spans K) (m : Memory w)
    (amount : Fin v.blocks→Fin v.hosts→Fin v.groups→Cell a)
    (spans : Fin v.blocks→Fin v.nodes→Fin K→Fin v.hosts→Fin v.groups→Cell b)
    (payFits : ∀x,(paid x).Fits w base) (srcFits : ∀x n j,(f6 x n j).Fits w base)
    (payRead : ∀x,Source (paid x) (amount x) v.lanes m) (spanRead : ∀x n j,Source (f6 x n j) (spans x n j) v.lanes m)
    (room : v.metadataEnd base a b<2^w) :
    ∃Y : Fin 2→Fin v.blocks→Fin v.hosts→Fin v.groups→Cell (v.bits*v.nodes),
      ∀f x,Reads (v.bank (v.inputsEnd base a b) f x) (Y f x) v.lanes (v.metadataImage base a b paid f6 m) :=by
  have le : v.inputsEnd base a b≤v.metadataEnd base a b:=by
    unfold metadataEnd;rw [v.translate];exact Nat.le_add_right ..
  have printed:=DescentResetMetadataInputs.issued base v.nodes a b v.bits v.lanes m paid f6 amount spans
    payFits srcFits payRead spanRead (le.trans_lt room)
  refine ⟨fun f x h g=>encode v.bits v.nodes (fun n=>if f=0 then
    DescentResetMetadataInputs.occupied n (amount x h g) 0 else
    (DescentResetMetadataInputs.countOn (fun j=>spans x n j h g) (List.finRange K):Cell v.bits)),?_⟩
  intro f x
  exact v.issued (v.inputsEnd base a b) (v.metaFields base a b paid f6) _
    (fun f x n=>(printed f x n).1) room _ (fun f x n=>(printed f x n).2) f x

theorem ordinaryPacked (base a b : ℕ) (paid : v.Counts) (src : v.Vectors K) (m : Memory w)
    (amount : Fin v.blocks→Fin v.hosts→Fin v.groups→Cell a)
    (words : Fin v.blocks→Fin K→Fin v.hosts→Fin v.groups→Cell (b*v.nodes))
    (payFits : ∀x,(paid x).Fits w base) (srcFits : ∀x j,(src x j).Fits w base)
    (payRead : ∀x,Source (paid x) (amount x) v.lanes m)
    (roomRows : ∀x j,v.rows≤(src x j).size) (old : ∀x j,Reads (src x j) (words x j) v.lanes m)
    (room : v.ordinaryEnd base a b<2^w) :
    ∃Y : Fin 2→Fin v.blocks→Fin v.hosts→Fin v.groups→Cell (v.bits*v.nodes),
      ∀f x,Reads (v.bank (v.inputsEnd (v.digitEnd base b) a b) f x) (Y f x) v.lanes
        (v.ordinaryImage base a b paid src m) :=by
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
  exact metadataPacked v (v.digitEnd base b) a b paid (v.scalarSpan base b src) mid amount _
    (fun x=>ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (payFits x))
    (v.scalarFit base b src srcFits lim) counts source room

end
end Hierarchy.DescentDatedNodeMetadata.Chart

end OAI
