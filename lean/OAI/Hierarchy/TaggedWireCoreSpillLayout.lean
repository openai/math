import OAI.Hierarchy.TaggedWireCoreLayout

namespace OAI
/-! # Ordinary commodity paths of the dated spill receiver -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope
open scoped Classical BigOperators
variable {S : PurchaseSampler} {h d k K edges : ℕ}
    {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
    (B : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord K)

namespace Mount

/-- The early directory only has commodity occurrences; the final reserve
directory is absent at this stage. -/
def spillLayout : SettledMatrix.Layout K edges (Commodity (Fin (2^h)) (Stages h d) k) Empty where
  edge := filledChord B.actual pad
  goods := commodityGraph π place
  reserve := ⟨Empty.elim,Empty.elim⟩
  goodsDistinct i := inj.ne (goods_different π i)
  reserveDistinct := fun i => nomatch i
  core := B.ordinary
  center := Empty.elim
  corePath i := unordered_walk (graph π place) _ B.row (B.core_order inj pad) (commodity_walk (S:=S) π place 0 i).1
  centerPath := fun i => nomatch i

end Mount
end Hierarchy.ProbeStage.CoreBoard
end

end OAI
