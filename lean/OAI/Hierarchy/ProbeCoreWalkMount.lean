import OAI.Hierarchy.ProbeCoreWalks

namespace OAI
/-! # Placing original walks in the physical edge table -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe WireTelescope
open scoped Classical
variable {S : PurchaseSampler} {h d k K : ℕ}

/-- Inject the core catalogue into the same ordinal table as the accepted
purchased links. A reversal or a duplicate elsewhere in that table has no
effect on either the local restriction or the multiplicity bill. -/
structure Mount (π : Equiv.Perm (Fin (2^h))) (place : Site h d k → Fin K) (edges : ℕ) where
  actual : PortGraph (Fin K) (Fin edges)
  row : Edges S h d k ↪ Fin edges
  tail : ∀ e,actual.tail (row e)=(graph π place).tail e
  head : ∀ e,actual.head (row e)=(graph π place).head e

namespace Mount
variable {π : Equiv.Perm (Fin (2^h))} {place : Site h d k → Fin K} {edges : ℕ}
    (B : Mount (S:=S) π place edges)

def ordinary (i : Commodity (Fin (2^h)) (Stages h d) k) : List (Fin edges) :=
  (commodityWalk π i).map B.row

def centers (c : Columns h d × Fin k) : List (Fin edges) := (catalystWalk c).map B.row

end Mount
end Hierarchy.ProbeStage.CoreBoard
end

end OAI
