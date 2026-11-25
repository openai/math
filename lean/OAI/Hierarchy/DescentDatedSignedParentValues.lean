import OAI.Hierarchy.DescentDatedSignedDrawing
import OAI.Hierarchy.DescentDatedSignedHeader

namespace OAI
/-! The two retained original parent fields used by the successor's operand reader. -/
namespace Hierarchy.DescentDatedAddressBook.SignedDrawing
open DescentSixParty DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentHaloWalkRAM DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F Pin U : Type} [Field F] [Fintype U] [DecidableEq U]
  {d H prior degree Q O K b groups k age : ℕ} {bits : Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ} {A:GroupStage W G price ε (Fin groups) U k}
  {native:W.graph.Edge↪ℕ} {R:Fin prior→Fin degree→Option (Fin prior)}
  {symm:∀u v j,R u j=some v→∃n,R v n=some u} {host:U↪Fin H} {pitch:ℕ}
  {space:Fused.capacity degree Q K A.cap≤2^b}
  {before:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Option (Fused.Raw R Q K A.cap b)}
  {parent:Fin (2^k)→Fin O→Fin prior→Fin groups→Option (ParentFilter.Source (breadth degree) Q K A.cap)}
  {marks:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Cell 1}
variable (d₀:SignedDrawing A native R symm host pitch space before parent marks)
    (S:DescentCompiler.AtomSchedule) (ready:A.StateBounds S age)
local notation "group" => (Function.Embedding.refl (Fin groups))
local notation "home" => SignedExtent.wholeHost group host
local notation "name" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank ((group).trans Fin.valEmbedding) (host.trans Fin.valEmbedding))

/-- The first grain's common serial counts earlier parallel grains in the issuer's actual edge order. -/
def serial (x:Fin (2^k)) (j:Fin (breadth degree*O)) (v:Fin H) (g:Fin groups):Cell b:=by
  letI:=d₀.finiteEdge
  letI:=d₀.finiteRaw
  letI:=d₀.finiteTicket
  exact Fin.ofNat (2^b) (DescentOrdinarySignedRanks.result d₀.blocks (Incidence.of_measured d₀.blocks R symm d₀.observed d₀.order)
    home (Stage.measured A native S ready) x 1 j v g)

/-- The receiver's sorted successor-neighbor digit of that same incident original parent. -/
def peer (x:Fin (2^k)) (j:Fin (breadth degree*O)) (v:Fin H) (g:Fin groups):Cell b:=by
  letI:=d₀.finiteEdge
  letI:=d₀.finiteRaw
  letI:=d₀.finiteTicket
  exact SignedExtent.signedPeer A native S ready name d₀.blocks R symm d₀.observed home x j v g

theorem missing (x:Fin (2^k)) (j:Fin (breadth degree*O)) (v:Fin H) (g:Fin groups)
    (absent:home x v g=none):
    d₀.serial S ready x j v g=0 ∧ d₀.peer S ready x j v g=0 :=by
  simp [serial,peer,DescentOrdinarySignedRanks.result,DescentOrdinarySignedRanks.request,SignedExtent.signedPeer,absent]
end
end Hierarchy.DescentDatedAddressBook.SignedDrawing

end OAI
