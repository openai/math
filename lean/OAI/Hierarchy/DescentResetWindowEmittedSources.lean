import OAI.Hierarchy.DescentResetWindowResidentSources
import OAI.Hierarchy.DescentRecipeClosedReset

namespace OAI
/-! # Reading the receiver source class from the emitted host directory -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentParallelBase DescentSharedCableNames DescentStageEdgeReceipt
open scoped Classical
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {q ε : ℝ}

private theorem renamed_near {V J : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {X Y : MarkedWorld F d P bits} {k : ℕ} (p : GroupStage X G q ε J V k)
    (s : Equiv.Perm X.graph.Site) (e : Equiv.Perm X.graph.Edge) (eqn : Y=PhysicalRename.world X s e) :
    let post : GroupStage Y G q ε J V k:=eqn.symm ▸ p.names s e
    post.near=p.near := by subst Y;rfl

variable {W : MarkedWorld F d P bits} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "rank" => ((Z).rawHostRank T vertex).trans Fin.valEmbedding
local notation "A" => B.next.placement
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k

theorem rendered_near {p : ℕ} (record : B.Recorded p) : (A).near=(Z).emittedNear T := by
  let birth:=DescentOrderedReset.grains W B.count B.order
  let norm:=(Z).orderedReblock T birth
  let rawSite:=B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) rank) B.valid.coordinates
  let index:=((Z).nativeResetEdges T vertex birth).order.trans Fin.valEmbedding
  let s:=DescentPhysicalOrder.rename rawSite
  let e:=DescentPhysicalOrder.rename (DescentResetLocalOrder.allCode B.raw index S B.valid rawSite)
  have renamed : (A).near=B.raw.near := renamed_near B.raw s e (norm.appendNames_result s e)
  exact renamed.trans record.neighbors

theorem sourceClass_emitted {p : ℕ} (record : B.Recorded p) (v : Host) (x : Local (blocks B) v) :
    (sourceClass B v x).val=
      ((insert v.1.2 ((Z).emittedNear T v.1.2)).filter
        (fun u=>rank u<rank ((blocks B).src x.val).1.2)).card := by
  exact (sourceClass_host B v x).trans (congrArg (fun near : B.next.V → Finset B.next.V =>
    ((insert v.1.2 (near v.1.2)).filter (fun u=>rank u<rank ((blocks B).src x.val).1.2)).card)
    (rendered_near B record))

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
