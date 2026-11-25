import OAI.Hierarchy.TaggedWideRankedRows

namespace OAI
/-! # Cut and mask observations at a native row rank -/
noncomputable section
open scoped Classical Fin.CommRing
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms.RankedRows
open ThreeFlat Routing
open AdaptiveProbe TaggedPrune Tagged WireTelescope ProtocolRAM.Calendar ProtocolStackContraction
open WideStack WideStack.Leaf WideCalendarSites WideControlJoin
variable {F : Type} [Field F] {L groups ports lanes w m n view : ℕ}
  {key : Fin L ↪ ℕ×ℕ} {S Ex Se : Type} [Fintype S] [Fintype Ex] [Fintype Se]
  (G : Gate) {board : RowBoard} (r : RankedRows (F:=F) key S groups ports lanes w m n view board)

/-- Both tests use the same transported compactor settings and physical voltage
assignment as the private and decoded cells of the signed receipt. -/
structure CutsAndMask (cut : Fin L→ CutFormat F (SitePins Ex Se S G)) (pad : Net F (SitePins Ex Se S G))
    (ex : Ex→ Bool) (sel : Se→ Bool) (seen : G.Seen→ Bool) : Prop where
  cuts : ∀a y h p t,(cut t).closed (readPins r.numbering ex sel seen
    (write (banks r.installed) r.cap a y h p))=((banks r.installed) t).settings.close (a t)
  masks : ∀a y h p,TypedWiring.value pad (readPins r.numbering ex sel seen
    (write (banks r.installed) r.cap a y h p))=
      if supported (banks r.installed) (active r.installed) a then 1 else 0

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms.RankedRows
end

end OAI
