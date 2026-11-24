import OAI.Computability.VPVNP.PairTerminalVertexFramePacked

/-!
# From the native shared scan to each packed vertex

Every subsequent site sees the exact rows, role tags and shared choices
of the accepted bit worker. It also sees the earlier level arrays and the
noncontrol header cells from that worker's input. The two control words
may be rewritten at each site handoff.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM PrivateRAM PairSimulation Compression CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles TerminalLink
open scoped Fin.CommRing

variable {G : Group} {D : DescriptorSpace.Layout} {limit width : ℕ} {roles : List TaggedLayer}
local notation "pub" => terminalOperands G
local notation "H" => vertexHeader G
local notation "size" => tagWords limit roles
local notation "first" => endAddress D
local notation "lo" => endAddress D + tagWords limit roles

/-- A single true shared-bit stage supplies the reference memory for all
subsequent ordinals. Its data include the exact branch bit at every wire. -/
theorem VertexPacked.shared (P : VertexPacked G D limit roles width)
    (workers : TerminalLink.Stage → PairTable) (bank : workers TerminalLink.Stage.sharedBits = ⟨28,5,FinalBits.Worker.table⟩)
    (src phy : Memory G.w) (fuel : ℕ) (clock : 54 ≤ fuel) (bits : Fin width → Bool)
    (layout : FinalBits.Worker.Layout pub src lo width)
    (valid : (Entry.resume TerminalLink.Stage.sharedBits (0 : Word G.w)).Valid H phy)
    (agree : SourceTransport.Agree (workerCell H) src phy)
    (capacity : ∀ l ∈ roles.map TaggedLayer.layer, ∀ i, (l.ids i).length ≤ limit)
    (rows : AllRows G.w src limit first first (roles.map TaggedLayer.layer))
    (tags : Reads G.w src (size+width) limit first roles) :
    let stage := Entry.resume TerminalLink.Stage.sharedBits (0 : Word G.w)
    let raw := FinalBits.Worker.reports pub 0 src bits
    let post := after phy (eventLog (stageReports H stage raw))
    StageRun workers pub fuel stage src phy (FinalBits.calls bits ++ [[]]) raw ∧
      ∀ {ord : ℕ} {m : Memory G.w}, LinkedVertexMemory G post ord m →
        AllRows G.w m limit first first (roles.map TaggedLayer.layer) ∧
        Reads G.w m (size+width) limit first roles ∧
        (∀ i, m (lo+i.val) = PrivateFields.bitValue G.w (bits i)) ∧
        (∀ x, D.base ≤ x → x < first → m x = src x) ∧
        ∀ j : ℕ, 0 < j → j < 31 → m (H+(j : Word G.w)).val = src (H+(j : Word G.w)).val := by
  intro stage raw post
  obtain ⟨run, child, role, stored, lower, upper⟩ := TerminalLayout.linked_vertexMemory workers bank
    pub src phy fuel limit first width roles bits capacity layout P.room P.arena clock valid agree rows tags
  refine ⟨run,fun {ord} {m} frame => ?_⟩
  exact ⟨P.rows frame capacity child,P.roleWords frame role,P.bits frame bits stored,
    fun x hx hx' => (P.directory frame hx hx').trans (lower x hx'),
    fun j hj hj' => (P.header frame j hj hj').trans (upper j hj hj')⟩

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
