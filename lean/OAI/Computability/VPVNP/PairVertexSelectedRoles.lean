import OAI.Computability.VPVNP.PairVertexActiveOccurrence
import OAI.Computability.VPVNP.PairVertexFrameData
import OAI.Computability.VPVNP.PairSelectedPacketFormat

/-! # Dispatching the three installed handlers on true selected packets -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM Compression DFS LocalHistory NodeArguments TraversalRows TreeDecode
open CompressorRecords SourceTransport LeafSourceLoad NetworkKernel
open scoped Fin.CommRing
open private collected_checks from OAI.Computability.VPVNP.PairSelectedLevelChecks

variable {w endAddr : ℕ}

/-- The physical role tag chooses the local input condition at this
descriptor address. All three choices share the initialized geometry bank. -/
def roleDomain (R : LeafArena.Regions) (data : Fin 10 → Word w) (offset : Word w) (vals : Static 34 → Word w)
    (domains : NodeDispatch.Role → Word w → Scratch w endAddr → Prop) (m : Memory w)
    (node : Word w) (saved : Scratch w endAddr) : Prop :=
  VertexFrameData R data offset vals saved ∧ domains (NodeDispatch.role (m (offset+node).val)) node saved

private theorem exactOn_mono {p r k : ℕ} {M : Machine w p r k} {pc ret : Fin p} {regs : Fin 9 ↪ Fin r}
    {m : Memory w} {domain domain' : Word w → Scratch w endAddr → Prop} {hook : HookParser w endAddr}
    (checked : hook.ExactOn domain M pc ret regs m) (small : ∀ a s, domain' a s → domain a s) :
    hook.ExactOn domain' M pc ret regs m where
  success a s h := checked.success a s (small _ _ h)
  reject a bits c top pending h := checked.reject a bits c top pending (small _ _ h)

variable {k K : Type*} [Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (κ : B.Entry → K) (hκ : B.IsSolution κ) {lanes : ℕ}
    (T : ℕ) (hT : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute κ hκ T hT X).Choices) (rowBase : ℕ)
    {geometry rootFields leaf shrink refresh : Segment} {p r g : ℕ}
    (A : Placement (segments geometry rootFields leaf shrink refresh) p r) (M : Machine w p r 11)
    (m : Memory w) (R : LeafArena.Regions) (offset : Word w) (data : Fin 10 → Word w) (vals : Static 34 → Word w)
    (order : Fin g ≃ B.Entry) (P : SiteParsers κ X.network) (desc : ℕ → List ℕ) (nodeCap limit : ℕ)
    (handlers : NodeDispatch.Role → HookParser w endAddr) (domains : NodeDispatch.Role → Word w → Scratch w endAddr → Prop)
    (cost : VisitPath w endAddr → Prop)

local notation "head₀" => TerminalLink.header (Machine.publicData M)
local notation "stable₀" => VertexFrameData R data offset vals
local notation "format₀" => SelectedPacketFormat B κ hκ T hT X z rowBase
local notation "hist₀" => privateHistogram order (LeafArena.Regions.histBase R)
local notation "valid₀" => Budgeted R.arguments (format₀) (stable₀) desc (hist₀) nodeCap limit
local notation "domain₀" => roleDomain R data offset vals domains m
local notation "hook₀" => dispatcher handlers m offset
local notation "guard₀" => JobGuard A M m (TerminalLink.workerCell (head₀)) cost
local notation "leaves₀" => sitePointers B.recordLimit rowBase (siteOrder X)
local notation "leafPackets₀" => (fun u y => Packet.mk (Prod.fst ((leaves₀) u)) (packed X u y))

/-- Exact local role runs at each genuine typed row supply all forward and
inverse obligations for the ascending worker. A role may reject on any
suffix or input half-buffer permitted by its own prepared row. -/
theorem SelectedChecks.ofRoleRows
    (ready : ∀ (q : Packet) s, stable₀ s → format₀ q → q.Fits R.arguments w endAddr → q.Stored R.arguments s →
      (∀ l, hist₀ s l + nodeCap ≤ limit) → domains (NodeDispatch.role (m (offset+(q.node : Word w)).val)) (q.node : Word w) s)
    (roleRuns : ∀ role, (handlers role).ExactOn (domains role) M (A.entry (rolePart role)) (A.dfsPC 3) A.dfs m)
    (cursor : Subtrees (hook₀) (valid₀) P (fun u => leafTree ((leaves₀) u)) (leafPackets₀) ∧
      Emits (valid₀) (hist₀) (guard₀) P (leafPackets₀) (leafJobs P (leaves₀)))
    (levels : let passes := executeLevels B κ hκ T hT X z
      let tags := TraversalRoles.selected B κ hκ T hT X z
      ∀ i : Fin passes.length, LevelChecks B κ hκ (hook₀) (valid₀) (hist₀) (guard₀) B.recordLimit
        (TraversalRoles.layerBase B.recordLimit rowBase tags i.val) passes[i]) :
    SelectedChecks B κ hκ T hT X z rowBase A M m ((NativeFrame.frameBase R : ℕ) : Word w) offset
      R.histBase order P (valid₀) (domain₀) handlers cost := by
  refine ⟨fun _ _ h => h.1.resident,fun _ h => h.frontier.frame.resident,
    budgeted_headDomain _ (fun q s frame type fits stored room => ⟨frame,ready q s frame type fits stored room⟩),
    ?_,cursor.1,cursor.2,?_⟩
  · intro role
    exact exactOn_mono (roleRuns role) (fun _ _ h => h.2 ▸ h.1.2)
  · let E := B.execute κ hκ T hT X
    let readers := repeatReaders (blockReaders B κ hκ) _ T lanes (Nat.add_sub_of_le hT).symm X
    let origins := executeOrigins B κ hκ T hT X
    exact collected_checks B κ hκ (hook₀) (valid₀) (hist₀) (guard₀) E _ readers origins (B.records κ hκ T hT X)
      z B.recordLimit rowBase (execute_originReaders B κ hκ T hT X)
      (selected_indexed B κ hκ (hook₀) (valid₀) (hist₀) (guard₀) T hT X z rowBase levels)

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
