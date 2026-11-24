import OAI.Computability.VPVNP.PairSelectedPacketFormat
import OAI.Computability.VPVNP.PairVertexFrameData

/-!
# Physical domains at the three vertex entries

A popped packet supplies its own independent half assignment. Its address
and the published role word identify the original cursor or the selected
output occurrence. The latter carries the current histogram headroom into
the shrinking or refresh reader.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.RoleDomains

open BurstRAM DFS TreeDecode NodeArguments Compression TraversalRows TraversalRoles CompressorRecords LocalHistory

open scoped Fin.CommRing

variable {k K : Type*} [Field k] [CommRing K] {S : BlockSchedule k} {B : S.Templates}
    {f : B.Entry → K} {hf : B.IsSolution f}
variable {w endAddr a g : ℕ} (X : State a g) (cap base : ℕ)
    (passes : List (SelectedLevel B f hf)) (R : LeafArena.Regions) (data : Fin 10 → Word w)
    (offset : Word w) (vals : LeafSourceLoad.Static 34 → Word w)
    (hist : Scratch w endAddr → B.Entry → ℕ) (nodeCap limit : ℕ)

local notation "leaf₀" => (TaggedLayer.mk (leafLayer (siteOrder X)) TraversalRoles.Role.cursor)
local notation "tags₀" => (leaf₀) :: ShrinkRoleDirectory.outputTags passes
local notation "stable₀" => VertexFrameData R data offset vals

/-- The literal output packet of a selected chronological row. -/
noncomputable def outputPacket (x : ShrinkRoleDirectory.Site passes)
    (z : (passes[x.1].pass.step.term passes[x.1].term).output.Half x.2) : Packet :=
  ⟨ShrinkRoleDirectory.address cap base (leaf₀) passes x,
    pullBits (passes[x.1].pass.output_eq passes[x.1].term) (packed (passes[x.1].pass.next passes[x.1].term)) x.2 z⟩

/-- The saved frame, local counter credit and independently stored half fields
at a selected output row. -/
structure Output (x : ShrinkRoleDirectory.Site passes) (s : Scratch w endAddr) : Prop where
  frame : stable₀ s
  credit : ∀ l, hist s l + nodeCap ≤ limit
  packet : ∃ z, (outputPacket X cap base passes x z).Fits R.arguments w endAddr ∧
    (outputPacket X cap base passes x z).Stored R.arguments s

/-- A cursor address with its actual original half assignment and physical
private-memory representation. -/
structure Leaf (node : Word w) (s : Scratch w endAddr) : Prop where
  within : node.val < R.nodes
  frame : stable₀ s
  packet : ∃ (v : X.network.Site) (z : X.network.Half v),
    let q := Packet.mk (sitePointers cap base (siteOrder X) v).1 (packed X v z)
    node.val = q.node ∧ q.Fits R.arguments w endAddr ∧ q.Stored R.arguments s

local notation "out₀" => Output X cap base passes R data offset vals hist nodeCap limit

/-- The input domain of each native role at this physical vertex. -/
def Domain : NodeDispatch.Role → Word w → Scratch w endAddr → Prop
  | .leaf => Leaf X cap base R data offset vals
  | .shrink => ShrinkRoleDirectory.Domain cap base (leaf₀) passes fun x s => out₀ x.val s
  | .refresh => fun node s => ∃ x : ShrinkRoleDirectory.Site passes,
    tagLevel B f hf passes[x.1] = .refresh ∧ node.val = ShrinkRoleDirectory.address cap base (leaf₀) passes x ∧ out₀ x s

private theorem output_role (v : SelectedLevel B f hf) :
    tagLevel B f hf v = .shrink ∨ tagLevel B f hf v = .refresh := by
  rcases v with ⟨_,_,_,_,_,_,origin,_,_⟩
  cases origin <;> simp [tagLevel,ofOrigin]

/-- Reading the physical tag at the popped address always produces its
corresponding typed domain, including on arbitrary later choice tapes. -/
theorem domainsReady (m : Memory w)
    (tags : TraversalRoles.Reads w m offset.val cap base (tags₀))
    (codes : 2 < 2^w) (fit : offset.val+base+tagWords cap (tags₀) ≤ 2^w)
    (nodes : base+tagWords cap (tags₀) ≤ R.nodes)
    (q : Packet) (s : Scratch w endAddr) (frame : stable₀ s)
    (typed : PacketFormat X cap base (leaf₀) passes q)
    (fits : q.Fits R.arguments w endAddr) (stored : q.Stored R.arguments s)
    (credit : ∀ l, hist s l + nodeCap ≤ limit) :
    Domain X cap base passes R data offset vals hist nodeCap limit
      (NodeDispatch.role (m (offset+(q.node : Word w)).val)) (q.node : Word w) s := by
  have len : (tags₀).length = passes.length+1 := by simp [ShrinkRoleDirectory.outputTags]
  have bound := typed.node_lt (by rfl)
  rw [← len,layerBase,List.take_length] at bound
  change q.node < base + tagWords cap (tags₀) at bound
  have room : offset.val+q.node < 2^w := by omega
  have nodeFit : (q.node : Word w).val = q.node := Nat.mod_eq_of_lt (by omega)
  have offsetWord : (offset.val : Word w) = offset := Fin.ext (Nat.mod_eq_of_lt offset.isLt)
  rcases typed.cases with ⟨v,z,eqn⟩ | ⟨x,z,eqn⟩
  · subst q
    have tag := tags.1 ((siteOrder X).entries.symm v)
    change m (offset.val + (sitePointers cap base (siteOrder X) v).1) = 0 at tag
    have role : NodeDispatch.role (m (offset+(((sitePointers cap base (siteOrder X) v).1 : ℕ) : Word w)).val) = .leaf := by
      rw [← offsetWord,probe_word_add _ _ m room,tag]; rfl
    rw [role]
    exact ⟨by rw [nodeFit]; exact bound.trans_le nodes,frame,v,z,nodeFit,fits,stored⟩
  · subst q
    have tag := ShrinkRoleDirectory.dispatch_at_site cap base (leaf₀) passes tags codes fit
      ((ShrinkRoleDirectory.address cap base (leaf₀) passes x : ℕ) : Word w) x nodeFit
    rw [offsetWord] at tag
    rw [tag]
    have ready : out₀ x s := ⟨frame,credit,z,fits,stored⟩
    rcases output_role passes[x.1] with shrink | refresh
    · rw [shrink]; exact ⟨⟨x,shrink⟩,nodeFit,ready⟩
    · rw [refresh]; exact ⟨x,refresh,nodeFit,ready⟩

end PairSimulation.VertexImage.RoleDomains

end VPVNP
end Computability
end OAI
