import OAI.Computability.VPVNP.PairShrinkSelectedOccurrence
import OAI.Computability.VPVNP.PairShrinkRoleParent
import OAI.Computability.VPVNP.PairVertexRoleNativeLeaf

/-! # The prepared parent packet at each selected shrinking row -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.RoleDomains

open BurstRAM PrivateRAM Compression CompressorRecords DFS NodeArguments TreeDecode LocalHistory
open TraversalRows TraversalRoles ShrinkRoleDirectory
open scoped Fin.CommRing

attribute [local irreducible] ShrinkRoleDirectory.occurrence

variable {k K : Type*} [Field k] [CommRing K] {S : BlockSchedule k} {B : S.Templates}
    {f : B.Entry → K} {hf : B.IsSolution f}
variable {w endAddr a g : ℕ} (X : State a g) (cap base : ℕ)
    (passes : List (SelectedLevel B f hf)) (R : LeafArena.Regions) (data : Fin 10 → Word w)
    (offset : Word w) (vals : LeafSourceLoad.Static 34 → Word w)
    (hist : Scratch w endAddr → B.Entry → ℕ) (nodeCap limit : ℕ) (x : ShrinkSite passes)

local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "addr₀" => ShrinkRoleDirectory.address cap base (leaf₀) passes x.val
local notation "occ₀" => x.occurrence
local notation "out₀" => Output X cap base passes R data offset vals hist nodeCap limit x.val

/-- The common vertex frame and the decoded parent assignment at the actual
packed output site, with sufficient credit for every label's local increments. -/
structure Parent (z : (occ₀).nextState.network.Half (occ₀).site) (s : Scratch w endAddr) : Prop where
  frame : VertexFrameData R data offset vals s
  credit : ∀ l, hist s l + nodeCap ≤ limit
  fits : (Packet.mk (addr₀) (packed (occ₀).nextState (occ₀).site z)).Fits R.arguments w endAddr
  stored : (Packet.mk (addr₀) (packed (occ₀).nextState (occ₀).site z)).Stored R.arguments s

local notation "par₀" => Parent X cap base passes R data offset vals hist nodeCap limit x

set_option maxHeartbeats 1000000 in
/-- The physical output packet yields the precise independent output half
used by the shrinking kernel, and conversely. -/
theorem output_iff_parent (s : Scratch w endAddr) : out₀ s ↔ ∃ z, par₀ z s := by
  let v := passes[x.val.1]
  let u := x.val.2
  let e := x.occurrence.halves
  have eqn (z : (v.pass.step.term v.term).output.Half u) :
      outputPacket X cap base passes x.val z =
        Packet.mk (addr₀) (packed (occ₀).nextState (occ₀).site (e z)) :=
    congrArg (Packet.mk (addr₀)) (x.occurrence.packed_eq z)
  constructor
  · intro out
    obtain ⟨z,fit,stored⟩ := out.packet
    rw [eqn] at fit stored
    exact ⟨e z,out.frame,out.credit,fit,stored⟩
  · rintro ⟨z,ok⟩
    refine ⟨ok.frame,ok.credit,e.symm z,?_⟩
    rw [eqn,e.apply_symm_apply]
    exact ⟨ok.fits,ok.stored⟩

/-- Each allowed local update has its literal natural value in the word
histogram while this shrinking parent is being processed. -/
theorem Parent.word_add {z : (occ₀).nextState.network.Half (occ₀).site} {s : Scratch w endAddr}
    (parent : par₀ z s) (wordFit : limit < 2^w) (l : B.Entry) (delta : ℕ) (charge : delta ≤ nodeCap) :
    ((hist s l : Word w)+(delta : Word w)).val = hist s l + delta := by
  rw [← Nat.cast_add,Fin.val_natCast]
  exact Nat.mod_eq_of_lt ((Nat.add_le_add_left charge _).trans (parent.credit l) |>.trans_lt wordFit)

/-- At this particular output row the physical decoder recovers exactly the
parent half consumed by its native map-and-child subroutine. -/
theorem parent_exact {p r k' : ℕ} (M : Machine w p r k') (visit ret : Fin p)
    (dfs : Fin 9 ↪ Fin r) (m : Memory w) (positive : 0 < w)
    (family : (occ₀).nextState.network.Half (occ₀).site → HookParser w endAddr)
    (checked : ∀ z, (family z).ExactOn (fun node s => node.val = (addr₀) ∧ par₀ z s) M visit ret dfs m) :
    (ShrinkRole.parentParser (occ₀).nextState (occ₀).site R.arguments family).ExactOn
      (fun node s => node.val = (addr₀) ∧ out₀ s) M visit ret dfs m :=
  restrict (ShrinkRole.parentParser_exactOn (occ₀).nextState (occ₀).site R.arguments family M visit ret dfs m
    positive (addr₀) (par₀) (fun _ _ h => h.stored) checked) fun _ s h =>
      ⟨h.1,(output_iff_parent X cap base passes R data offset vals hist nodeCap limit x s).mp h.2⟩

end PairSimulation.VertexImage.RoleDomains

end VPVNP
end Computability
end OAI
