import OAI.Computability.VPVNP.PairShrinkCanonicalJob
import OAI.Computability.VPVNP.PairShrinkSelectedCapacity

/-!
# Child and parent packet intervals of a canonical resident shrinking job

Every selected old or new node before the row end has a private argument
interval ending before the histogram. Its packed half-wire bits fit the
argument stride. The histogram, cache and stacks all precede staging.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCanonicalJob

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords NodeArguments
open ShrinkCallCapacity ShrinkCallFields

variable {a g w endAddr n : ℕ} {U : Type*}
variable (Z : State a g) (site : Z.network.Site) (parent : Z.network.Half site)
variable (oldNode : U → ℕ) (node degree rowEnd labels : ℕ) (s : Scratch)
local notation "G" => TerminalLayout.privateRegions degree n rowEnd labels
local notation "ports" => Fintype.card LeafStartup.ScalarPort
local notation "parentPacket" => Packet.mk node (packed Z site parent)

/-- Numerical packet premises of the gather at its published node addresses.
The stack boundary may be any address up to the live length. -/
theorem packet_bounds (stack : endAddr ≤ n) (children : ∀ u, oldNode u < rowEnd)
    (newNode : node < rowEnd) (degreeBound : 2 ^ a ≤ degree) (width : Z.maxWireWidth ≤ n)
    (wordFit : mapBase G ports n < 2 ^ w) (hidden : mapBase G ports n = s.hidden) :
    (∀ u, (G).arguments.base (oldNode u) + (G).arguments.stride ≤ s.staging) ∧
      (parentPacket).Fits (G).arguments w endAddr ∧
        (G).arguments.base node + (parentPacket).bits.length ≤ s.staging := by
  have hist : (G).histBase ≤ mapBase G ports n :=
    (Nat.le_add_right ..).trans (histogram_before G ports n)
  have staging : mapBase G ports n ≤ s.staging := hidden ▸ Nat.le_add_right ..
  have parentSize : (parentPacket).bits.length ≤ (G).arguments.stride :=
    (packed_length_le Z site parent).trans
      ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 degreeBound) width).trans (Nat.le_succ _))
  have parentBefore : (G).arguments.base node + (parentPacket).bits.length ≤ mapBase G ports n :=
    (Nat.add_le_add_left parentSize _).trans (((G).node_before newNode).trans hist)
  exact ⟨fun u ↦ ((G).node_before (children u)).trans (hist.trans staging),
    ⟨stack.trans (Nat.le_add_right ..), parentSize, parentBefore.trans wordFit.le⟩,
    parentBefore.trans staging⟩

end PairSimulation.ShrinkCanonicalJob

end VPVNP
end Computability
end OAI
