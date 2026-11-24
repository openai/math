import OAI.Computability.VPVNP.PairRefreshHalfDecoder

/-!
# Selecting a shrinking node's stored parent argument

The current site's packed packet fixes its full outgoing and incoming half-wire
assignment. Its native parser can therefore use the corresponding typed map jobs
for all field choices on the incoming tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM Compression NodeArguments DFS
open scoped Fin.CommRing

variable {w n a g p r k : ℕ} (Y : State a g) (v : Y.network.Site) (A : Arena)
  (family : Y.network.Half v → HookParser w n)

/-- Read the packed output half at the popped descriptor's actual address. -/
noncomputable def parentParser : HookParser w n where
  read node s bits := (RefreshHalfDecoder.parent Y v A node.val s).bind
    fun z => (family z).read node s bits

theorem parentParser_read (node : Word w) (s : Scratch w n) (z : Y.network.Half v)
    (stored : (Packet.mk node.val (packed Y v z)).Stored A s) (positive : 0 < w)
    (bits : List Bool) :
    (parentParser Y v A family).read node s bits = (family z).read node s bits := by
  simp only [parentParser, RefreshHalfDecoder.parent_eq Y v A node.val s z stored positive,
    Option.bind_some]

/-- A single native parser handles every prepared value of the parent packet,
including distinct independent endpoint assignments at the same physical row. -/
theorem parentParser_exactOn (M : Machine w p r k) (visit ret : Fin p) (dfs : Fin 9 ↪ Fin r)
    (m : Memory w) (positive : 0 < w) (address : ℕ) (ready : Y.network.Half v → Scratch w n → Prop)
    (stored : ∀ z s, ready z s → (Packet.mk address (packed Y v z)).Stored A s)
    (exactAt : ∀ z, (family z).ExactOn (fun node s => node.val = address ∧ ready z s)
      M visit ret dfs m) :
    (parentParser Y v A family).ExactOn (fun node s => node.val = address ∧ ∃ z, ready z s)
      M visit ret dfs m := by
  constructor
  · rintro node s ⟨atRow, z, good⟩ bs job tail hit
    rw [parentParser_read Y v A family node s z (atRow ▸ stored z s good) positive] at hit
    exact (exactAt z).success node s ⟨atRow, good⟩ bs job tail hit
  · rintro node bs c top pending ⟨atRow, z, good⟩ pc reg stack atEnd h5 h6 h3 fail
    rw [parentParser_read Y v A family node _ z (atRow ▸ stored z _ good) positive] at fail
    exact (exactAt z).reject node bs c top pending ⟨atRow, good⟩ pc reg stack atEnd h5 h6 h3 fail

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
