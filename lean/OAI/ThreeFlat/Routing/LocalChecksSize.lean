import OAI.ThreeFlat.Routing.LocalChecks

namespace OAI
namespace ThreeFlat.Routing.LocalChecks

open scoped Classical

/-- Internal bits consist of the shared certificate and the internal prefix flags of each local table. -/
theorem internal_le_shared_add_cells {P H G F : Type*} [Fintype P] [Fintype H] [Fintype G]
    [Zero F] [One F] (port : G → Type*) [∀ g, Fintype (port g)]
    (wire : ∀ g, port g → P ⊕ H) (test : ∀ g, (port g → Bool) → Prop) :
    (network (F := F) port wire test).internal ≤ Fintype.card H + (network (F := F) port wire test).cells := by
  simp only [network,TypedWiring.glue_internal,TypedWiring.glue_cells]
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro g _
  simp only [TypedWiring.localTable,TableCompiler.localTableNetwork_internal,TableCompiler.localTableNetwork_cells]
  gcongr; omega

end ThreeFlat.Routing.LocalChecks

end OAI
