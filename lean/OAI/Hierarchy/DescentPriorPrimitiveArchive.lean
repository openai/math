import OAI.Hierarchy.DescentResetTerminalRegisterLayout
import OAI.Hierarchy.DescentInitialRolePages
import OAI.Hierarchy.DescentSeedTokenStartup
import OAI.Hierarchy.DescentDatedPrimitiveExtent
import OAI.Hierarchy.DescentDatedOrdinaryCountRoof
import OAI.Hierarchy.DescentPrimitiveCheckpointShape
import OAI.Hierarchy.DescentDatedResetOutput

namespace OAI
/-! The carried primitive label register has a fixed physical bank on every issuing date. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM
noncomputable section

namespace PriorRolePages
open DescentInitialHost DescentSeedRoot DescentPackedSeed DescentDatedSeedStartup DescentCompiler
theorem initial_pages {F : Type} [Field F] {c p : ℕ} (X : Catalyst.Approximation F c p)
    (R s payload k H G M base : ℕ) :
    let v:=initial X R s payload k H G M base
    v.endAddress=DescentDatedSeedStartup.Primitive.initialEnd X R s payload k H G M base ∧
      ∀ x : Fin (2^k),v.bank x.val=DescentDatedSeedStartup.Primitive.page X R s payload k H G M base x:=
  ⟨rfl,fun _=>rfl⟩

def ordinary {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) : PriorRolePages:=
  let start:=v.primitiveFirst (v.operandEnd floor)
  let d:=v.paletteShape.durable
  ⟨d.output (v.paletteShape.durableStart start),d.rows,Nat.clog 2 (d.rows+1),d.blocks⟩
theorem ordinary_pages {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) :
    (ordinary v floor).endAddress=v.primitiveRoof (v.operandEnd floor) ∧
      ∀ x : Fin (2^v.reference.k),(ordinary v floor).bank x.val=v.primitiveBank (v.operandEnd floor) x:=
  ⟨rfl,fun _=>rfl⟩

theorem reset_pages (v : ResetOutput) (base : ℕ) :
    (reset v base).endAddress=v.primitiveEnd base ∧
      ∀x:Fin v.primitive.chart.blocks,(reset v base).bank x.val=v.primitive.bank (v.birthEnd base) x:=
  ⟨rfl,fun _=>rfl⟩

end PriorRolePages
end
end Hierarchy.DescentDatedAddressBook

end OAI
