import OAI.Hierarchy.TaggedWireTurnHeader
import OAI.Hierarchy.TaggedWideHost

namespace OAI
/-! # Fixed sparse-turn comparator wired to shared physical pins -/

noncomputable section
namespace Hierarchy.WireTelescope.TurnShelf
open ThreeFlat Routing Tagged
open scoped Classical BigOperators
variable {F : Type*} [Field F] {V : Type} [Fintype V] {N p e r : ℕ}

/-- Each header wire is projected from a fixed observed CPU address. The
barrel aperture is separately wired to the supplied public physical slab. -/
def physical (base : ℕ) (s : Fin N) (bit : ℕ×ℕ→V⊕Bool) (aperture : Aperture p e→V⊕Bool) :
    BitNetwork F (Fintype.card V) :=
  WideHost.localFamily (I:=Unit) (V:=V) (A:=fun _=>Pin r p e) (fun _=>network F r p e)
    (fun _ q=>Sum.elim bit aperture (wire base s q))

theorem physical_bill (base : ℕ) (s : Fin N) (bit : ℕ×ℕ→V⊕Bool) (aperture : Aperture p e→V⊕Bool) :
    let a:=physical (F:=F) (r:=r) base s bit aperture
    a.cells+a.internal≤r*(2308*width p e*(e+p+2)) := by
  intro a
  rw [show a.cells+a.internal=_ from WideHost.localFamily_size ..]
  simpa using size F r p e

theorem physical_value {W : ℕ} (base : ℕ) (s : Fin N) (bit : ℕ×ℕ→V⊕Bool) (aperture : Aperture p e→V⊕Bool)
    (x : V→Bool) (m : Computability.VPVNP.BurstRAM.Memory W)
    (read : ∀ t : Fin r,∀c : Control p e,
      let u:=projection c
      Sum.elim x id (bit (addr base s t u.1,u.2))=(m (addr base s t u.1)).val.testBit u.2) :
    TypedWiring.value (physical (F:=F) (r:=r) base s bit aperture) x =
      TypedWiring.value (network F r p e) (nativeView base s m (Sum.elim x id ∘ aperture)) := by
  rw [physical,WideHost.localFamily_eval,Fintype.prod_unique]
  apply congrArg (TypedWiring.value _)
  funext j
  rcases j with ⟨t,c⟩|a
  · exact read t c
  · rfl

end Hierarchy.WireTelescope.TurnShelf

end
end OAI
