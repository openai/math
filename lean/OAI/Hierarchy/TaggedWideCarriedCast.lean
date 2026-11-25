import OAI.Hierarchy.TaggedWidePassApertures

namespace OAI
/-! # Reindexing a live source bit through its true chronological width equality -/
noncomputable section
namespace Hierarchy.Tagged.PassiveWindow
open AdaptiveProbe WireTelescope NamedAperture
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical
variable {S n cap : ℕ} {A : Type} (ends : Fin n→Chord S) (bits : Fin n→ℕ) (s : Fin S)
    (room : ∀i,bits i≤cap) (slot : EndsAt ends bits s ↪ A)
    {U V : Widths S} (shape : installedWidths ends bits=U)
local notation "base" => carried ends bits s room slot shape
local notation "atWidth" eq => carried ends bits s room slot (shape.trans eq)

theorem carried_cast_read (x : State U s) (get : A→Fin cap→Bool)
    (read : ∀i p,(base).owner i=some p→∀u:Fin ((base).width i),
      get i (u.castLE ((base).within i))=(x p).val.testBit ((base).base i+u.val))
    (eq : U=V) :
    ∀i p,(atWidth eq).owner i=some p→∀u:Fin ((atWidth eq).width i),
      get i (u.castLE ((atWidth eq).within i))=
        ((cast (congrArg (fun T=>State T s) eq) x) p).val.testBit ((atWidth eq).base i+u.val) := by
  subst V
  exact read

end Hierarchy.Tagged.PassiveWindow
end

end OAI
