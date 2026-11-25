import OAI.Computability.BorderVNP.DiagonalCalendarRoutedAt

/-! # Retaining the returned sites of a selected routing frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

/-- The physical sites witnessing the same checked inputs used by the route
decoder, together with their original reached report states. -/
structure CheckedRouteReadback {A : Type} {P : Prop} {Q : Sort*} (route : A → P → Q)
    (W : A → Sort*) (reached : (a : A) → W a → Prop) where
  /-- The actual frame family and validated public declarations. -/
  inputs : CheckedRouteInputs route
  /-- The concrete publication sites on those exact frames. -/
  sites : W inputs.sites
  /-- The readback property proved for those exact sites. -/
  returned : reached inputs.sites sites

/-- Choose the installed frames and their authentic sites simultaneously. -/
noncomputable def CheckedRouteReadback.ofReturns {A : Type} {P : Prop} {Q : Sort*}
    (route : A → P → Q) {W : A → Sort*} {reached : (a : A) → W a → Prop}
    (frames : ∃ a, ∃ sites : W a, reached a sites) (checks : P) : CheckedRouteReadback route W reached :=
  ⟨⟨frames.choose,checks⟩,frames.choose_spec.choose,frames.choose_spec.choose_spec⟩

end Diagonal

end BorderVNP
end Computability
end OAI
