import OAI.Hierarchy.TaggedWireNamedAperture

namespace OAI
/-! # Transport of the original role bits into an equal physical width family -/

noncomputable section
namespace Hierarchy.WireTelescope.NamedAperture
open LinearAlgebra.SpectralBooks ChordGraph CalendarTape AdaptiveProbe
open scoped Classical

theorem rowBits_transport {K n : ℕ} (ends : Fin n→Chord K) (bits : Fin n→ℕ) {B : Widths K}
    (same : installedWidths ends bits=B) {s : Fin K} (x : State B s) (p : (bitGraph (rowGraph ends) bits).Port s) :
    rowBits ends bits (cast (congrArg (fun U=>State U s) same.symm) x) p=
      siteBits B s x (transportAt same (atPort ends bits p)) := by
  subst B
  exact rowBits_siteBits ends bits x p

end Hierarchy.WireTelescope.NamedAperture

end
end OAI
