import OAI.Computability.NearSquareRoot.CRTControlledElementaryRun
import OAI.Computability.IntegerMultiplication.Strip.Bearing

/-! # Linear preparation and collection of complete row packets

A single global header supplies the rulers for carving the flat payload into rows.
A second header computation emits one local header per row in physical order.
Shared data can be copied into those local headers before the row kernel runs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip

variable {X : Type} {P B : X → Type} {w : X → ℝ} {header shared : X → Tree}
variable (s : (x : X) → Series (P x)) (t : (x : X) → Series (B x))
variable (f : (x : X) → P x × B x → Tree)

/-- Broadcast the shared field computed from the global header across all row
headers, charging its whole copied size. -/
theorem sharedRowHeaders
    (ruler : Carries w header (fun x => send (tally (s x).count)))
    (getShared : Carries w header shared)
    (copies : ∃ K : ℕ, ∀ x, ((s x).count + 1 : ℝ) * (shared x).count ≤ (K : ℝ) * w x) :
    Carries w header (stackRun s fun x _ => shared x) :=
  Strip.spread s shared (ruler.twice getShared) copies

/-- Attach the shared descriptor to each individually generated row marker. -/
theorem prefixRowHeaders (marker : (x : X) → P x → Tree)
    (ruler : Carries w header (fun x => send (tally (s x).count)))
    (getShared : Carries w header shared)
    (copies : ∃ K : ℕ, ∀ x, ((s x).count + 1 : ℝ) * (shared x).count ≤ (K : ℝ) * w x)
    (markers : Carries w header (stackRun s marker)) :
    Carries w header (stackRun s fun x a => Tree.fork (shared x) (marker x a)) :=
  Strip.coalesce s _ _ (sharedRowHeaders s ruler getShared copies) markers

/-- Carve a flat cartesian payload and attach the local headers obtained from
the actual global header. The array of records is arbitrary. -/
theorem prepareRowPackets {rowHead : (x : X) → P x → Tree}
    (dims : Carries w header (fun x => rulers (s x) (t x)))
    (emitted : Carries w header (stackRun s rowHead))
    (geometry : ∃ K : ℕ, ∀ x,
      ((s x).count + 1 : ℝ) * ((t x).count + 1) ≤ (K : ℝ) * w x)
    (dataVol : Volume w (stackRun (fun x => (s x).cart (t x)) f)) :
    Carries w (together header (stackRun (fun x => (s x).cart (t x)) f))
      (stackRun s fun x a => Tree.fork (rowHead x a) (stripe (t x) fun b => f x (a,b))) := by
  have getHeader := Carries.dropRight dims.budget dims.small dataVol
  have getData := Carries.dropLeft dims.budget dims.small dataVol
  exact Strip.coalesce s _ _ (getHeader.chain emitted)
    (Strip.carve s t f getData (getHeader.chain dims) geometry)

/-- Concatenate the resulting row forests in physical order. -/
theorem collectRowPackets (positive : ∀ x, 1 ≤ w x)
    (nestedVol : Volume w (stackRun s fun x a => stripe (t x) fun b => f x (a,b))) :
    Carries w (stackRun s fun x a => stripe (t x) fun b => f x (a,b))
      (stackRun (fun x => (s x).cart (t x)) f) :=
  Strip.flatten s t f (Carries.idles positive nestedVol)

end Controlled

end NearSquareRoot
end Computability
end OAI
