import OAI.Hierarchy.GridLensWireBudget

namespace OAI
/-! # Reading a geometric certificate from physical wire labels -/

namespace Hierarchy.GridLens
noncomputable section

variable {k n E : ℕ}

/-- The legal geometric origins of an equality or catalyst charge. A segment may
be a focus link, an interior crossing, or one half of a passage. A `through` charge
uses both halves of the designated passage. Stationary operations may be repeated. -/
inductive WireRoute (k n E : ℕ)
  | stationary (site : EuclideanSpace ℝ (Fin k))
  | segment (rail : Fin E) (part : Segment n) (reverse : Bool)
  | through (rail : Fin E) (index : Fin (n+1)) (reverse : Bool)

namespace WireRoute

variable (direction : Fin E → Fin k) (row : Fin E → Fin k → Fin (n+1)) (R : ℝ)

/-- The physical sites to which the two wires of the test must be attached. -/
def site : WireRoute k n E → Bool → EuclideanSpace ℝ (Fin k)
  | .stationary x, _ => x
  | .segment e s r, b => segmentEnd (direction e) (row e) R s (if r then !b else b)
  | .through e t r, b => cellPort (cellOnRail (direction e) (row e) t) (direction e) (if r then !b else b)

/-- The waypoint of a through wire is its cell center. -/
def via : WireRoute k n E → EuclideanSpace ℝ (Fin k)
  | .stationary x => x
  | .segment e s r => segmentEnd (direction e) (row e) R s (!r)
  | .through e t _ => cellCenter (cellOnRail (direction e) (row e) t)

/-- The physical slots consumed by each leg, before any distance is taken. -/
def slot : WireRoute k n E → Bool → Option (Fin E × Segment n)
  | .stationary _, _ => none
  | .segment e s _, b => if b then none else some (e,s)
  | .through e t r, b => some (e, .inr (t, if r then !b else b))

/-- Disjoint labels and pointwise attachment of the measured ports are sufficient
for the full geometric certificate. No arithmetic on distances is an input. -/
def certificate {A : Type*} (ends : A → Bool → EuclideanSpace ℝ (Fin k))
    (route : A → WireRoute k n E)
    (attached : ∀ a b, ends a b = site direction row R (route a) b)
    (distinct : ∀ {i i' : A × Bool} {z}, slot (route i.1) i.2 = some z →
      slot (route i'.1) i'.2 = some z → i = i') : PathCertificate direction row R ends := by
  refine ⟨fun a => via direction row R (route a), fun i => slot (route i.1) i.2, distinct, ?_⟩
  rintro ⟨a,b⟩
  simp only [legSite, attached]
  cases h : route a with
  | stationary x => cases b <;> simp [slot, site, via]
  | segment e s r => cases b <;> cases r <;> simp [slot, site, via]
  | through e t r => cases b <;> cases r <;> simp [slot, site, via, segmentEnd]

end WireRoute
end
end Hierarchy.GridLens

end OAI
