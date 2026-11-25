import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarTreeNames

/-! # Parent edges and child order from numbered ports

At each nonroot the least port leading closer to the root fixes the parent
edge. The port at its other end gives the child's place in the parent's
local order. Both ends retain their wire and orientation, including on
graphs with loops and parallel wires.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

open scoped Classical

variable {V E : Type*} (G : PortGraph V E)

/-- The port of the same wire at its opposite end. -/
def reversePort {v : V} (p : G.Port v) : G.Port (otherEnd G p) :=
  ⟨(p.val.1, !p.val.2), rfl⟩

@[simp] theorem otherEnd_reversePort {v : V} (p : G.Port v) :
    otherEnd G (reversePort G p) = v := by
  simpa [otherEnd, reversePort] using p.property

variable (portNum : (v : V) → G.Port v → ℕ)
  (hinj : ∀ v, Function.Injective (portNum v)) {r : V} {d : V → ℕ}
  (hd : DistanceChecks (underlying G.tail G.head) r d)

/-- The port with the least number among those leading toward the root. -/
noncomputable def canonicalParentPort (v : V) (hv : v ≠ r) : G.Port v :=
  (existsUnique_parentPort G portNum hinj hd v hv).choose

theorem canonicalParentPort_spec (v : V) (hv : v ≠ r) :
    IsParentPort G portNum d v (canonicalParentPort G portNum hinj hd v hv) :=
  (existsUnique_parentPort G portNum hinj hd v hv).choose_spec.1

theorem eq_canonicalParentPort (v : V) (hv : v ≠ r) (p : G.Port v)
    (hp : IsParentPort G portNum d v p) : p = canonicalParentPort G portNum hinj hd v hv :=
  (existsUnique_parentPort G portNum hinj hd v hv).choose_spec.2 p hp

/-- Follow the canonical port toward the root; the root is its own parent. -/
noncomputable def canonicalParent (v : V) : V :=
  if hv : v ≠ r then otherEnd G (canonicalParentPort G portNum hinj hd v hv) else r

@[simp] theorem canonicalParent_root : canonicalParent G portNum hinj hd r = r := by
  simp [canonicalParent]

theorem canonicalParent_eq_otherEnd (v : V) (hv : v ≠ r) :
    canonicalParent G portNum hinj hd v =
      otherEnd G (canonicalParentPort G portNum hinj hd v hv) := by
  simp [canonicalParent, hv]

theorem canonicalParent_depth_lt (v : V) (hv : v ≠ r) :
    d (canonicalParent G portNum hinj hd v) < d v := by
  rw [canonicalParent_eq_otherEnd G portNum hinj hd v hv]
  exact (canonicalParentPort_spec G portNum hinj hd v hv).1

/-- A child's slot is numbered at its parent. The root has no sibling order
to participate in and is assigned zero. -/
noncomputable def canonicalSiblingSlot (v : V) : ℕ :=
  if hv : v ≠ r then
    portNum _ (reversePort G (canonicalParentPort G portNum hinj hd v hv))
  else 0

theorem canonicalSiblingSlot_eq (v : V) (hv : v ≠ r) :
    canonicalSiblingSlot G portNum hinj hd v =
      portNum _ (reversePort G (canonicalParentPort G portNum hinj hd v hv)) := by
  simp [canonicalSiblingSlot, hv]

include hinj in
private theorem otherEnd_eq_of_number_eq {s t : V} (p : G.Port s) (q : G.Port t)
    (hst : s = t) (hn : portNum s p = portNum t q) : otherEnd G p = otherEnd G q := by
  subst t
  exact congrArg (otherEnd G) (hinj s hn)

/-- Distinct children of one parent occupy distinct positions in its port order. -/
theorem canonicalSiblingSlot_injective {v w : V} (hv : v ≠ r) (hw : w ≠ r)
    (hp : canonicalParent G portNum hinj hd v = canonicalParent G portNum hinj hd w)
    (hs : canonicalSiblingSlot G portNum hinj hd v = canonicalSiblingSlot G portNum hinj hd w) :
    v = w := by
  rw [canonicalParent_eq_otherEnd G portNum hinj hd v hv,
    canonicalParent_eq_otherEnd G portNum hinj hd w hw] at hp
  rw [canonicalSiblingSlot_eq G portNum hinj hd v hv,
    canonicalSiblingSlot_eq G portNum hinj hd w hw] at hs
  simpa only [otherEnd_reversePort] using
    otherEnd_eq_of_number_eq G portNum hinj
      (reversePort G (canonicalParentPort G portNum hinj hd v hv))
      (reversePort G (canonicalParentPort G portNum hinj hd w hw)) hp hs

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
