import OAI.Computability.VPVNP.DegreeRefreshMotif

/-!
# Reading the incident external wires of a bundle matching

When an arc matching sends whole bundles to whole bundles, the incoming
segments at a port all come from one external wire. Their offsets are still
determined by their order within the original source bundle.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.Refresh

variable {B : Type*} {d : ℕ}

private def readBundleSegment (w : Arc B d → ℕ) (a : Arc B d) {b : B × Fin d}
    (hab : a.1 = b) (word : Word (∑ j, w (b,j))) : Word (w a) := by
  subst b
  exact fun k ↦ word (finSigmaFinEquiv (n := fun j ↦ w (a.1,j)) ⟨a.2,k⟩)

private theorem readBundleSegment_external (w : Arc B d → ℕ) (z : External w)
    (a : Arc B d) {b : B × Fin d} (hab : a.1 = b) :
    readBundleSegment w a hab (z b) = segment w z a := by
  subst b
  rfl

/-- Read all segments at a port using just the two external half-wires there.
The inverse matching recovers each incoming segment's source-port index. -/
def incidentPortSegments (t : Equiv.Perm (Arc B d)) (target : Equiv.Perm (B × Fin d))
    (h : ∀ a : Arc B d, (t a).1 = target a.1) (w : Arc B d → ℕ) (p : B × Fin d)
    (outWord : Word (∑ j, w (p,j))) (inWord : Word (∑ j, w (target.symm p,j))) :
    PortSegments t w p.1 p.2 :=
  (fun j ↦ readBundleSegment w (p,j) rfl outWord, fun j ↦
    readBundleSegment w (t.symm (p,j)) (by
      apply target.injective
      rw [← h, t.apply_symm_apply, target.apply_symm_apply]) inWord)

/-- On a global assignment of external words the local reader agrees with
direct extraction from each arc's original bundle. -/
@[simp] theorem incidentPortSegments_external (t : Equiv.Perm (Arc B d))
    (target : Equiv.Perm (B × Fin d)) (h : ∀ a : Arc B d, (t a).1 = target a.1)
    (w : Arc B d → ℕ) (p : B × Fin d) (z : External w) :
    incidentPortSegments t target h w p (z p) (z (target.symm p)) =
      portSegments t w z p.1 p.2 := by
  apply Prod.ext
  · rfl
  · funext j
    exact readBundleSegment_external w z _ _

end Compression.Refresh

end VPVNP
end Computability
end OAI
