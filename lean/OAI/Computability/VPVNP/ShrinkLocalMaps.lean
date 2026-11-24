import OAI.Computability.VPVNP.ShrinkRoles
import OAI.Computability.VPVNP.ShrinkConversion
import OAI.Computability.VPVNP.SlotDemandLocal

/-!
# Demand rows of the six maps at their packed sites

A and B read their respective slices of the old bundle from whole vertex
factors placed at their sites. C and D read the two ends of their old wire,
including the reversal when its source is thick. The resulting matrix row
indices agree with the global demand indices used in the conversion identity.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

open ShrinkMotif NetworkKernel MotifDemandPadding RAMSerialization

variable {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

variable (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering) (order : P.ThickNumbering)
variable (w : Arc V H Tag L d c → ℕ) (l : Bool)

/-- Use the coordinates of the old packed site to access its placed old factors. -/
def shrinkPlacedHalf (s : Site V Tag L) {v : (V × Tag) × L} (hv : v = packedSiteEquiv s)
    (x : Placed (P.shrinkPlace l) (P.oldWireNetwork w).Half v) :
    P.PlacedHalf w l s :=
  fun u h ↦ x u (hv.trans (congrArg packedSiteEquiv h))

/-- Each party reads only the demand coordinates located at its own site. -/
def shrinkLocalDemandArg (m : P.Motif) (j : Fin 6)
    (x : Placed (P.shrinkPlace l) (P.oldWireNetwork w).Half (P.shrinkPartySite l m j)) :
    HalfBits demandSource demandTarget (P.shrinkDemandWidths number w m) j := by
  constructor
  · intro e he
    subst j
    cases e with
    | false => exact (wordBits _).symm (P.localAWord hc hd number order w l m
        (P.shrinkPlacedHalf w l _ rfl x))
    | true => exact (wordBits _).symm (P.localCWord w l m
        (P.shrinkPlacedHalf w l _ (P.shrinkPartySite_C l m) x))
  · intro e he
    subst j
    cases e with
    | false => exact (wordBits _).symm (P.localBWord hc hd number order w l m
        (P.shrinkPlacedHalf w l _ rfl x))
    | true => exact (wordBits _).symm (P.localDWord w l m
        (P.shrinkPlacedHalf w l _ rfl x))

/-- On the restrictions of a global assignment, the local rows read precisely
the four demand words of the unplaced six-party identity. -/
theorem shrinkLocalDemandArg_eval (m : P.Motif) (j : Fin 6)
    (x : (u : (P.oldWireNetwork w).Site) → (P.oldWireNetwork w).Half u) :
    P.shrinkLocalDemandArg hc hd number order w l m j (fun u _ ↦ x u) =
      P.shrinkDemandArg hc hd number order w m x j := by
  apply Prod.ext
  · funext e he
    subst j
    cases e with
    | false => rfl
    | true => exact congrArg (wordBits _).symm (P.localCWord_eval w l m x)
  · funext e he
    subst j
    cases e with
    | false => rfl
    | true => exact congrArg (wordBits _).symm (P.localDWord_eval w l m x)

end Compression.PackingData

end VPVNP
end Computability
end OAI
