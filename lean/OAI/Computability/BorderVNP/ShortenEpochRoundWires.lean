import OAI.Computability.BorderVNP.ShortenEpochRoundInitial
import OAI.Computability.BorderVNP.CoverSiteRoundingFinite
import OAI.Computability.BorderVNP.ShortenEpochQuotientMidpoint

/-!
# The rounded active wire set and its endpoint histogram

Filtering the physical cable list by the old charge and then by the final
rounding event gives exactly the active edges of the new site realization.
The two Boolean labels in the rounding estimate are the actual two ends.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch.Round

open BorderVNP.Cover BorderVNP.Shortening BorderVNP.Crossing Finset
open scoped Classical

variable {I : Type} [Fintype I] {d D : ℕ} {P R : Type*} {bits : P → ℕ} {p : Pack D P bits R}

/-- The physical site at the indicated end of a cable. -/
def endAt (N : Network D P bits) (e : N.Edge) (b : Bool) : N.Site :=
  if b then N.dst e else N.src e

/-- Active physical cables in the last segment pack. -/
abbrev Wires (p : Pack D P bits R) (ch : p.layout.Edge → Bool) := {e // ch e = true}

private theorem sum_wires {E A : Type*} [Fintype E] [AddCommMonoid A] (ch : E → Bool) (f : E → A) :
    (∑ e : {e // ch e = true}, f e.val) = ∑ e, if ch e then f e else 0 := by
  classical
  let F (e : E) := if ch e then f e else 0
  have hy : (∑ e : {e // ch e = true}, F e.val) = ∑ e : {e // ch e = true}, f e.val :=
    sum_congr rfl (fun e _ => by simp [F,e.property])
  have hn : (∑ e : {e // ¬ch e = true}, F e.val) = 0 := sum_eq_zero (fun e _ => by simp [F,e.property])
  change _ = ∑ e, F e
  rw [← Fintype.sum_subtype_add_sum_subtype (p := fun e => ch e = true) F,hy,hn,add_zero]

/-- Actual weighted length is a sum over the physically charged cable subtype. -/
theorem length_as_sum {l : ℕ} (pos : p.layout.Site → SurfaceHost I l)
    (ch : p.layout.Edge → Bool) :
    (∑ e : Wires p ch, (p.layout.width e.val : ℝ)*dist (pos (p.layout.src e.val)) (pos (p.layout.dst e.val))) =
      chargedLength p.layout pos ch := sum_wires ch (fun e => (p.layout.width e : ℝ)*dist (pos (p.layout.src e)) (pos (p.layout.dst e)))

/-- Changing a rounded endpoint is exactly changing its tile address. -/
theorem failure_address (x y : SurfaceHost I (d+1)) :
    coordinateRoundingFailure d (fun k => x k) (fun k => y k) =
    if productAddress d x = productAddress d y then 0 else 1 := by
  classical
  unfold coordinateRoundingFailure
  congr 1
  apply propext
  constructor
  · intro h
    funext k
    have hk := congrArg (surfaceAddress d) (congrFun h k)
    simpa only [productAddress,surfaceAddress_roundedSite] using hk
  · intro h
    funext k
    exact congrArg (deckSite d) (congrFun h k)

variable {L : ℝ}

/-- The returned width and histogram are exactly those of the rounded site realization.
This also counts the source and destination separately for a directed cable. -/
theorem final_wire_identities (pos : p.layout.Site → SurfaceHost I (d+1)) (ch : p.layout.Edge → Bool)
    (s : SiteRoutes p I d L)
    (hs : ∀ v, reduceMove d (s.origin v) = productAddress d (pos v))
    (hc : ∀ e, s.active e ↔ ch e ∧ productAddress d (pos (p.layout.src e)) ≠ productAddress d (pos (p.layout.dst e))) :
    let keep (e : Wires p ch) := (p.layout.width e.val : ℝ)*coordinateRoundingFailure d
      (fun k => pos (p.layout.src e.val) k) (fun k => pos (p.layout.dst e.val) k)
    let ends (b : Wires p ch × Bool) (k : I) := surfaceAddress d
      (roundedSite d (pos (endAt p.layout b.1.val b.2) k))
    s.nonlocalWidth = ∑ e, keep e ∧ s.incidence = tileMass ends (fun b => keep b.1) := by
  classical
  let a (v : p.layout.Site) := productAddress d (pos v)
  let f (e : p.layout.Edge) := (p.layout.width e : ℝ) * coordinateRoundingFailure d
    (fun k => pos (p.layout.src e) k) (fun k => pos (p.layout.dst e) k)
  have hf (e : p.layout.Edge) : (if s.active e then (p.layout.width e : ℝ) else 0) =
      if ch e then f e else 0 := by
    dsimp [f]; rw [failure_address]
    split_ifs <;> simp_all
  constructor
  · change (∑ e, if s.active e then (p.layout.width e : ℝ) else 0) = ∑ e : Wires p ch, f e.val
    rw [sum_wires]; exact sum_congr rfl (fun e _ => hf e)
  · funext t
    simp only [SiteRoutes.incidence, SiteRoutes.sourceAddress, hs, tileMass, surfaceAddress_roundedSite,
      Fintype.sum_prod_type, Fintype.sum_bool, endAt, Bool.false_eq_true, ↓reduceIte, sum_add_distrib]
    have H (site : p.layout.Edge → p.layout.Site) :
        (∑ e : s.Active, if a (site e.val) = t then (p.layout.width e.val : ℝ) else 0) =
          ∑ e : Wires p ch, if a (site e.val) = t then f e.val else 0 := by
      rw [sum_wires s.active (fun e => if a (site e) = t then (p.layout.width e : ℝ) else 0),
        sum_wires ch (fun e => if a (site e) = t then f e else 0)]
      apply sum_congr rfl
      intro e _
      by_cases h : a (site e) = t
      · simpa only [h,ite_true] using hf e
      · simp [h]
    rw [add_comm]
    exact congrArg₂ (· + ·) (H p.layout.dst) (H p.layout.src)

/-- Physical midpoint population on the last segment pack, including its actual depth. -/
noncomputable def midpointMass {l : ℕ} (hl : 0 < l) (pos : p.layout.Site → SurfaceHost I l)
    (ch : p.layout.Edge → Bool) :=
  tileMass (fun e : Wires p ch => fun k => addressAt l hl
    (surfaceMidpoint (pos (p.layout.src e.val)) (pos (p.layout.dst e.val)) k)) (fun e => (p.layout.width e.val : ℝ))

end Epoch.Round

end BorderVNP
end Computability
end OAI
