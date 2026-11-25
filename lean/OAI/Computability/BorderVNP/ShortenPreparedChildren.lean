import OAI.Computability.BorderVNP.ShortenPreparedLabels
import OAI.Computability.BorderVNP.ShortenPlacedStep

/-!
# Charging and reindexing the actual children of a combining step

Coincident charged cables contribute zero length and do not enter the
midpoint census. They remain in the child layout. The slight reindexing of
the congruence level puts the same child sites at the domain of the chosen
whole-pack motion.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Epoch Cover Cover.Frame Hecke Framed Packing PackMotions CombiningStep
open scoped Classical

variable {I : Type} [Fintype I]

/-- Transport a product surface through an equality of integer level names. -/
def levelCast {d l : ℕ} (hd : d = l) (x : SurfaceHost I d) : SurfaceHost I l := hd ▸ x

/-- Such reindexing preserves all actual distances. -/
theorem levelCast_dist {d l : ℕ} (hd : d = l) (x y : SurfaceHost I d) :
    dist (levelCast hd x) (levelCast hd y) = dist x y := by cases hd; rfl

variable {D d n k m : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}

/-- Positive-length charged cables are the active wires for motion and direction bins. -/
noncomputable def PlacedPack.active (p : PlacedPack D P bits K I d) (e : p.pack.layout.Edge) : Bool :=
  p.charged e && decide (p.site (p.pack.layout.src e) ≠ p.site (p.pack.layout.dst e))

/-- An active cable is charged and has distinct endpoints. -/
theorem PlacedPack.active_iff (p : PlacedPack D P bits K I d) (e : p.pack.layout.Edge) :
    p.active e = true ↔ p.charged e = true ∧ p.site (p.pack.layout.src e) ≠ p.site (p.pack.layout.dst e) := by
  simp only [active,Bool.and_eq_true,decide_eq_true_eq]

namespace PreparedBins

variable {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
variable (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*n))

/-- Sites of the child at the equal domain level of the whole-pack motion. -/
def childSites (i : Fin k) (v : (child i).pack.layout.Site) : SurfaceHost (Cube D) ((d+1)+2*n) :=
  levelCast (Nat.add_right_comm d (2*n) 1) ((child i).site v)

/-- Transporting the chosen labels does not change their type or their integral carry. -/
noncomputable def Labels.transport {a l : ℕ} {input : Fin k → Pack D P bits K}
    {active : ∀ i, (input i).layout.Edge → Bool} {sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) a}
    (L : Labels B input active sites) (hl : a = l) :
    Labels B input active (fun i v => levelCast hl (sites i v)) := by cases hl; exact L

/-- Every physically prepared child has actual integral lifts for its active cables. -/
theorem exists_childLabels
    (sitesMem : ∀ i v, Catalog.relative (d+2*n) ((child i).site v) ∈ S)
    (short : ∀ i e, (child i).charged e = true →
      dist ((child i).site ((child i).pack.layout.src e)) ((child i).site ((child i).pack.layout.dst e)) ≤ 2*h) :
    Nonempty (Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child)) := by
  obtain ⟨L⟩ := B.exists_labels (fun i => (child i).pack) (fun i => (child i).active) (fun i => (child i).site)
    sitesMem (fun w => ((child w.1).active_iff _ |>.mp w.2.property).2)
    (fun w => short w.1 w.2.val (((child w.1).active_iff _).mp w.2.property).1)
  exact ⟨L.transport _ (Nat.add_right_comm d (2*n) 1)⟩

variable [NeZero D]
variable (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child))
variable (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) n)

/-- The physical step built on the actual sorted sample tags. -/
noncomputable def placedStep
    (g : Placement (m := m) (parallelPacks fun i => (child i).pack)
      (jointBin (fun i => (child i).pack)
        (B.tag (d := d+1) (n := n) (fun i => (child i).pack) (fun i => (child i).active) L.kind L.lift) ω)
      (CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart) (Cube D) (SurfaceHost (Cube D) (d+1))) :
    PlacedStep m B.Bin d child := ⟨_,_,fun _ => true,g⟩

/-- Physical placement preserves length cablewise, including coincident and
inactive retained cables. The tag determines the correct listed radius. -/
theorem keeps_length
    (g : Placement (m := m) (parallelPacks fun i => (child i).pack)
      (jointBin (fun i => (child i).pack)
        (B.tag (d := d+1) (n := n) (fun i => (child i).pack) (fun i => (child i).active) L.kind L.lift) ω)
      (CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart) (Cube D) (SurfaceHost (Cube D) (d+1)))
    (hchart : g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart) :
    (B.placedStep child L ω g).KeepsLength := by
  intro i c
  let p := child i
  by_cases hc : p.active c = true
  · let w : Active (fun i => (child i).pack) (fun i => (child i).active) := ⟨i,c,hc⟩
    let a := sampleAddress (fun i => (child i).pack) (fun i => (child i).active) (fun w => speed (L.kind w).val)
      (fun w x => (⟨L.kind w,(B.chart (L.kind w)).code x⟩ : B.Bin))
      (fun w => sourceFrame (L.kind w).val (L.lift w)) (fun w => movedCarry (L.kind w).val (L.lift w))
      w (ω i)
    have hb : (B.placedStep child L ω g).bin ⟨i,c⟩ = some a := by
      change (if ht : p.active c then some _ else none) = _
      rw [dite_eq_left hc]
    simp only [hb, Option.isSome_some, ite_true]
    rw [ite_eq_left ((p.active_iff c).mp hc).1]
    have he := g.bin_length ⟨i,c⟩ a hb
    rw [hchart] at he
    have hold := L.length w
    rw [show dist (childSites child w.1 ((child w.1).pack.layout.src w.2.val))
        (childSites child w.1 ((child w.1).pack.layout.dst w.2.val)) = _ from levelCast_dist _ _ _] at hold
    exact he.trans hold.symm
  · have hb : (B.placedStep child L ω g).bin ⟨i,c⟩ = none := by
      change (if ht : p.active c then some _ else none) = _
      rw [dite_eq_right hc]
    simp only [hb, Option.isSome_none, Bool.false_eq_true, ite_false]
    by_cases hcharged : p.charged c = true
    · have he : p.site (p.pack.layout.src c) = p.site (p.pack.layout.dst c) := by
        by_contra hne; exact hc ((p.active_iff c).mpr ⟨hcharged,hne⟩)
      rw [ite_eq_left hcharged,he,dist_self]
    · rw [ite_eq_right hcharged]

end PreparedBins
end Shortening

end BorderVNP
end Computability
end OAI
