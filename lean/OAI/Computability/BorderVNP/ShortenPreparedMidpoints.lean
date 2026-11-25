import OAI.Computability.BorderVNP.ShortenPreparedLabels
import OAI.Computability.BorderVNP.ShortenEpochQuotientMidpoint

/-!
# Midpoint addresses for the actual prepared placements

The midpoint of a classified cable is the projection of its sampled chart
center in its own tile. The fitted placement preserves its endpoint distance,
so projection gives the required bound by half its true length. The same
tie-resolved tile test identifies the centers of the replacement seeds.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Crossing Epoch Cover Cover.Frame Hecke Framed Packing PackMotions CombiningStep Set
open scoped Classical

variable {D : ℕ} [NeZero D] {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) {copies d n m : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
    (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) ((d+1)+2*n))
    (L : Labels B input active sites)
    (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) (d+1) n)

omit [NeZero D] in
private theorem dist_center_src {c : HyperbolicHost (Cube D)} {v : Direction D ℂ} {r : ℝ}
    (hv : ‖v‖ = 1) (hr : 0 ≤ r) : dist c (endpoint c v r true) = r := by
  have hz : productLine (-v) 0 = productChart 0 := by
    ext1 i
    change tangentLine _ (0 * _) = tangentChart 0
    simp [tangentLine]
  calc
    _ = dist (shiftTo c (productLine (-v) 0)) (shiftTo c (productLine (-v) r)) := by
      rw [hz,shiftTo_chart_zero]; rfl
    _ = r := by rw [(shiftTo_isometry c).dist_eq,dist_productLine,zero_sub,abs_neg,abs_of_nonneg hr,norm_neg,hv,mul_one]

/-- The midpoint and address hypotheses of the two physical epoch bounds hold for
every sampled placement, with the same midpoint for its record and concentration counts. -/
theorem physical_midpoints :
    let mb := B.tag (d := d+1) (n := n) input active L.kind L.lift
    let bin := jointBin input mb ω
    let p := parallelPacks input
    let perm := CanonicalPlacement.perm (fun t : B.types => t.val.radius) B.chart (T := Cube D → Deck (d+1))
    ∀ (g : Placement (m := m) p bin perm (Cube D) (SurfaceHost (Cube D) (d+1))),
      g.old = movedOld input ω sites →
      g.chart = CanonicalPlacement.chart (fun t : B.types => t.val.radius) B.chart →
      g.project = (fun a => tileProject a.1) →
      ∃ (oldMid : p.layout.Edge → SurfaceHost (Cube D) (d+1))
        (addr : p.layout.Edge → (Cube D → Deck (d+1)) × B.Bin),
        (∀ c a, bin c = some a → addr c = a ∧ a.1 = productTileName d (oldMid c) ∧
          dist (oldMid c) (g.old (p.layout.src c)) ≤ dist (g.old (p.layout.src c)) (g.old (p.layout.dst c))/2) ∧
        ∀ a, (perm 0 a).1 = productTileName d (g.project a (g.chart a).center) := by
  intro mb bin p perm g hold hchart hproject
  let shape := fun w : Active input active => (L.kind w).val
  let data := parallelData input active L.kind shape L.lift ω
  let r := fun t : B.types => t.val.radius
  have hbins : CanonicalPlacement.bin r B.chart p data = bin :=
    parallel_bin input active L.kind shape L.lift ω r B.chart
  let mid := fun c : p.layout.Edge => match data c with
    | some y => tileProject y.tile y.center
    | none => surfaceMidpoint (g.old (p.layout.src c)) (g.old (p.layout.dst c))
  let reserve : B.types := ⟨B.nonempty.choose,B.nonempty.choose_spec⟩
  let fallback : B.Bin := ⟨reserve,(B.chart reserve).code (reserve.val.center,reserve.val.direction)⟩
  let addr := fun c : p.layout.Edge => (bin c).getD (productTileName d (mid c),fallback)
  refine ⟨mid,addr,?_,?_⟩
  · intro c a ha
    refine ⟨by simp [addr,ha],?_⟩
    have he := congrFun hbins c
    rw [ha] at he
    change (data c).map (CanonicalPlacement.address r B.chart) = some a at he
    cases hd : data c with
    | none => simp [hd] at he
    | some y =>
      have hy : CanonicalPlacement.address r B.chart y = a := Option.some.inj (by simpa [hd] using he)
      subst a
      have hm : mid c = tileProject y.tile y.center := by simp [mid,hd]
      rw [hm]
      refine ⟨(tileProject_address y.tile y.center y.mem).symm,?_⟩
      have hs : tileProject y.tile (endpoint y.center y.direction (r y.kind) true) = g.old (p.layout.src c) := by
        by_cases hc : active c.1 c.2
        · let w : Active input active := ⟨c.1,c.2,hc⟩
          have hey : record (shape w) (L.kind w) (L.lift w) (ω c.1) = y :=
            Option.some.inj (by simpa [data,parallelData,hc,w] using hd)
          subst y
          rw [hold]
          have hproj := projects (shape w) (L.kind w) (L.lift w) (ω c.1) true
          simp only [ite_true] at hproj
          rw [L.src w] at hproj
          exact hproj
        · simp [data,parallelData,hc] at hd
      rw [g.bin_length _ _ ha,hchart,← hs]
      calc
        _ ≤ dist y.center (endpoint y.center y.direction (r y.kind) true) := tileProject_nonexpanding _ _ _
        _ = r y.kind := dist_center_src y.norm y.kind.val.positive.le
        _ = _ := by change r y.kind = 2*r y.kind/2; ring
  · intro a
    rw [hproject,hchart]
    exact (tileProject_address a.1 _ (B.relative a.2.1 a.2.2)).symm

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
