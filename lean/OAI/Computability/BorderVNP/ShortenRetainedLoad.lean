import OAI.Computability.BorderVNP.ShortenPreparedChildren
import OAI.Computability.BorderVNP.ShortenEpochRoundRecords
import OAI.Computability.BorderVNP.ShortenCubeEnumeration

/-!
# Retained records of moved child packs

A common sampled permutation, word tuple and deck translation move all sites
of each child. Its public records, prior boxes and expanded payload reach
only boundedly many source tiles per destination tile. Disjoint union adds
the resulting child costs, including separate external port intervals.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Cover Cover.Frame Crossing Epoch Framed Hecke Packing Finset
open scoped Classical BorderVNP.Epoch.Cube

/-- Exact per-tile count of a disjoint parallel union, for any tile test on
its sites. Old boxes, both cable ends, and all external intervals are counted
in their own constituent. -/
theorem parallel_localRecords {D k : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {K : Type*}
    (input : Fin k → Pack D P bits K) (ex : Bool) (prior payload : ∀ i, (input i).layout.Site → ℕ)
    (test : ∀ i, (input i).layout.Site → Prop) :
    localRecords (parallelPacks input).layout ex (fun v => prior v.1 v.2) (fun v => payload v.1 v.2)
      (fun v => test v.1 v.2) = ∑ i, localRecords (input i).layout ex (prior i) (payload i) (test i) := by
  let box (v : Σ i, (input i).layout.Site) := if test v.1 v.2 then boxCost ex (prior v.1 v.2) (payload v.1 v.2) else 0
  let src (c : Σ i, (input i).layout.Edge) := if test c.1 ((input c.1).layout.src c.2) then
    recordCost ex ((input c.1).layout.width c.2) else 0
  let dst (c : Σ i, (input i).layout.Edge) := if test c.1 ((input c.1).layout.dst c.2) then
    recordCost ex ((input c.1).layout.width c.2) else 0
  let port (x : Fin k × P) := if test x.1 ((input x.1).layout.attach x.2) then recordCost ex (bits x.2) else 0
  change (∑ v, box v) + (∑ c, src c) + (∑ c, dst c) + (∑ x, port x) = _
  rw [Fintype.sum_sigma,Fintype.sum_sigma,Fintype.sum_sigma,Fintype.sum_prod_type]
  simp only [localRecords,testedWidth,sum_add_distrib]
  rfl

private theorem cast_local_cap {D l d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {K : Type*}
    {I : Type} [Fintype I] (p : PlacedPack D P bits K I d) (hl : d+1 = l) (hpos : 0 < l)
    (prior payload : p.pack.layout.Site → ℕ) (ex : Bool) (M : ℕ)
    (h : ∀ t, localRecords p.pack.layout ex prior payload (fun v => productTileName d (p.site v) = t) ≤ M) :
    ∀ t, localRecords p.pack.layout ex prior payload
      (fun v => (fun k => addressAt l hpos (levelCast hl (p.site v) k)) = t) ≤ M := by
  subst l; exact h

namespace PreparedBins

/-- Uniform per-tile cap after the selected motions of all children, before
splitting their cables. Both record modes use the very same physical motions,
with a linear factor in the number of children. -/
theorem moved_children_localRecords (D n : ℕ) :
    ∃ C : ℕ, ∀ d {k : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {K : Type*}
      (child : Fin k → PlacedPack D P bits K (Cube D) ((d+1)+2*n))
      (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+2) n)
      (prior payload : ∀ i, (child i).pack.layout.Site → ℕ) (ex : Bool) (M : ℕ),
      (∀ i t, localRecords (child i).pack.layout ex (prior i) (payload i)
        (fun v => productTileName ((d+1)+2*n) ((child i).site v) = t) ≤ M) →
      ∀ t, localRecords (parallelPacks fun i => (child i).pack).layout ex
        (fun v => prior v.1 v.2) (fun v => payload v.1 v.2)
        (fun v => productTileName (d+1) (movedOld (fun i => (child i).pack) ω
          (childSites (d := d+1) (n := n) child) v) = t) ≤ C*k*M := by
  obtain ⟨C,hC⟩ := final_round_record_bounds n (Cube D)
  refine ⟨C,?_⟩
  intro d k P _ bits K child ω prior payload ex M hc t
  let input := fun i => (child i).pack
  let x := childSites (d := d+1) (n := n) child
  let out (i : Fin k) (v : (input i).layout.Site) := productTileName (d+1) (sampleMove (ω i) (x i v)) = t
  have bound (i : Fin k) : localRecords (input i).layout ex (prior i) (payload i) (out i) ≤ C*M := by
    let s := ω i
    let g (j : Cube D) := gammaSL 1 (s.2.2 j).out * wordMatrix s.2.1 j
    let hg : ∀ j, Clears (g j) n := sample_clears s
    let y (v : (input i).layout.Site) : SurfaceHost (Cube D) (d+2+2*n) := WithLp.toLp 2 (fun j => x i v (s.1 j))
    have hold (u) : localRecords (input i).layout ex (prior i) (payload i)
        (fun v => (fun j => addressAt (d+2+2*n) (by omega) (y v j)) = u) ≤ M := by
      let a (v : (input i).layout.Site) (j : Cube D) := addressAt (d+2+2*n) (by omega) (x i v j)
      have test : (fun v => (fun j => a v (s.1 j)) = u) = fun v => a v = u ∘ s.1.symm := by
        funext v; apply propext
        constructor
        · intro he; funext j
          simpa [Function.comp_def] using congrFun he (s.1.symm j)
        · intro he; funext j
          simpa [Function.comp_def] using congrFun he (s.1 j)
      change localRecords _ _ _ _ (fun v => (fun j => a v (s.1 j)) = u) ≤ M
      rw [test]
      exact cast_local_cap (child i) (Nat.add_right_comm (d+1) (2*n) 1) (by omega) _ _ _ _ (hc i) _
    have H := hC d g hg (input i).layout y (prior i) (payload i) ex M hold t
    simp only [surfaceAddress_roundedSite] at H
    exact H
  calc
    _ = ∑ i, localRecords (input i).layout ex (prior i) (payload i) (out i) :=
      parallel_localRecords input ex prior payload out
    _ ≤ ∑ _i : Fin k, C*M := sum_le_sum fun i _ => bound i
    _ = _ := by simp [Nat.mul_left_comm,Nat.mul_assoc]

end PreparedBins

end Shortening

end BorderVNP
end Computability
end OAI
