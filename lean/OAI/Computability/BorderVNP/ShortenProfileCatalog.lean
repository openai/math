import OAI.Computability.BorderVNP.ShortenRelativeEndpoints
import OAI.Computability.BorderVNP.ShortenCombiningConcentration

/-!
# Catalogs for the output of an arbitrary actual combining step

Every histogram uses the same bank sites and terminal positions. A moved old
site and an inserted site therefore have relative types in a finite catalog
chosen before the input fan-in or profile multiplicities. The old site case
covers every retained local box, including ends of uncharged cables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Catalog

open Crossing Epoch Cover Cover.Frame Hecke Set CombiningStep
open scoped BigOperators Classical

variable {I : Type*} [Fintype I] {D m : ℕ} {K : Type*} [Field K]

/-- Sites of the common one-copy banks and control spokes, before any histogram is selected. -/
abbrev BankSite (e : PaidIdentity K D m) :=
  Unit ⊕ (Fin D × Bool) ⊕ Σ a, (e.net a).Site

/-- The histogram-independent position of a bank or terminal site. -/
noncomputable def bankPosition (e : PaidIdentity K D m) :
    BankSite e → EuclideanSpace ℝ (Fin D)
  | .inl _ => 0
  | .inr (.inl u) => antipodalPosition u
  | .inr (.inr ⟨a,v⟩) => (e.net a).position v

/-- Every physical profile site occupies its fixed bank position for every count tuple. -/
theorem profile_position (e : PaidIdentity K D m) (j : ℕ) (hist : Fin e.count → ℕ)
    (v : (e.profile j hist).Site) :
    (e.profile j hist).position v = bankPosition e (show BankSite e from v) := by
  change BankSite e at v
  rcases v with _ | _ | ⟨_,_⟩ <;> rfl

/-- A round's finite choices, prepared from the previous catalog. Chart
representatives use lifted base-tile coordinates; their tile address is separate. -/
structure Pattern (I : Type*) [Fintype I] (D : ℕ) where
  /-- Number of whole-pack motions in the finite frame list. -/
  moves : ℕ
  /-- Common congruence depth needed to clear all motion denominators. -/
  depth : ℕ
  /-- Permutation of surface factors for each motion. -/
  perm : Fin moves → Equiv.Perm I
  /-- Frame motion on each factor. -/
  matrix : Fin moves → I → SL
  /-- Each motion uses this fixed low residue window. -/
  clears : ∀ n i, Clears (matrix n i) depth
  /-- Number of relative bin representatives. -/
  bins : ℕ
  /-- Placement of the canonical crossing at a relative representative. -/
  chart : Fin bins → SeedChart I D

/-- Relative sites in every moved copy, obtained from the finite low frame tables. -/
noncomputable def Pattern.movedSites (p : Pattern I D) (S : Finset (HyperbolicHost I)) :
    Finset (HyperbolicHost I) :=
  let h := finite_moved_points p.perm p.matrix p.clears S.finite_toSet
  h.choose_spec.1.toFinset

/-- The low-window table covers every retained site after every possible deck translation. -/
theorem Pattern.mem_movedSites (p : Pattern I D) (S : Finset (HyperbolicHost I))
    (n : Fin p.moves) (x : HyperbolicHost I) (hx : normalize x ∈ S) (deck : I → gamma 1) :
    normalize (translatePoint deck (motion (p.perm n) (p.matrix n) x)) ∈ p.movedSites S := by
  let h := finite_moved_points p.perm p.matrix p.clears S.finite_toSet
  exact h.choose_spec.1.mem_toFinset.mpr (h.choose_spec.2 n x hx deck)

/-- Relative positions of all retained and inserted sites after one step.
Its parameters contain neither fan-in nor histogram counts. -/
noncomputable def Pattern.nextSites (p : Pattern I D) (e : PaidIdentity K D m) (S : Finset (HyperbolicHost I)) :
    Finset (HyperbolicHost I) :=
  p.movedSites S ∪ Finset.univ.image (fun t : Fin p.bins × BankSite e =>
    normalize ((p.chart t.1).atSite (bankPosition e t.2)))

/-- Prepare all successive relative site catalogs before selecting the fan-in.
The next motion and chart list can be chosen from the current catalog. -/
noncomputable def siteCatalogs (e : PaidIdentity K D m) (initial : Finset (HyperbolicHost I))
    (round : ℕ → Finset (HyperbolicHost I) → Pattern I D) : ℕ → Finset (HyperbolicHost I)
  | 0 => initial
  | n+1 =>
    let s := siteCatalogs e initial round n
    (round n s).nextSites e s

variable {P : Type*} {bits : P → ℕ} {A : Type} [Fintype A] [NeZero D]
variable (e : PaidIdentity K D m) (p : Pack D P bits K) (bin : p.layout.Edge → Option A)
variable (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool) (d : ℕ)

/-- The catalog applies to the concrete post-step quotient sites. Retained
old records are moved in their own copy; every joint histogram bank is
installed at the canonical representative of its seed's relative bin. -/
theorem actual_sites (pat : Pattern I D) (initial : Finset (HyperbolicHost I))
    (g : Placement (m := m) p bin perm I (SurfaceHost I (d+1)))
    (q : Counts e p bin perm)
    (copyMotion : p.layout.Site → Fin pat.moves) (oldLift : p.layout.Site → HyperbolicHost I)
    (oldDeck : p.layout.Site → I → gamma 1) (ho : ∀ v, normalize (oldLift v) ∈ initial)
    (hm : ∀ v, g.old v = productProjection (d+1) (translatePoint (oldDeck v)
      (motion (pat.perm (copyMotion v)) (pat.matrix (copyMotion v)) (oldLift v))))
    (code : A → Fin pat.bins) (chartEq : ∀ a, g.chart a = pat.chart (code a))
    (deck : A → I → gamma 1)
    (hp : ∀ a z, g.project a z = productProjection (d+1) (translatePoint (deck a) z)) :
    ∀ v : (physical p bin perm e positive q).Site,
      relative d (g.postSites p bin perm e positive q v) ∈ pat.nextSites e initial := by
  rintro (v | ⟨a,v⟩)
  · change relative d (g.old v) ∈ _
    erw [hm v,relative_projection]
    exact Finset.mem_union_left _ (pat.mem_movedSites initial _ _ (ho v) _)
  · change relative d (g.project a ((g.chart a).atSite
      ((e.profile (SeedIntervals.blocks p.layout bin perm m a) (q a).val).position v))) ∈ _
    erw [hp,relative_projection,normalize_translate,chartEq,profile_position e _ _ v]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(code a,(v : BankSite e)),Finset.mem_univ _,rfl⟩)

/-- The next segment catalog follows from the finite site list using bounded
relative carries. It represents actual distances even for winding quotient
graphs, by choosing one jointly lifted endpoint pair per charged edge. -/
theorem actual_segments (pat : Pattern I D) (initial : Finset (HyperbolicHost I)) (L : ℝ) :
    ∃ V : Set (SegmentType I), V.Finite ∧ ∀ {P : Type*} {bits : P → ℕ} {A : Type} [Fintype A]
      (p : Pack D P bits K) (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
      (positive : p.layout.Edge → Bool) (d : ℕ)
      (g : Placement (m := m) p bin perm I (SurfaceHost I (d+1))) (q : Counts e p bin perm),
      (∀ v, relative d (g.postSites p bin perm e positive q v) ∈ pat.nextSites e initial) →
      ∀ c : (physical p bin perm e positive q).Edge,
      let N := physical p bin perm e positive q
      let z := g.postSites p bin perm e positive q
      z (N.src c) ≠ z (N.dst c) → dist (z (N.src c)) (z (N.dst c)) ≤ L →
        ∃ s ∈ V, Realizes (z (N.src c)) (z (N.dst c)) s.ends := by
  obtain ⟨V,hV,h⟩ := finite_segments (pat.nextSites e initial).finite_toSet L
  refine ⟨V,hV,?_⟩
  intro P bits A _ p bin perm positive d g q hs c N z hne hlen
  exact h d _ _ (hs (N.src c)) (hs (N.dst c)) hne hlen

end Shortening.Catalog

end BorderVNP
end Computability
end OAI
