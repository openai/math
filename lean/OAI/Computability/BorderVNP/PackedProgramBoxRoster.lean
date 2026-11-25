import OAI.Computability.BorderVNP.PackedBankSortedCell
import OAI.Computability.BorderVNP.PackedBankRoundSites
import OAI.Computability.BorderVNP.PackedHistoryPrivateSites
import OAI.Computability.BorderVNP.ShortenPublicParallelNames

/-! # Public physical slot of each stored private factor

The rectangle for every seed is complete on every accepted histogram. Its
paid sites store one immutable template table even for multiplicity zero.
The old part of the rectangle keeps its original descriptors and its holes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.CombiningStep Shortening.StaticRows Shortening.PublicParallel CellSparse
open scoped Classical

/-- Every retained program has precisely its birth site's one-copy factor tables. -/
theorem Site.Retention.boxes_eq {a s : Site} (h : a.Retention s) : s.boxes = a.boxes := by
  induction h <;> first | rfl | assumption

/-- All stages of this lineage refer to the same immutable factor bodies. -/
theorem Site.Lineage.boxes_eq_birth {w : ℕ} (s : Site.Lineage w) : s.program.boxes = s.birth.boxes :=
  s.retention.boxes_eq

namespace BoxRoster

/-- A fixed padded table specifies the real box bodies and fills every
unoccupied physical site with an empty list. -/
structure Realizes {X α : Type*} {s : ℕ} (row : X ↪ Fin s) (bodies : X → List α)
    (known : Fin s → List α) : Prop where
  live : ∀ v, known (row v) = bodies v
  hole : ∀ i, i ∉ Set.range row → known i = []

/-- Exact equality with the slot lookup used by the final sorted cell. -/
theorem Realizes.slots_eq {X : Type} {α : Type*} {s : ℕ} {row : X ↪ Fin s} {bodies : X → List α}
    {known : Fin s → List α} (h : Realizes row bodies known) (i : Fin s) :
    FinalCell.slots row bodies i = known i := by
  by_cases present : ∃ v, row v = i
  · obtain ⟨v,rfl⟩ := present
    rw [FinalCell.slots,Function.partialInv_left row.injective]
    exact (h.live v).symm
  · have hx : Function.partialInv row i = none := by
      cases he : Function.partialInv row i with
      | none => rfl
      | some v => exact (present ⟨v,(row.injective.isPartialInv v i).mp he⟩).elim
    rw [FinalCell.slots,hx,h.hole i present]
    rfl

/-- Reindex the padded public array along its scheduled capacity equality. -/
theorem Realizes.reindex {X α : Type*} {s t : ℕ} {a : X ↪ Fin s} {body : X → List α}
    {known : Fin s → List α} (h : Realizes a body known) (b : X ↪ Fin t) (f : Fin t ≃ Fin s)
    (eqn : ∀ v, f (b v) = a v) : Realizes b body (known ∘ f) := by
  constructor
  · intro v
    rw [Function.comp_apply,eqn,h.live]
  · intro r hr
    apply h.hole
    rintro ⟨v,hv⟩
    exact hr ⟨v,f.injective ((eqn v).trans hv)⟩

/-- Child-major rectangle of the previous public descriptors. -/
def parallel {α : Type*} {k s : ℕ} (known : Fin k → Fin s → List α) (r : Fin (k*s)) :=
  let z : Fin k × Fin s := finProdFinEquiv.symm r
  known z.1 z.2

/-- Each old slot stays live or empty at its exact parallel site index. -/
theorem Realizes.parallel {α : Type*} {k s : ℕ} {X : Fin k → Type*} {row : ∀ j, X j ↪ Fin s}
    {body : ∀ j, X j → List α} {known : Fin k → Fin s → List α} (h : ∀ j, Realizes (row j) (body j) (known j)) :
    Realizes (parallelName row) (fun v => body v.1 v.2) (BoxRoster.parallel known) := by
  constructor
  · rintro ⟨j,v⟩
    change (fun z : Fin k × Fin s => known z.1 z.2) (finProdFinEquiv.symm (finProdFinEquiv (j,row j v))) = _
    rw [Equiv.symm_apply_apply]
    exact (h j).live v
  · intro i absent
    obtain ⟨⟨j,r⟩,rfl⟩ := finProdFinEquiv.surjective i
    change (fun z : Fin k × Fin s => known z.1 z.2) (finProdFinEquiv.symm (finProdFinEquiv (j,r))) = []
    rw [Equiv.symm_apply_apply]
    apply (h j).hole
    rintro ⟨v,rfl⟩
    exact absent ⟨⟨j,v⟩,rfl⟩

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (number : e.Entry → ℕ)

/-- The body fixed by each publicly named template. Its paid entry uses the
actual crossing identity's coefficient dictionary, for all profile counts. -/
noncomputable def template : TemplateSite e → List (List Factor)
  | .inl _ | .inr (.inl _) => []
  | .inr (.inr ⟨a,v⟩) => [[PaidBox.tableFactor e number a v]]

/-- Static descriptor rectangle after a complete seed population is installed. -/
noncomputable def sewn {s n : ℕ} (known : Fin s → List (List Factor)) (i : Fin (siteCapacity e s n)) :=
  match (finSumFinEquiv.symm i : Fin s ⊕ Fin (n*Fintype.card (TemplateSite e))) with
  | .inl r => known r
  | .inr t => template e number ((Fintype.equivFin _).symm (finProdFinEquiv.symm t).2)

/-- The native site roster after the fixed sequence of inner rectangles. At
each combining step the same predecessor array appears once per physical child. -/
noncomputable def steps {b k : ℕ} {V : ℕ → ℕ} (seeds : Fin b → ℕ)
    (rect : ∀ i : Fin b, V (i.val+1) = siteCapacity e (k*V i.val) (seeds i))
    (base : Fin (V 0) → List (List Factor)) : (j : ℕ) → Fin (V j) → List (List Factor)
  | 0 => base
  | j+1 => if h : j<b then fun r =>
      let ix : Fin b := ⟨j,h⟩
      sewn (s := k*V j) (n := seeds ix) e number
        (parallel (k := k) (s := V j) (fun _ => steps seeds rect base j)) (Fin.cast (rect ix) r)
    else fun _ => []

variable [NeZero D] {P A : Type} [Fintype P] [Fintype A] {bits : P → ℕ} (p : Pack D P bits K)
    (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
    (first : Fin D × Bool) (q : Counts e p bin perm) (names : A → ℕ) {s n ne np : ℕ}
    (oldSite : p.layout.Site ↪ Fin s) (seed : A ≃ Fin n) {ns : ℕ}
    (used : (output e p bin perm positive first q).layout.Site ↪ Fin ns)
    (edge : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)

/-- One actual physical combining step realizes the predetermined rectangle,
including all holes. No multiplicity or cable assignment enters its box roster. -/
theorem sewn_realizes (known : Fin s → List (List Factor)) (ho : Realizes oldSite (fun v => (old v).boxes) known) :
    let site := siteRows e p oldSite seed.toEmbedding
    Realizes site (fun v => (roundSites e p bin perm positive first q names number used edge port old cuts v).boxes)
      (sewn (n := n) e number known) := by
  intro site
  constructor
  · rintro (v|⟨a,t⟩)
    · have key : site (.inl v) = finSumFinEquiv (.inl (oldSite v)) := rfl
      simpa only [key,sewn,Equiv.symm_apply_apply,roundSites,Site.retain] using ho.live v
    · have key : site (.inr ⟨a,t⟩) = finSumFinEquiv (.inr (finProdFinEquiv (seed a,Fintype.equivFin _ t))) := rfl
      simp only [key,sewn,Equiv.symm_apply_apply]
      rcases t with ⟨⟩ | u | ⟨i,v⟩ <;> rfl
  · intro i hi
    obtain ⟨r,rfl⟩ := finSumFinEquiv.surjective i
    rcases r with r | z
    · rw [sewn,Equiv.symm_apply_apply]
      apply ho.hole
      rintro ⟨v,rfl⟩
      exact hi ⟨.inl v,rfl⟩
    · obtain ⟨⟨a,t⟩,rfl⟩ := finProdFinEquiv.surjective z
      obtain ⟨a,rfl⟩ := seed.surjective a
      obtain ⟨t,rfl⟩ := (Fintype.equivFin (TemplateSite e)).surjective t
      exact (hi ⟨.inr ⟨a,t⟩,rfl⟩).elim

end BoxRoster
end Packing.Inherited

end BorderVNP
end Computability
end OAI
