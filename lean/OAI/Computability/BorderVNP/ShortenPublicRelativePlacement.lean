import OAI.Computability.BorderVNP.ShortenPublicRelativeBatch
import OAI.Computability.BorderVNP.ShortenCatalogStep
import OAI.Computability.BorderVNP.CoverLorentzMoves

/-!
# Exact site descriptors of every physical shortening profile

The packed input stores each copy motion and translation once, each retained
site's old catalog and tile at its existing row, and each seed's bin and tile
at its own address. The output at the existing static site number is proved
equal to the tile and catalog of the sewn placement for every public histogram.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open Catalog Epoch Crossing CombiningStep Cover Cover.AddressCircuit
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {I : Type*} [Fintype I] {q D m : ℕ} [NeZero D] {K : Type*} [Field K]

private noncomputable def atNamedRow {X Y : Type*} {n : ℕ} (name : X ↪ Fin n)
    (value : X → Y → Bool) (r : Fin n) (j : Y) : Bool :=
  if h : ∃ x, name x = r then value h.choose j else false

private theorem atNamedRow_eval {X Y : Type*} {n : ℕ} (name : X ↪ Fin n)
    (value : X → Y → Bool) (x : X) (j : Y) : atNamedRow name value (name x) j = value x j := by
  have h : ∃ u, name u = name x := ⟨x,rfl⟩
  simp only [atNamedRow,dite_eq_left h,name.injective h.choose_spec]

variable {P : Type*} {bits : P → ℕ} {A : Type} [Fintype A] (N : Pack D P bits K)
variable (bin : N.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)

/-- Packing the genuine geometric fields uses each actual row's stable name.
Unused input site and seed rows are zero-filled, including empty catalogs. -/
noncomputable def placementInput (enum : Fin q ≃ I) (p : Pattern I D) (S : Finset (HyperbolicHost I))
    (d lev : ℕ) (g : Placement (m := m) N bin perm I (SurfaceHost I (lev+1)))
    (a : PublicPlacement p S N bin perm lev g) {copies sites seeds : ℕ}
    (old : N.layout.Site ↪ Fin sites) (seed : A ↪ Fin seeds) (pick : Fin copies → Fin p.moves)
    (shift : Fin copies → I → gamma 1) : BatchPorts q p S d copies sites seeds → Bool :=
  Sum.elim (fun j => Sum.elim (fun n => decide (n=pick j.1))
    (productWires _ fun i => (shift j.1 (enum i) : Deck _)) j.2)
    (Sum.elim (fun j => atNamedRow old (fun v => Sum.elim
      (fun t => decide (t=(⟨normalize (a.oldLift v),a.oldType v⟩ : ↥S)))
      (tileWord enum _ (a.oldLift v))) j.1 j.2)
      (fun j => atNamedRow seed (fun s => Sum.elim (fun k => decide (k=a.code s))
        (productWires _ fun i => (a.deck s (enum i) : Deck _))) j.1 j.2))

/-- Wire encoding of the actual quotient site, with the output depth named
separately so that the positive quotient index can be written as a successor. -/
noncomputable def quotientRow (enum : Fin q ≃ I) (S : Finset (HyperbolicHost I)) {l : ℕ}
    (lev : ℕ) (hl : lev+1=l) (x : SurfaceHost I (lev+1)) : ProductSlots q l ⊕ ↥S → Bool :=
  Sum.elim (productWires l (fun i => hl ▸ productAddress lev x (enum i)))
    (fun t => decide (t.val=relative lev x))

private theorem quotientRow_projection (enum : Fin q ≃ I) (S : Finset (HyperbolicHost I)) {l : ℕ}
    (lev : ℕ) (hl : lev+1=l) (x : HyperbolicHost I) :
    quotientRow enum S lev hl (productProjection (lev+1) x) =
      Sum.elim (tileWord enum l x) (fun t => decide (t.val=normalize x)) := by
  subst l
  rfl

/-- The occupied old and seed rows of a physical placement. This contract
allows arbitrary bits at unused padded site names. -/
structure PlacementReads (enum : Fin q ≃ I) (p : Pattern I D) (S : Finset (HyperbolicHost I))
    {d copies sites seeds lev : ℕ} (home : Fin sites → Fin copies)
    (g : Placement (m := m) N bin perm I (SurfaceHost I (lev+1)))
    (a : PublicPlacement p S N bin perm lev g) (oldSite : N.layout.Site ↪ Fin sites) (seed : A ↪ Fin seeds)
    (z : BatchPorts q p S d copies sites seeds → Bool) : Prop where
  /-- The site's own row and the shared choice bank of its copy. -/
  old : ∀ v, z ∘ oldPin q p S d home (oldSite v) = Sum.elim (fun n => decide (n=a.copyMotion v))
    (siteInput enum S _ _ (a.oldDeck v) (a.oldLift v) (a.oldType v))
  /-- The relative seed bin and the shared seed tile. -/
  bank : ∀ s i, z (.inr (.inr (seed s,i))) = Sum.elim (fun k => decide (k=a.code s))
    (productWires _ fun j => (a.deck s (enum j) : Deck _)) i

omit [Field K] [Fintype A] in
/-- The canonical zero-padded source is one realization of the occupied-row contract. -/
theorem placementInput_reads (enum : Fin q ≃ I) (p : Pattern I D) (S : Finset (HyperbolicHost I))
    (d lev : ℕ) (g : Placement (m := m) N bin perm I (SurfaceHost I (lev+1)))
    (a : PublicPlacement p S N bin perm lev g) {copies sites seeds : ℕ}
    (old : N.layout.Site ↪ Fin sites) (seed : A ↪ Fin seeds) (pick : Fin copies → Fin p.moves)
    (shift : Fin copies → I → gamma 1) (home : Fin sites → Fin copies)
    (hp : ∀ v, pick (home (old v)) = a.copyMotion v) (hs : ∀ v, shift (home (old v)) = a.oldDeck v) :
    PlacementReads N bin perm enum p S home g a old seed
      (placementInput N bin perm enum p S d lev g a old seed pick shift) := by
  constructor
  · intro v
    funext j
    rcases j with j | j | j | j <;>
      simp only [placementInput,oldPin,Function.comp_apply,Sum.elim_inl,Sum.elim_inr,
        siteInput,rowInput,tileWord,hp,hs,atNamedRow_eval]
  · intro s i
    simp [placementInput,atNamedRow_eval]

set_option maxHeartbeats 1400000 in
/-- Every selected histogram has the same site-row circuit. Its answer at
each stable physical site number is the tile and relative position of that
specific retained site, terminal or bank site in the actual sewn placement. -/
theorem BatchRows.placement_rows_of_reads (enum : Fin q ≃ I) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) {d copies sites seeds : ℕ} (home : Fin sites → Fin copies)
    {f : Frame (BatchPorts q p S d copies sites seeds) (Fin (StaticRows.siteCapacity e sites seeds) ×
      (ProductSlots q (d+2*p.depth) ⊕ ↥(p.nextSites e S)))} (batch : BatchRows enum p e S d home f)
    (lev : ℕ) (hl : lev+1=d+2*p.depth) (g : Placement (m := m) N bin perm I (SurfaceHost I (lev+1)))
    (a : PublicPlacement p S N bin perm lev g) (old : N.layout.Site ↪ Fin sites) (seed : A ↪ Fin seeds)
    (z : BatchPorts q p S d copies sites seeds → Bool)
    (reads : PlacementReads N bin perm enum p S home g a old seed z)
    (positive : N.layout.Edge → Bool) (counts : Counts e N bin perm)
    (v : (physical N bin perm e positive counts).Site) (j : ProductSlots q (d+2*p.depth) ⊕ ↥(p.nextSites e S)) :
    f.eval z
      (StaticRows.siteRows e N old seed v,j) =
      quotientRow enum (p.nextSites e S) lev hl (g.postSites N bin perm e positive counts v) j := by
  rcases v with v | ⟨s,v⟩
  · change N.layout.Site at v
    change f.eval z (siteOrdinal e sites seeds (.inl (old v)),j) =
      quotientRow enum (p.nextSites e S) lev hl (g.old v) j
    rw [batch.old z _ _ _ _ _ (reads.old v) j,a.moved v,quotientRow_projection]
    rcases j with j | j
    · rfl
    · apply Bool.eq_iff_iff.mpr
      simp only [Sum.elim_inr,decide_eq_true_eq,Subtype.ext_iff,movedIndex,moved]
  · change BankSite e at v
    change f.eval z (siteOrdinal e sites seeds (.inr (seed s,(v : BankSite e))),j) =
      quotientRow enum (p.nextSites e S) lev hl (g.project s ((g.chart s).atSite
        ((e.profile (SeedIntervals.blocks N.layout bin perm m s) (counts s).val).position v))) j
    rw [batch.bank z (seed s) v (a.code s) (a.deck s) (reads.bank s) j,a.projects,quotientRow_projection,a.chartEq,
      profile_position e _ _ v]
    rcases j with j | j
    · rfl
    · apply Bool.eq_iff_iff.mpr
      simp only [Sum.elim_inr,decide_eq_true_eq,Subtype.ext_iff,bankIndex,bankPoint,normalize_translate]

set_option maxHeartbeats 1400000 in
/-- Every selected histogram has the same site-row circuit. Its answer at
each stable physical site number is the tile and relative position of that
specific retained site, terminal or bank site in the actual sewn placement. -/
theorem BatchRows.placement_rows (enum : Fin q ≃ I) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) {d copies sites seeds : ℕ} (home : Fin sites → Fin copies)
    {f : Frame (BatchPorts q p S d copies sites seeds) (Fin (StaticRows.siteCapacity e sites seeds) ×
      (ProductSlots q (d+2*p.depth) ⊕ ↥(p.nextSites e S)))} (batch : BatchRows enum p e S d home f)
    (lev : ℕ) (hl : lev+1=d+2*p.depth) (g : Placement (m := m) N bin perm I (SurfaceHost I (lev+1)))
    (a : PublicPlacement p S N bin perm lev g) (old : N.layout.Site ↪ Fin sites) (seed : A ↪ Fin seeds)
    (pick : Fin copies → Fin p.moves) (shift : Fin copies → I → gamma 1)
    (hp : ∀ v, pick (home (old v)) = a.copyMotion v) (hs : ∀ v, shift (home (old v)) = a.oldDeck v)
    (positive : N.layout.Edge → Bool) (counts : Counts e N bin perm)
    (v : (physical N bin perm e positive counts).Site) (j : ProductSlots q (d+2*p.depth) ⊕ ↥(p.nextSites e S)) :
    f.eval (placementInput N bin perm enum p S d lev g a old seed pick shift)
      (StaticRows.siteRows e N old seed v,j) =
      quotientRow enum (p.nextSites e S) lev hl (g.postSites N bin perm e positive counts v) j := by
  apply batch.placement_rows_of_reads N bin perm enum p e S home lev hl g a old seed _
  exact placementInput_reads N bin perm enum p S d lev g a old seed pick shift home hp hs


end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
