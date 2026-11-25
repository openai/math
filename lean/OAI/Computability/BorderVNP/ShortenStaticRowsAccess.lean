import OAI.Computability.BorderVNP.ShortenStaticRows
import OAI.Computability.BorderVNP.ShortenSeedDescriptorEndpoints

/-!
# Accessing the static rows of the sewn pack

Old intervals retain their own sites. Each chosen prefix supplies one hook
at each old end, terminating at the appropriate signed terminal in the
seed bank. Inside the bank the endpoints are fixed and only widths depend
on the histogram counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.StaticRows

open Crossing SeedIntervals CombiningStep
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
variable {nSites nEdges nSeeds : ℕ}
variable (oldSite : p.layout.Site ↪ Fin nSites) (oldEdge : p.layout.Edge ↪ Fin nEdges)
variable (seed : A ↪ Fin nSeeds)

/-- Arithmetic address of an interval in the old-band rectangle. -/
def bandAddress (c : p.layout.Edge × Band D) : ℕ := (bandRow D c.2).val + (2*D+1)*(oldEdge c.1).val

omit [NeZero D] [Fintype A] in
/-- Static site names keep the old site numbers and shift seed sites into fixed bank rectangles. -/
theorem siteRow_old (v : p.layout.Site) :
    (siteRows e p oldSite seed (.inl v)).val = (oldSite v).val := rfl

omit [NeZero D] [Fintype A] in
/-- Arithmetic address of a seed's site in the fixed paid bank. -/
theorem siteRow_seed (a : A) (v : TemplateSite e) :
    (siteRows e p oldSite seed (.inr ⟨a,v⟩)).val =
      nSites + ((Fintype.equivFin (TemplateSite e) v).val + Fintype.card (TemplateSite e)*(seed a).val) := rfl

/-- Every selected cable has exactly these two reserved hook addresses. -/
theorem hookRows (c : ↥((partition p.layout bin perm m).selected)) :
    (edgeRows e p bin perm oldEdge seed (.inl (.inl c))).val = bandAddress p oldEdge c.val ∧
      (edgeRows e p bin perm oldEdge seed (.inl (.inr c))).val =
        nEdges*(2*D+1) + bandAddress p oldEdge c.val := ⟨rfl,rfl⟩

/-- Arithmetic address of an unselected band, after both hook rectangles. -/
theorem retainedRow (c : {c : (layout p.layout bin perm m).Edge // c ∉ (partition p.layout bin perm m).selected}) :
    (edgeRows e p bin perm oldEdge seed (.inr (.inl c))).val =
      (nEdges*(2*D+1)+nEdges*(2*D+1)) + bandAddress p oldEdge c.val := rfl

/-- Arithmetic address of a bank edge, after the two hook rectangles and retained-band rectangle. -/
theorem bankRow (a : A) (c : TemplateEdge e) :
    (edgeRows e p bin perm oldEdge seed (.inr (.inr ⟨a,c⟩))).val =
      (nEdges*(2*D+1)+nEdges*(2*D+1)) + (nEdges*(2*D+1) +
        ((Fintype.equivFin (TemplateEdge e) c).val + Fintype.card (TemplateEdge e)*(seed a).val)) := rfl

/-- Fixed initial site of a selector spoke, bank feeder, or original paid-network wire. -/
def templateSrc : TemplateEdge e → TemplateSite e
  | .inl _ => .inl ()
  | .inr (.inl (_,u)) => .inr (.inl u)
  | .inr (.inr ⟨a,z⟩) => .inr (.inr ⟨a,(e.net a).src z⟩)

/-- Fixed destination site of a selector spoke, bank feeder, or original paid-network wire. -/
def templateDst : TemplateEdge e → TemplateSite e
  | .inl u => .inr (.inl u)
  | .inr (.inl (a,u)) => .inr (.inr ⟨a,(e.net a).attach u⟩)
  | .inr (.inr ⟨a,z⟩) => .inr (.inr ⟨a,(e.net a).dst z⟩)

/-- The exact width formula for the three cable kinds in a bank template. -/
def templateWidth (j : ℕ) (histogram : Fin e.count → ℕ) : TemplateEdge e → ℕ
  | .inl _ => j * Nat.clog 2 e.count
  | .inr (.inl (a,_)) => histogram a * m
  | .inr (.inr ⟨a,z⟩) => histogram a * (e.net a).width z

variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

/-- Source, destination and width accessors for retained old bands in the actual sewn layout. -/
theorem retained_fields
    (c : {c : (layout p.layout bin perm m).Edge // c ∉ (partition p.layout bin perm m).selected}) :
    let L := (output e p bin perm positive first q).layout
    let z : L.Edge := .inr (.inl c)
    L.src z = .inl (p.layout.src c.val.1) ∧ L.dst z = .inl (p.layout.dst c.val.1) ∧
      L.width z = (layout p.layout bin perm m).width c.val := ⟨rfl,rfl,rfl⟩

/-- All bank endpoint and width columns come from the fixed template and actual public histogram. -/
theorem bank_fields (a : A) (u : TemplateEdge e) :
    let L := (output e p bin perm positive first q).layout
    let z : L.Edge := .inr (.inr ⟨a,u⟩)
    L.src z = .inr ⟨a,templateSrc e u⟩ ∧ L.dst z = .inr ⟨a,templateDst e u⟩ ∧
      L.width z = templateWidth e (blocks p.layout bin perm m a) (q a).val u := by
  rcases u with _ | ⟨u,v⟩ | ⟨u,z⟩ <;> exact ⟨rfl,rfl,rfl⟩

/-- The global hook name of one concrete selected cable endpoint. -/
noncomputable def seedHook (a : A) (d : Fin D) (c : {c : p.layout.Edge // bin c = some (perm d a)})
    (source : Bool) : EdgeShape e p bin perm :=
  .inl ((partition p.layout bin perm m).includePort a (cutSlot p.layout bin perm m a d c source))

/-- The public endpoint row gives the exact attachment sites and width of its sewn hook.
In particular no inverse search over the selected cables is needed at a terminal. -/
theorem hook_fields (binName : A → ℕ) (a : A) (d : Fin D)
    (c : {c : p.layout.Edge // bin c = some (perm d a)}) (source : Bool) :
    let L := (output e p bin perm positive first q).layout
    let z := seedHook e p bin perm a d c source
    L.src z = .inl (if source then p.layout.src c.val else p.layout.dst c.val) ∧
      L.dst z = .inr ⟨a,.inr (.inl (d, if source then positive c.val else !(positive c.val)))⟩ ∧
      L.width z = (descriptor p.layout bin perm m binName c (some (d,true))).span := by
  let t := partition p.layout bin perm m
  let j := blocks p.layout bin perm m
  let b := bundle p.layout bin perm m positive
  let G := seedNetwork e j (p := pieces (m := m) p bin perm) t b q
  have hg := t.attach_include G a (cutSlot p.layout bin perm m a d c source)
  refine ⟨?_,?_,?_⟩
  · cases source <;> rfl
  · change Sum.inr ((t.parallel G).attach (t.includePort a (cutSlot p.layout bin perm m a d c source))) = _
    rw [hg]
    cases source <;> rfl
  · cases source <;> exact descriptor_width p.layout bin perm m binName c (some (d,true))

end Shortening.StaticRows

end BorderVNP
end Computability
end OAI
