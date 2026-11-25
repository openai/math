import OAI.Computability.BorderVNP.ShortenStaticRowEmit
import OAI.Computability.BorderVNP.ShortenStaticRowCircuitCorrect
import OAI.Computability.BorderVNP.ShortenSeedDescriptorFrozen

/-!
# End-to-end shared Boolean circuit for the three old-cable rectangles

Given the computed interval spans, inverse seed IDs and old public row
columns, this one circuit emits every old-cable row of every sewn histogram
branch, including all virtual padding loops. Unused seed words may have any
value: the terminal-address capacity test is needed only at an occupied hook.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.StaticRows.Serializer

open Crossing SeedIntervals CombiningStep StaticTerminalCircuit VPVNP.VerifierNetwork ParseBatchSort
open scoped Classical

variable {D m nEdges nSites nSeeds : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
variable (oldSite : p.layout.Site ↪ Fin nSites) (old : p.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds)
variable (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A)

/-- Physical span supplied by the cut stage on charged and frozen old cables. -/
noncomputable def emittedSpan (c : p.layout.Edge) (b : Band D) : ℕ :=
  match h : bin c with
  | none => (frozenDescriptor p.layout 0 c b).span
  | some a => (descriptor p.layout bin perm m (fun a => (seed a).val) (⟨c,h⟩ : {c // bin c = some a}) b).span

omit [Field K] [Fintype A] in
/-- Both descriptor cases supply the exact width of the corresponding old band. -/
theorem emittedSpan_eq (c : p.layout.Edge) (b : Band D) :
    emittedSpan (m := m) p bin perm seed c b = (SeedIntervals.layout p.layout bin perm m).width (c,b) := by
  unfold emittedSpan
  split
  · rename_i h
    exact (frozen_width p.layout bin perm m 0 c h b).symm
  · rename_i a h
    exact (descriptor_width p.layout bin perm m (fun a => (seed a).val) (⟨c,h⟩ : {c // bin c = some a}) b).symm

/-- Source-stage correspondence for one candidate row. The seed operand is constrained only
for matched-prefix rows with an actual bin. The span is the preceding cut circuit's result. -/
structure DirectoryRepresents (r : Row nEdges D) (flag : Flag → Bool) (v : DirectoryWord → ℕ) : Prop where
  /-- Old record occupancy in the public rectangle. -/
  occupied : flag .occupied = true ↔ r.1 ∈ Set.range old
  /-- Each occupied old row carries its actual charge and orientation bits. -/
  flags : ∀ c, old c = r.1 → flag .charged = (bin c).isSome ∧ flag .positive = positive c
  /-- Old endpoint site names and retained bit count supplied to the mux. -/
  fields : ∀ c, old c = r.1 → v .oldSrc = (oldSite (p.layout.src c)).val ∧
    v .oldDst = (oldSite (p.layout.dst c)).val ∧ v .span = emittedSpan (m := m) p bin perm seed c r.2.1
  /-- Destination site for unused virtual rows. -/
  padding : v .pad =
    (siteRows e p oldSite seed (dummy (Packing.Names.rowSlot (bandCandidate e nSeeds r.2.2 r.1 r.2.1)))).val
  /-- Inverting the public bin permutation recovers the seed number for either hook. -/
  seedNumber : ∀ c, old c = r.1 → ∀ d, r.2.1 = some (d,true) → ∀ a, bin c = some a →
    v .seed = (seed ((perm d).symm a)).val

variable {e p bin perm positive oldSite old seed dummy} {r : Row nEdges D} {flag : Flag → Bool}
variable {v : DirectoryWord → ℕ}

omit [Fintype A] in
/-- The arithmetic computation of both terminal identifiers supplies the exact mux input
columns required for the physically sewn row. -/
theorem DirectoryRepresents.expanded
    (h : DirectoryRepresents e p bin perm positive oldSite old seed dummy r flag v) :
    Represents e p bin perm positive oldSite old seed dummy r.2.2 r.1 r.2.1 flag
      (expandWords e nSites (direction r.2.1) v) where
  occupied := h.occupied
  charged c hc := (h.flags c hc).1
  orientation c hc := (h.flags c hc).2
  src c hc := (h.fields c hc).1
  dst c hc := (h.fields c hc).2.1
  span c hc := (h.fields c hc).2.2.trans (emittedSpan_eq _ _ _ _ _ _)
  pad := h.padding
  terminal := by
    intro c hc d hb a ha side
    have hid := h.seedNumber c hc d hb a ha
    cases side <;> simp only [expandWords,hb,direction,Option.elim_some,hid] <;> rfl

/-- Every used inverse-seed address fits in the allocated global site-ID field, regardless
of the contents of the unused seed operands of absent or retained candidates. -/
theorem DirectoryRepresents.usedAddressFits
    (h : DirectoryRepresents e p bin perm positive oldSite old seed dummy r flag v) {w : ℕ}
    (hc : siteCapacity e nSites nSeeds ≤ 2^w)
    (hused : enabled r.2.2 (isPrefix r.2.1) flag = true) (hkind : r.2.2.val < 2) (side : Bool) :
    address e nSites (direction r.2.1) side (v .seed) < 2^w := by
  obtain ⟨c,hr,hs⟩ := (bandCandidate_mem_iff e p bin perm old seed _ _ _).mp (h.expanded.enabled_iff.mp hused)
  obtain ⟨ht,d,hb⟩ := (selected_iff p bin perm _ _).mp (hs.mpr hkind)
  cases ha : bin c with
  | none => simp [ha] at ht
  | some a =>
    rw [h.seedNumber c hr d hb a ha]
    exact address_fits e nSites nSeeds w _ _ (seed ((perm d).symm a)).isLt hc

/-- A single shared Boolean circuit returns exact occupancy, source, destination and width
for every reserved hook/retained slot on every histogram branch. -/
theorem exists_physical_oldRows {σ : Type*} [Fintype σ] (e : PaidIdentity K D m) (nSites nEdges w : ℕ)
    (source : Frame σ (Row nEdges D × DirectoryInput w)) :
    ∃ f : Frame σ (Row nEdges D × Output w),
      f.size ≤ source.size + 1 + nEdges * (2*D+1) * 3 *
        (2 * nodeBudget e * (100*(w+1)^2) + 64*(1+3*w)) ∧
      ∀ {P : Type*} {bits : P → ℕ} {A : Type} [Fintype A] {nSeeds : ℕ}
        (p : Pack D P bits K) (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
        (positive : p.layout.Edge → Bool) (oldSite : p.layout.Site ↪ Fin nSites)
        (old : p.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds)
        (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A)
        (x : σ → Bool) (r : Row nEdges D),
        siteCapacity e nSites nSeeds ≤ 2^w →
        DirectoryRepresents e p bin perm positive oldSite old seed dummy r
          (fun t => source.eval x (r,.inl t))
          (fun t => value (fun j => source.eval x (r,.inr (t,j)))) →
        ∀ (first : Fin D × Bool) (q : Counts e p bin perm),
          (f.eval x (r,.inl ()) = true ↔ bandCandidate e nSeeds r.2.2 r.1 r.2.1 ∈
            Set.range (outputRows e p bin perm positive first q old seed)) ∧
          ∀ c, value (fun j => f.eval x (r,.inr (c,j))) =
            paddedField e p bin perm positive oldSite old seed dummy r.2.2 r.1 r.2.1 first q c := by
  obtain ⟨f,hsize,hf⟩ := exists_oldBandFrame e nSites nEdges w source
  refine ⟨f,hsize,?_⟩
  intro P bits A _ nSeeds p bin perm positive oldSite old seed dummy x r hc hr first q
  have he := hf x r (hr.usedAddressFits hc)
  have hs := hr.expanded.correct first q
  exact ⟨he.1 ▸ hs.1,fun c => (he.2 c).trans (hs.2 c)⟩

end Shortening.StaticRows.Serializer

end BorderVNP
end Computability
end OAI
