import OAI.Computability.BorderVNP.PackedLiveCuts
import OAI.Computability.BorderVNP.PackedInverseSeeds
import OAI.Computability.BorderVNP.ShortenStaticOldRows

/-! # Producing the old-cable part of the successor directory

The incoming site pointers and charge/orientation bits are read at stable cable IDs.
Spans and inverse-seed numbers are computed in batches from the physical inputs. Together
they form the actual source of the old-band, hook and residual serializers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DirectoryCircuit

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows
open VPVNP.VerifierNetwork ParseBatchSort
open scoped Classical

/-- Relabel only the actual cables before allocating their intervals in public row order. -/
noncomputable def densePack {D M : ℕ} {P R : Type*} {bits : P → ℕ} (p : Pack D P bits R)
    (slot : p.layout.Edge ↪ Fin M) : Pack D P bits R :=
  ⟨Names.denseLayout p.layout slot, Names.tables p.layout (Names.denseRank p.layout slot).toEmbedding
    (fun i => p.layout.src ((Names.denseRank p.layout slot).symm i)) p.2⟩

/-- Bit pins copied from the old site/edge table. Padding sites only enter virtual rows. -/
structure Columns (σ : Type*) (M D w : ℕ) where
  /-- True precisely when a sparse old ID carries a cable. -/
  occupied : Fin M → σ
  /-- Orientation of the old cable in the selected bin. -/
  positive : Fin M → σ
  /-- Stable names of its source and target sites. -/
  endpoint : Fin M → Bool → Fin w → σ
  /-- Stable destination site of a virtual slot. -/
  padding : Serializer.Row M D → Fin w → σ

private abbrev Stage (σ : Type*) (M D w : ℕ) :=
  σ ⊕ (((Fin M × Band D) × CutCircuit.Result × Fin w) ⊕ (Fin M × Fin D × Fin w))

private def select {σ : Type*} {M D k w : ℕ} [NeZero D] (p : PublicPopulation.Pins (Fin M) σ k w)
    (col : Columns σ M D w) (z : Serializer.Row M D × Serializer.DirectoryInput w) : Stage σ M D w :=
  let r := z.1
  match z.2 with
  | .inl .occupied => .inl (col.occupied r.1)
  | .inl .charged => .inl (p.active r.1)
  | .inl .positive => .inl (col.positive r.1)
  | .inr (.oldSrc,j) => .inl (col.endpoint r.1 true j)
  | .inr (.oldDst,j) => .inl (col.endpoint r.1 false j)
  | .inr (.pad,j) => .inl (col.padding r j)
  | .inr (.span,j) => .inr (.inl ((r.1,r.2.1),.span,j))
  | .inr (.seed,j) => .inr (.inr (r.1,r.2.1.elim 0 Prod.fst,j))

private theorem span_eq {D m M : ℕ} [NeZero D] {K : Type*} {P : Type*} {bits : P → ℕ}
    (p : Pack D P bits K) (slot : p.layout.Edge ↪ Fin M) {A : Type} (bin : p.layout.Edge → Option A)
    (perm : Fin D → Equiv.Perm A) (names : A → ℕ) (c : p.layout.Edge) (b : Band D) :
    (CutCircuit.liveDescriptor p.layout slot bin perm m names c b).span =
      (layout (densePack p slot).layout (CutCircuit.denseBin p.layout slot bin) perm m).width
        (Names.denseSlot p.layout slot c,b) := by
  cases hb : bin c with
  | none =>
    rw [CutCircuit.live_frozen p.layout slot bin perm m names c hb b]
    apply Eq.symm
    apply frozen_width
    simpa only [CutCircuit.denseBin,Function.comp_apply,Equiv.symm_apply_apply] using hb
  | some a =>
    rw [CutCircuit.live_charged p.layout slot bin perm m names c a hb b]
    exact (descriptor_width _ _ _ _ _ _ _).symm

/-- Assemble every row required by the old-band serializer on the same physical dense pack.
The frame is selected before the old layout, its table entries, bins and orientations. -/
theorem old_directory_frames {D m : ℕ} [NeZero D] {K : Type*} [Field K]
    (e : PaidIdentity K D m) (hm : 0 < m) :
    ∃ C E : ℕ, ∀ (nSites M nSeeds k w : ℕ) {A : Type} {σ : Type*} [Fintype A] [Fintype σ]
      (p : PublicPopulation.Pins (Fin M) σ k w) (col : Columns σ M D w) (code : A ↪ Fin (2^k))
      (seed : A ≃ Fin nSeeds) (perm : Fin D → Equiv.Perm A), nSeeds ≤ 2^w →
      ∃ f : Frame σ (Serializer.Row M D × Serializer.DirectoryInput w),
        f.size ≤ (PublicPopulation.offsets p).size +
          PoolCircuit.scatterCost (Fintype.card A) M D C E k w +
          M*Fintype.card (Band D)*(48*w) + 1 + M*Fintype.card (Band D)*(3300*(w+1)^2) +
          (1 + D * (2*(Fintype.card A+M+1)*PublicPopulation.laneCost
            (Nat.clog 2 (Fintype.card A+M)) k w)) ∧
        ∀ {P : Type*} {bits : P → ℕ} (pack : Pack D P bits K) (bin : pack.layout.Edge → Option A)
          (positive : pack.layout.Edge → Bool) (oldSite : pack.layout.Site ↪ Fin nSites)
          (slot : pack.layout.Edge ↪ Fin M) (x : σ → Bool)
          (dummy : Fin (edgeCapacity e M nSeeds) → SiteShape e (densePack pack slot) A),
          PublicPopulation.Represents p pack.layout bin slot code x →
          (∀ a, count pack.layout bin a < 2^w) →
          (∀ c, value (x ∘ p.width (slot c)) = pack.layout.width c) →
          (∀ u, x (col.occupied u) = true ↔ u ∈ Set.range slot) →
          (∀ c, x (col.positive (slot c)) = positive c) →
          (∀ c, value (x ∘ col.endpoint (slot c) true) = (oldSite (pack.layout.src c)).val ∧
            value (x ∘ col.endpoint (slot c) false) = (oldSite (pack.layout.dst c)).val) →
          (∀ r, value (x ∘ col.padding r) = (siteRows e (densePack pack slot) oldSite seed.toEmbedding
            (dummy (Names.rowSlot (bandCandidate e nSeeds r.2.2 r.1 r.2.1)))).val) →
          ∀ r, Serializer.DirectoryRepresents e (densePack pack slot)
            (CutCircuit.denseBin pack.layout slot bin) perm (positive ∘ (Names.denseSlot pack.layout slot).symm)
            oldSite (CutCircuit.denseRows pack.layout slot) seed.toEmbedding dummy r
            (fun t => f.eval x (r,.inl t)) (fun t => value (fun j => f.eval x (r,.inr (t,j)))) := by
  obtain ⟨C,E,sc⟩ := CutCircuit.live_cut_frames D m hm
  refine ⟨C,E,fun nSites M nSeeds k w A σ _ _ p col code seed perm hn => ?_⟩
  obtain ⟨cuts,hc,ec⟩ := sc M k w p code perm
  obtain ⟨inv,hi,ei⟩ := PoolCircuit.inverse_seed_frames D k w p code
    (fun a => (seed a).castLE hn) perm
  let raw := parallelFrame (Frame.initial (id : σ → σ)) (parallelFrame cuts inv)
  let out := raw.select (select p col)
  refine ⟨out,?_,?_⟩
  · simp only [out,Frame.select_size,raw,parallelFrame_size,Frame.initial_size,zero_add]
    exact Nat.add_le_add hc (by simpa only [Fintype.card_fin] using hi)
  · intro P bits pack bin positive oldSite slot x dummy hx fit widths occupied orient endpoints pad r
    let L := (densePack pack slot).layout
    let f := CutCircuit.denseBin pack.layout slot bin
    let old := CutCircuit.denseRows pack.layout slot
    let q := Names.denseSlot pack.layout slot
    have hrow (c : pack.layout.Edge) : old (q c) = slot c := by simp [old,q,CutCircuit.denseRows]
    have hbin (c : pack.layout.Edge) : f (q c) = bin c := by simp [f,q,CutCircuit.denseBin]
    constructor
    · simp only [out,Frame.select_eval,select,raw,parallelFrame_eval_inl,Frame.initial_eval,id_eq,occupied]
      constructor
      · rintro ⟨c,h⟩
        exact ⟨q c,(hrow c).trans h⟩
      · rintro ⟨z,h⟩
        obtain ⟨c,rfl⟩ := q.surjective z
        exact ⟨c,(hrow c).symm.trans h⟩
    · intro z hz
      obtain ⟨c,rfl⟩ := q.surjective z
      have h := (hrow c).symm.trans hz
      simp only [out,Frame.select_eval,select,raw,parallelFrame_eval_inl,Frame.initial_eval,id_eq,← h]
      exact ⟨(hx.active c).trans (congrArg Option.isSome (hbin c).symm),
        (orient c).trans (congrArg positive (q.symm_apply_apply c).symm)⟩
    · intro z hz
      obtain ⟨c,rfl⟩ := q.surjective z
      have h := (hrow c).symm.trans hz
      simp only [out,Frame.select_eval,select,raw,parallelFrame_eval_inl,parallelFrame_eval_inr,
        Frame.initial_eval,id_eq,← h]
      have hsrc : L.src (q c) = pack.layout.src c := Names.src_slot _ _ _ c
      have hdst : L.dst (q c) = pack.layout.dst c := Names.dst_slot _ _ _ c
      refine ⟨(endpoints c).1.trans (congrArg (fun z => (oldSite z).val) hsrc.symm),
        (endpoints c).2.trans (congrArg (fun z => (oldSite z).val) hdst.symm),?_⟩
      exact (ec pack.layout bin slot x hx fit widths c r.2.1 .span).trans
        ((span_eq pack slot bin perm _ c r.2.1).trans (Serializer.emittedSpan_eq _ _ _ _ _ _).symm)
    · simpa only [out,Frame.select_eval,select,raw,parallelFrame_eval_inl,Frame.initial_eval,id_eq,Function.comp_def] using pad r
    · intro z hz d hband a ha
      obtain ⟨c,rfl⟩ := q.surjective z
      have h := (hrow c).symm.trans hz
      have key := hx.address c a ((hbin c).symm.trans ha)
      simpa only [out,Frame.select_eval,select,raw,parallelFrame_eval_inr,← h,hband,
        Option.elim_some,Fin.val_castLE,Equiv.toEmbedding_apply] using ei x (slot c) a key d

end Packing.DirectoryCircuit

end BorderVNP
end Computability
end OAI
