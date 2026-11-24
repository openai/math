import OAI.Computability.VPVNP.CompressorRecordPlacement
import OAI.Computability.VPVNP.SlotDemandKernel
import Mathlib.Data.List.NodupEquivFin

/-!
# Scanning original wires into the two lists of each packed bundle

In the first scan of Appendix E, an arc thick at both ends belongs to the
payload of its source bundle. Every other arc is a CD motif assigned to the
bundle of its thin C endpoint. The classified arc directory supplies one row
identifier per original arc. The native bounded-append pass then visits each
original arc once, recording its identifier in exactly one row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleLists

open Compression Compression.PackingData BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- The filtered physical identifiers are exactly those earlier than the cursor
which map to the row's owner. -/
theorem mem_preimagePrefix_iff (place : Word w → Word w) (owner i : Word w)
    (k : ℕ) (hk : k ≤ 2 ^ w) :
    i ∈ preimagePrefix place owner k ↔ i.val < k ∧ place i = owner := by
  simp only [preimagePrefix, List.mem_filter, List.mem_map, List.mem_range, beq_iff_eq]
  apply and_congr_left
  intro _
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt (hj.trans_le hk)] using hj
  · intro hi
    exact ⟨i.val, hi, Fin.ext (Nat.mod_eq_of_lt i.isLt)⟩

/-- In a representable range, filtering the consecutive word identifiers keeps
their strict numeric order. -/
theorem preimagePrefix_pairwise (place : Word w → Word w) (owner : Word w)
    (k : ℕ) (hk : k ≤ 2 ^ w) :
    (preimagePrefix place owner k).Pairwise (· < ·) := by
  apply List.Pairwise.filter
  apply List.pairwise_map.mpr
  refine List.pairwise_lt_range.imp_of_mem ?_
  intro a b ha hb hab
  change a % (2 ^ w) < b % (2 ^ w)
  simpa only [Nat.mod_eq_of_lt ((List.mem_range.mp ha).trans_le hk),
    Nat.mod_eq_of_lt ((List.mem_range.mp hb).trans_le hk)] using hab

/-- Looking up the number of preceding identifiers in an owner's row recovers
the identifier at that rank. -/
theorem preimagePrefix_get_at_rank (place : Word w → Word w) (owner i : Word w)
    (k : ℕ) (hi : i.val < k) (hp : place i = owner) :
    ∃ h : (preimagePrefix place owner i.val).length < (preimagePrefix place owner k).length,
      (preimagePrefix place owner k)[(preimagePrefix place owner i.val).length]'h = i := by
  have cast : Fin.ofNat (2 ^ w) i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have step : preimagePrefix place owner (i.val + 1) = preimagePrefix place owner i.val ++ [i] := by
    simp only [preimagePrefix, List.range_succ, List.map_append, List.map_singleton, List.filter_append,
      cast, List.filter_cons, List.filter_nil, beq_iff_eq, hp, ite_true]
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hi
  have pref : preimagePrefix place owner (i.val + 1) <+: preimagePrefix place owner k := by
    conv_rhs => arg 3; rw [hn]
    conv_rhs => rw [preimagePrefix, List.range_add, List.map_append, List.filter_append]
    exact List.prefix_append _ _
  rw [step] at pref
  have hidx : (preimagePrefix place owner i.val).length <
      (preimagePrefix place owner i.val ++ [i]).length := by simp
  refine ⟨hidx.trans_le pref.length_le, ?_⟩
  rw [← pref.getElem hidx, List.getElem_append_right (le_refl _)]
  simp

variable {V H Tag L : Type} {d c A n : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- A packed site and one of its outgoing slots, identifying the bundle at that port. -/
abbrev Port (V Tag L : Type*) (d : ℕ) := Site V Tag L × Fin d
/-- The choice of a thick-wire payload row or a CD motif row at a packed port. -/
abbrev Bucket (V Tag L : Type*) (d : ℕ) := Port V Tag L d ⊕ Port V Tag L d

/-- The left summand receives thick wires, the right summand receives motifs. -/
def bucketOf (a : Arc V H Tag L d c) : Bucket V Tag L d :=
  if h : P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a))
  then .inl a.1 else .inr (P.bundle ⟨a,h⟩)

@[simp] theorem bucketOf_thick (a : P.ThickWire) : bucketOf P a.val = .inl a.val.1 := by
  simp [bucketOf, a.prop]

@[simp] theorem bucketOf_motif (m : P.Motif) : bucketOf P m.val = .inr (P.bundle m) := by
  simp [bucketOf, m.prop]

/-- The left row over a port consists of exactly its original thick wires. -/
def thickEquiv (b : Port V Tag L d) : {a // bucketOf P a = .inl b} ≃ P.ThickFiber b where
  toFun x := by
    have h : P.thick (sourcePosition x.val) ∧ P.thick (sourcePosition (P.actual x.val)) := by
      by_contra hn
      simpa [bucketOf, hn] using x.prop
    exact ⟨⟨x.val,h⟩, by simpa [bucketOf,h] using x.prop⟩
  invFun x := ⟨x.val.val, (bucketOf_thick P x.val).trans (congrArg Sum.inl x.prop)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-- The right row over a port consists of exactly its assigned CD motifs. -/
def motifEquiv (b : Port V Tag L d) : {a // bucketOf P a = .inr b} ≃ P.MotifFiber b where
  toFun x := by
    have h : ¬ (P.thick (sourcePosition x.val) ∧ P.thick (sourcePosition (P.actual x.val))) := by
      intro ht
      simpa [bucketOf, ht] using x.prop
    exact ⟨⟨x.val,h⟩, by simpa [bucketOf,h] using x.prop⟩
  invFun x := ⟨x.val.val, (bucketOf_motif P x.val).trans (congrArg Sum.inr x.prop)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-- Contiguous bundle indices, with slot number varying fastest. -/
def portIndex (site : Site V Tag L ≃ Fin n) : Port V Tag L d ≃ Fin (n*d) :=
  (site.prodCongr (Equiv.refl (Fin d))).trans finProdFinEquiv

/-- Number the thick-wire rows first and the CD motif rows second, using the same site-and-slot
order in each half. -/
def bucketIndex (site : Site V Tag L ≃ Fin n) : Bucket V Tag L d ≃ Fin (n*d+n*d) :=
  ((portIndex site).sumCongr (portIndex site)).trans finSumFinEquiv

omit [AddCommGroup Tag] [AddCommGroup L] in
theorem bucketIndex_thick_val (site : Site V Tag L ≃ Fin n) (b : Port V Tag L d) :
    (bucketIndex site (.inl b)).val = (site b.1).val * d + b.2.val := by
  change b.2.val + d * (site b.1).val = _
  ac_rfl

omit [AddCommGroup Tag] [AddCommGroup L] in
theorem bucketIndex_motif_val (site : Site V Tag L ≃ Fin n) (b : Port V Tag L d) :
    (bucketIndex site (.inr b)).val = n*d + ((site b.1).val * d + b.2.val) := by
  change n*d + (b.2.val + d * (site b.1).val) = _
  ac_rfl

variable (arcs : Arc V H Tag L d c ≃ Fin A) (site : Site V Tag L ≃ Fin n)

/-- Map a physical old arc identifier to the encoded row that collects it during bounded
append. -/
def wordOwner : Word w → Word w := encodedPlacement arcs (bucketIndex site) (bucketOf P)

/-- The ordered list of original arc identifiers for a classified row. -/
def arcList (b : Bucket V Tag L d) : List (Word w) :=
  preimagePrefix (wordOwner P arcs site) (Fin.ofNat _ (bucketIndex site b).val) A

theorem wordOwner_at (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w) (a : Arc V H Tag L d c) :
    wordOwner P arcs site (Fin.ofNat (2^w) (arcs a).val) =
      Fin.ofNat _ (bucketIndex site (bucketOf P a)).val := by
  apply Fin.ext
  rw [wordOwner, encodedPlacement_eq arcs (bucketIndex site) (bucketOf P) hA hn,
    Equiv.symm_apply_apply, Fin.val_ofNat, Nat.mod_eq_of_lt ((bucketIndex site _).isLt.trans_le hn)]

/-- Physical row membership of an original wire in either summand. -/
theorem mem_arcList_iff (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w) (a : Arc V H Tag L d c)
    (b : Bucket V Tag L d) :
    Fin.ofNat (2^w) (arcs a).val ∈ arcList P arcs site b ↔ bucketOf P a = b := by
  rw [arcList, mem_preimagePrefix_iff _ _ _ _ hA, wordOwner_at P arcs site hA hn a]
  simp only [Fin.val_ofNat, Nat.mod_eq_of_lt ((arcs a).isLt.trans_le hA), (arcs a).isLt,
    true_and, Fin.ext_iff, Nat.mod_eq_of_lt ((bucketIndex site _).isLt.trans_le hn)]
  exact Fin.val_injective.eq_iff.trans (bucketIndex site).injective.eq_iff

theorem arcList_nodup (hA : A ≤ 2^w) (b : Bucket V Tag L d) :
    (arcList (w := w) P arcs site b).Nodup :=
  (preimagePrefix_pairwise _ _ _ hA).imp fun h ↦ h.ne

/-- Decode a stored arc ID to the corresponding member of the typed fiber. -/
def memberEquiv (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w) (b : Bucket V Tag L d) :
    {i // i ∈ arcList (w := w) P arcs site b} ≃ {a // bucketOf P a = b} where
  toFun i := by
    have hi := ((mem_preimagePrefix_iff _ _ _ _ hA).mp i.prop).1
    let a := arcs.symm ⟨i.val.val,hi⟩
    have eqn : Fin.ofNat (2^w) (arcs a).val = i.val := by
      rw [show arcs a = _ from arcs.apply_symm_apply _]; exact Fin.ext (Nat.mod_eq_of_lt i.val.isLt)
    exact ⟨a,(mem_arcList_iff P arcs site hA hn a b).mp (eqn ▸ i.prop)⟩
  invFun a := ⟨Fin.ofNat _ (arcs a.val).val,(mem_arcList_iff P arcs site hA hn _ b).mpr a.prop⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv a := by
    apply Subtype.ext
    apply arcs.injective
    simpa only [Equiv.apply_symm_apply, Fin.ext_iff, Fin.val_ofNat] using Nat.mod_eq_of_lt ((arcs a.val).isLt.trans_le hA)

/-- Scan-order numbering of the complete fiber. Reading a cell at this
ordinal and decoding its original arc identifier implements this equivalence. -/
def ordinalEquiv (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w) (b : Bucket V Tag L d) :
    Fin (arcList (w := w) P arcs site b).length ≃ {a // bucketOf P a = b} :=
  (List.Nodup.getEquiv _ (arcList_nodup P arcs site hA b)).trans (memberEquiv P arcs site hA hn b)

theorem ordinalEquiv_id (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w) (b : Bucket V Tag L d)
    (i : Fin (arcList (w := w) P arcs site b).length) :
    (arcList P arcs site b).get i = Fin.ofNat (2^w) (arcs (ordinalEquiv P arcs site hA hn b i).val).val :=
  (congrArg Subtype.val ((memberEquiv P arcs site hA hn b).symm_apply_apply
    ((List.Nodup.getEquiv _ (arcList_nodup P arcs site hA b)) i))).symm

/-- The number of thick wires or motif pieces expected in a classified bundle row. -/
def rowLength : Bucket V Tag L d → ℕ :=
  Sum.elim (fun _ ↦ 2^c*d/4) (fun _ ↦ pieceCount d c)

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

theorem fiber_card (hc : 2 ≤ c) (b : Bucket V Tag L d) :
    Fintype.card {a // bucketOf P a = b} = rowLength (c := c) b := by
  cases b with
  | inl b => exact (Fintype.card_congr (thickEquiv P b)).trans (P.card_thick_fiber hc b)
  | inr b => exact (Fintype.card_congr (motifEquiv P b)).trans (P.card_motifs_bundle hc b)

theorem arcList_length (hc : 2 ≤ c) (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w)
    (b : Bucket V Tag L d) :
    (arcList (w := w) P arcs site b).length = rowLength (c := c) b :=
  (encodedPlacement_rowLength arcs (bucketIndex site) (bucketOf P) hA hn b).trans
    (fiber_card P hc b)

/-- Once the classification and zero counts occupy their physical arrays,
the native preimage pass fills every bundle's two lists. There is one call
and four external probes per original arc. -/
theorem fill_run (hc : 2 ≤ c) (p : Fin 6 → Word w) (reg : RowRegions p)
    (hA : (p 0).val = A) (hn : (p 2).val = n*d+n*d) (hcap : pieceCount d c ≤ (p 4).val)
    (mem : Memory w) (owners : ∀ i : Word w, i < p 0 → ownerAt p mem i = wordOwner P arcs site i)
    (zero : ∀ u : Word w, u < p 2 → mem (countAt p u).val = 0) :
    let M := (template collectPreimage 3).instantiate w p
    ∃ rs, runSegment M.program 23 (some 0) mem (List.replicate A []) = some rs ∧
      PreimagesAt p (wordOwner P arcs site) (after mem (eventLog rs)) A ∧
      (∀ b : Bucket V Tag L d, let u := Fin.ofNat (2^w) (bucketIndex site b).val
        rowRepresents (after mem (eventLog rs)) (countAt p u) (rowAt p u) (arcList P arcs site b)) ∧
      rs.length = A ∧ RAMBuckets.cost Report.probes rs = 5*A ∧
      ∀ r ∈ rs, r.events.length = 22 := by
  intro M
  have ha : A ≤ 2^w := hA ▸ (p 0).isLt.le
  have hb : n*d+n*d ≤ 2^w := hn ▸ (p 2).isLt.le
  have legal (i : Word w) (hi : i < p 0) : wordOwner P arcs site i < p 2 := by
    let j : Fin A := ⟨i.val, hA ▸ hi⟩
    have e : Fin.ofNat (2^w) j.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    change (encodedPlacement _ _ _ i).val < (p 2).val
    rw [← e, encodedPlacement_eq arcs (bucketIndex site) (bucketOf P) ha hb j, hn]
    exact (bucketIndex site _).isLt
  have capacity (u : Word w) (hu : u < p 2) :
      (preimagePrefix (wordOwner P arcs site) u (p 0).val).length ≤ (p 4).val := by
    let j : Fin (n*d+n*d) := ⟨u.val, hn ▸ hu⟩
    obtain ⟨b, he⟩ := (bucketIndex site (d := d)).surjective j
    have eu : Fin.ofNat (2^w) (bucketIndex site b).val = u := by
      rw [he]; exact Fin.ext (Nat.mod_eq_of_lt u.isLt)
    rw [← eu, hA]
    change (arcList P arcs site b).length ≤ _
    rw [arcList_length P arcs site hc ha hb]
    cases b with
    | inl b =>
      apply le_trans _ hcap
      exact Nat.div_le_div_right (by omega : 2^c*d ≤ 3*(2^c*d))
    | inr b => exact hcap
  have start : PreimagesAt p (wordOwner P arcs site) mem 0 := by
    refine ⟨owners, fun u hu ↦ ?_⟩
    simp [preimagePrefix, rowRepresents, zero u hu]
  obtain ⟨rs,hr,hlists,hlen,hwork⟩ := collectPreimages_run reg legal capacity start A (by simp [hA])
  have full : PreimagesAt p (wordOwner P arcs site) (after mem (eventLog rs)) A := by
    simpa only [Nat.zero_add] using hlists
  refine ⟨rs,hr,full,fun b ↦ full.rows _ ?_,hlen,?_,fun r hr' ↦ (hwork r hr').1⟩
  · change (bucketIndex site b).val % (2^w) < (p 2).val
    have h := (bucketIndex site b).isLt
    rw [Nat.mod_eq_of_lt (h.trans_le hb), hn]; exact h
  · exact (preimagePass_cost (fun r hr' ↦ (hwork r hr').2)).trans (by rw [hlen])

end CompressorRecords.BundleLists

end VPVNP
end Computability
end OAI
