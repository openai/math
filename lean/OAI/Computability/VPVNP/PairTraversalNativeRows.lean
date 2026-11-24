import OAI.Computability.VPVNP.PairTraversalRows
import OAI.Computability.VPVNP.CompressorRecordPlacement
import OAI.Computability.VPVNP.PairTraversalRowExecution

/-!
# From the native placement scan to the ordered children of a site

The descriptor scan enumerates numerical identifiers in increasing order. The
local history reader restricts that same order to the placement fiber. Equality
of these lists keeps their indices aligned even when the placement is many to
one or its fiber is empty.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open NetworkKernel LocalHistory CompressorRecords BurstRAM
open scoped Fin.CommRing

variable {w : ℕ} {I J : Type}

/-- The numerical site identifier stored in a word. -/
def siteWord (w : ℕ) (o : Order I) (x : I) : Word w := Fin.ofNat (2 ^ w) (o.entries.symm x).val

theorem siteWord_injective (o : Order I) (fit : o.length ≤ 2 ^ w) :
    Function.Injective (siteWord w o) := by
  intro x y e
  apply o.entries.symm.injective
  apply Fin.ext
  simpa only [siteWord, Fin.val_ofNat, Nat.mod_eq_of_lt ((o.entries.symm x).isLt.trans_le fit),
    Nat.mod_eq_of_lt ((o.entries.symm y).isLt.trans_le fit)] using congrArg Fin.val e

/-- Each stored owner agrees with the placement on the represented old sites. -/
def RepresentsPlacement (old : Order I) (next : Order J) (place : I → J)
    (physical : Word w → Word w) : Prop :=
  ∀ u, physical (siteWord w old u) = siteWord w next (place u)

theorem encodedPlacement_represents (old : Order I) (next : Order J) (place : I → J)
    (ho : old.length ≤ 2 ^ w) (hn : next.length ≤ 2 ^ w) :
    RepresentsPlacement old next place
      (encodedPlacement (w := w) old.entries.symm next.entries.symm place) := by
  intro u
  apply Fin.ext
  rw [siteWord, encodedPlacement_eq _ _ _ ho hn, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact (Nat.mod_eq_of_lt ((next.entries.symm _).isLt.trans_le hn)).symm

private theorem preimagePrefix_sorted (place : Word w → Word w) (v : Word w)
    {k : ℕ} (fit : k ≤ 2 ^ w) : (preimagePrefix place v k).SortedLT := by
  apply List.Pairwise.sortedLT
  apply List.Pairwise.filter
  apply List.pairwise_map.mpr
  refine List.pairwise_lt_range.imp_of_mem ?_
  intro i j hi hj hij
  change i % (2 ^ w) < j % (2 ^ w)
  rwa [Nat.mod_eq_of_lt ((List.mem_range.mp hi).trans_le fit),
    Nat.mod_eq_of_lt ((List.mem_range.mp hj).trans_le fit)]

private theorem restrict_mono (o : Order I) (P : I → Prop) [Fintype (Subtype P)] :
    StrictMono fun j => o.entries.symm ((o.restrict P).entries j).val := by
  let _ := LinearOrder.lift' (fun x : Subtype P => o.entries.symm x.val)
    (o.entries.symm.injective.comp Subtype.val_injective)
  exact (Fintype.orderIsoFinOfCardEq (Subtype P) rfl).strictMono

/-- The old identifiers in the order chosen by the site's local history reader. -/
def orderedIds (w : ℕ) (old : Order I) (P : I → Prop)
    (children : Order (Subtype P)) : List (Word w) :=
  List.ofFn fun j => siteWord w old (children.entries j).val

/-- The native identifier list equals the restricted order entry by entry. -/
theorem preimagePrefix_eq_orderedIds (old : Order I) (next : Order J) (place : I → J)
    (physical : Word w → Word w) (realizes : RepresentsPlacement old next place physical)
    (ho : old.length ≤ 2 ^ w) (hn : next.length ≤ 2 ^ w) (v : J)
    [Fintype {u // v = place u}] :
    preimagePrefix physical (siteWord w next v) old.length =
      orderedIds w old (fun u => v = place u) (old.restrict _) := by
  let P := fun u => v = place u
  let ord := old.restrict P
  apply (preimagePrefix_sorted physical _ ho).eq_of_mem_iff
  · apply List.sortedLT_ofFn_iff.mpr
    intro i j hij
    change (old.entries.symm (ord.entries i).val).val % (2 ^ w) <
      (old.entries.symm (ord.entries j).val).val % (2 ^ w)
    rw [Nat.mod_eq_of_lt ((old.entries.symm _).isLt.trans_le ho),
      Nat.mod_eq_of_lt ((old.entries.symm _).isLt.trans_le ho)]
    exact restrict_mono old P hij
  · intro x
    simp only [preimagePrefix, List.mem_filter, List.mem_map, List.mem_range,
      beq_iff_eq, orderedIds, List.mem_ofFn]
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hv⟩
      let u := old.entries ⟨k, hk⟩
      have hcode : siteWord w old u = Fin.ofNat _ k := by simp [siteWord, u]
      have hu : v = place u := siteWord_injective next hn (hv.symm.trans ((hcode ▸ realizes u)))
      let child : Subtype P := ⟨u, hu⟩
      refine ⟨ord.entries.symm child, ?_⟩
      change siteWord w old (ord.entries (ord.entries.symm child)).val = _
      rw [Equiv.apply_symm_apply]
      exact hcode
    · rintro ⟨j, rfl⟩
      let child := ord.entries j
      exact ⟨⟨(old.entries.symm child.val).val, (old.entries.symm child.val).isLt, rfl⟩,
        (realizes child.val).trans (congrArg (siteWord w next) child.prop.symm)⟩

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
variable {N : Network} {t : Term A N}

private theorem address_ids (old : Order N.Site) (next : Order t.output.Site)
    (r : TermParsers κ t) (cap previous : ℕ) (i : Fin next.length) :
    (orderedIds w old _ (r.order.children (next.entries i))).map
      (DescriptorRows.address (previous : Word w) ((cap + 2 : ℕ) : Word w)) =
      childWords w cap previous (stepLayer old next r) i := by
  simp only [orderedIds, childWords, stepLayer, List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply, DescriptorRows.address, siteWord, Fin.ofNat_eq_cast, address,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

open Classical in
/-- Apply the native row and header routines to a completed placement scan for a
selected term. The resulting DFS descriptor uses the local parser's exact
child list, with each identifier converted to its preceding-layer address. -/
theorem native_step_row (old : Order N.Site) (next : Order t.output.Site)
    (r : TermParsers κ t) (i : Fin next.length) (physical : Word w → Word w)
    (realizes : RepresentsPlacement old next t.place physical)
    (hchildren : r.order.children (next.entries i) =
      old.restrict (fun u => next.entries i = t.place u))
    (pub : Fin 6 → Word w) (mem : Memory w)
    (oldCount : (pub 0).val = old.length) (newCount : (pub 2).val = next.length)
    (collected : PreimagesAt pub physical mem old.length)
    (state : Word w) (priv : Word w → Word w) (cap previous base : ℕ)
    (sourceBefore : (rowAt pub (siteWord w next (next.entries i))).val +
      ((stepLayer old next r).ids i).length ≤ address cap base i.val + 2)
    (countBefore : (countAt pub (siteWord w next (next.entries i))).val <
      address cap base i.val + 2)
    (fit : address cap base i.val + 2 + ((stepLayer old next r).ids i).length < 2 ^ w) :
    let owner := siteWord w next (next.entries i)
    let node := address cap base i.val
    let ids := orderedIds w old _ (r.order.children (next.entries i))
    ∃ es, DescriptorRows.NativePass Fin.elim0 state priv mem node (rowAt pub owner).val
      (node + 2) (countAt pub owner) (previous : Word w) ((cap + 2 : ℕ) : Word w) ids es ∧
      DFS.Row (after mem es) node (node + 2)
        (childWords w cap previous (stepLayer old next r) i) := by
  let owner := siteWord w next (next.entries i)
  let ids := orderedIds w old _ (r.order.children (next.entries i))
  let node := address cap base i.val
  have ho : old.length ≤ 2 ^ w := oldCount ▸ (pub 0).isLt.le
  have hn : next.length ≤ 2 ^ w := newCount ▸ (pub 2).isLt.le
  have valid : owner < pub 2 := by
    change (next.entries.symm (next.entries i)).val % (2 ^ w) < (pub 2).val
    rw [Equiv.symm_apply_apply, Nat.mod_eq_of_lt (i.isLt.trans_le hn), newCount]
    exact i.isLt
  have hids : preimagePrefix physical owner old.length = ids := by
    unfold ids
    rw [hchildren]
    exact preimagePrefix_eq_orderedIds old next t.place physical realizes ho hn (next.entries i)
  have hrow := collected.rows owner valid
  rw [hids] at hrow
  have len : ids.length = ((stepLayer old next r).ids i).length := by
    simp only [ids, orderedIds, stepLayer, List.length_ofFn]
  obtain ⟨es, pass⟩ := DescriptorRows.native_pass Fin.elim0 state priv mem node
    (rowAt pub owner).val (node + 2) (countAt pub owner) (previous : Word w)
    ((cap + 2 : ℕ) : Word w) ids (by simpa using hrow) (len ▸ sourceBefore)
    countBefore (by omega) (len ▸ fit)
  exact ⟨es, pass, (address_ids old next r cap previous i) ▸ pass.row⟩

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
