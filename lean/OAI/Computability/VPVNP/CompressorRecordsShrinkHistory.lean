import OAI.Computability.VPVNP.CompressorRecordsShrinkPreimages
import OAI.Computability.VPVNP.ShrinkFieldBounds

/-!
# Ordered resident hidden fields and maps of a shrinking history node

Each dense motif/type or motif/party ordinal is appended exactly once to its
packed owner. Reading the resulting row recovers the same restricted order
as the mathematical parser, including occurrences sharing a motif or owner.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkHistoryRows

open Compression Compression.PackingData BurstRAM PrimedStackRAM PairSimulation.LocalHistory PairSimulation.TraversalRows
open scoped Classical Fin.CommRing

variable {I J : Type} [Fintype I] [DecidableEq J] {w : ℕ}

/-- Restrict an existing enumeration to entries whose placement equals the given owner,
retaining their original order. -/
abbrev residents (old : Order I) (place : I → J) (v : J) := old.restrict (fun u => v = place u)

/-- The four or six low-order role digits remain part of the stored identifier. -/
structure Directory (old : Order I) (next : Order J) (place : I → J) (p : Fin 6 → Word w)
    (mem : Memory w) : Prop where
  count (v : J) : (mem ((p 3).val+(next.entries.symm v).val)).val = (residents old place v).length
  idAt (v : J) (j : Fin (residents old place v).length) :
    mem ((p 5).val+(next.entries.symm v).val*(p 4).val+j.val) = siteWord w old ((residents old place v).entries j).val

open private countAt_val rowAt_val from OAI.Computability.VPVNP.CompressorRecordPreimageScan

theorem directory_of_rows (old : Order I) (next : Order J) (place : I → J)
    (p : Fin 6 → Word w) (areas : RowRegions p) (ho : (p 0).val = old.length) (hn : (p 2).val = next.length)
    (mem : Memory w) (h : PreimagesAt p (encodedPlacement old.entries.symm next.entries.symm place) mem old.length) :
    Directory old next place p mem := by
  have oldFits := ho ▸ (p 0).isLt.le
  have newFits := hn ▸ (p 2).isLt.le
  have hv (v : J) : (siteWord w next v).val = (next.entries.symm v).val :=
    Nat.mod_eq_of_lt ((next.entries.symm v).isLt.trans_le newFits)
  have valid (v : J) : siteWord w next v < p 2 := by
    change (siteWord w next v).val < (p 2).val
    rw [hv,hn]
    exact (next.entries.symm v).isLt
  let physical := encodedPlacement (w := w) old.entries.symm next.entries.symm place
  have eq (v : J) := preimagePrefix_eq_orderedIds old next place physical
    (encodedPlacement_represents old next place oldFits newFits) oldFits newFits v
  have row (v : J) := h.rows (siteWord w next v) (valid v)
  constructor
  · intro v
    have h := (row v).1
    rw [countAt_val areas (valid v),hv,eq] at h
    simpa only [orderedIds,List.length_ofFn] using h
  · intro v j
    have h := (row v).2
    rw [eq] at h
    have a := h ⟨j.val,by simpa only [orderedIds,List.length_ofFn] using j.isLt⟩
    rw [rowAt_val areas (valid v),hv] at a
    simpa only [orderedIds,List.getElem_ofFn] using a

/-- Clear the chosen site's counters and append each dense occurrence through
the native four-probe collector. The row capacity follows from the typed
fiber cardinality, independently of the chosen layout and the bit assignments. -/
theorem build (old : Order I) (next : Order J) (place : I → J) (p : Fin 6 → Word w)
    (areas : RowRegions p) (ho : (p 0).val = old.length) (hn : (p 2).val = next.length)
    (hcap : ∀ v : J, Fintype.card {u : I // place u = v} ≤ (p 4).val) (mem : Memory w)
    (owner : ∀ i : Word w, i < p 0 → ownerAt p mem i = encodedPlacement old.entries.symm next.entries.symm place i) :
    ∃ cs rs, let mid := after mem (eventLog cs)
      let out := after mid (eventLog rs)
      runSegment ((template SliceRAM.clearOps 0).instantiate w (fun _ => p 3)).program 8
        (some 0) mem (List.replicate next.length []) = some cs ∧
      runSegment ((template collectPreimage 3).instantiate w p).program 23
        (some 0) mid (List.replicate old.length []) = some rs ∧
      Directory old next place p out ∧ cs.length=next.length ∧ rs.length=old.length ∧
      (∀ r ∈ cs, r.probes=1 ∧ r.events.length+1=8) ∧ (∀ r ∈ rs, r.probes=4 ∧ r.events.length+1=23) ∧
      (∀ j, OutsidePreimageWrites p j → out j = mem j) := by
  have hOld := ho ▸ (p 0).isLt
  have hNew := hn ▸ (p 2).isLt
  have upper := hn ▸ areas.countsBeforeRows
  obtain ⟨cs,clear,zero,frame,_,clen,cwork⟩ :=
    SliceRAM.clearPass_run (p 3) next.length (upper.trans (p 5).isLt.le) hNew mem
  let mid := after mem (eventLog cs)
  let phys := encodedPlacement (w := w) old.entries.symm next.entries.symm place
  have live (i : Word w) (hi : i < p 0) : ownerAt p mid i = phys i := by
    change mid (p 1+i).val = phys i
    have small : (p 1+i).val < (p 3).val := (Nat.mod_le ..).trans_lt
      ((Nat.add_lt_add_left hi _).trans_le areas.ownersBeforeCounts)
    rw [show mid (p 1+i).val = mem (p 1+i).val from frame _ (.inl small)]
    exact owner i hi
  have legal (i : Word w) (hi : i < p 0) : phys i < p 2 := by
    let j : Fin old.length := ⟨i.val,ho ▸ hi⟩
    have e : Fin.ofNat (2^w) j.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    change (encodedPlacement _ _ _ i).val < (p 2).val
    rw [← e,encodedPlacement_eq old.entries.symm next.entries.symm place hOld.le hNew.le j,hn]
    exact (next.entries.symm _).isLt
  have cap (v : Word w) (hv : v < p 2) : (preimagePrefix phys v (p 0).val).length ≤ (p 4).val := by
    let j : Fin next.length := ⟨v.val,hn ▸ hv⟩
    let site := next.entries j
    have eq : Fin.ofNat (2^w) (next.entries.symm site).val = v := by
      rw [show next.entries.symm site = j from Equiv.symm_apply_apply _ _]
      exact Fin.ext (Nat.mod_eq_of_lt v.isLt)
    rw [ho,← eq,encodedPlacement_rowLength old.entries.symm next.entries.symm place hOld.le hNew.le site]
    exact hcap site
  have start : PreimagesAt p phys mid 0 := by
    refine ⟨live,fun v hv => ?_⟩
    have addr := countAt_val areas hv
    have zz : mid (countAt p v).val = 0 := by
      apply zero
      · omega
      · have hh : v.val < (p 2).val := hv
        omega
    simp [rowRepresents,preimagePrefix,zz]
  obtain ⟨rs,scan,rows,rlen,rwork⟩ := collectPreimages_run areas legal cap start old.length (by simp [ho])
  obtain ⟨_,rframe⟩ := collectPreimages_cursor_frame (k := 0) areas scan
  refine ⟨cs,rs,clear,scan,directory_of_rows old next place p areas ho hn _ (by simpa using rows),clen,rlen,cwork,?_,?_⟩
  · intro r hr
    exact ⟨(rwork r hr).2,by rw [(rwork r hr).1]⟩
  · intro j hj
    have hf := frame j (by simpa only [← hn] using hj.1)
    exact (rframe j hj).trans hf

variable {a g : ℕ} (X : State a (packingLaneBits a g))

/-- Enumerate the four hidden field types of each motif in the shrinking motif order. -/
abbrev hiddenOrder := (shrinkMotifOrder X).prod (Order.fin 4)
/-- Enumerate the six map parties of each motif in the shrinking motif order. -/
abbrev mapOrder := (shrinkMotifOrder X).prod (Order.fin 6)

/-- The enumeration of packed owners used to index the shrinking history's resident rows. -/
def packedOrder : Order ((X.Base × BitWord (Shrink.J a)) × BitWord g) :=
  ⟨ShrinkPreimages.newCount X,(Shrink.packedIndex X.baseIndex).symm.trans packedSiteEquiv⟩

theorem hidden_count (layout : Bool) (site : (X.Base × BitWord (Shrink.J a)) × BitWord g) :
    Fintype.card {e : X.packingData.Motif × Fin 4 // X.packingData.shrinkInternalOwner layout e = site} =
      4*(2^a*pieceCount (2^a) (Shrink.colors a)) :=
  X.packingData.card_shrinkInternalOwner (by have := Nat.two_pow_pos a; change 2 ≤ 2 * 2^a + 1; omega) layout site

theorem map_count (layout : Bool) (site : (X.Base × BitWord (Shrink.J a)) × BitWord g) :
    Fintype.card {e : X.packingData.Motif × Fin 6 // X.packingData.shrinkPartySite layout e.1 e.2 = site} =
      6*(2^a*pieceCount (2^a) (Shrink.colors a)) :=
  X.packingData.card_shrinkPartySite (by have := Nat.two_pow_pos a; change 2 ≤ 2 * 2^a + 1; omega) layout site

end CompressorRecords.ShrinkHistoryRows

end

end VPVNP
end Computability
end OAI
