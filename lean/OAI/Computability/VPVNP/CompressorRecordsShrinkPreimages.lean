import OAI.Computability.VPVNP.CompressorRecordsShrinkGraph
import OAI.Computability.VPVNP.CompressorSlotPhaseCosts
import OAI.Computability.VPVNP.PairTraversalDirectories

/-!
# Building the preimage directory of the chosen shrinking layout

Appendix E's third scan uses the owner column of the selected placement. The count
array starts with a native clear. The subsequent calls append each old position once,
leaving every packed site's immediate children in increasing old-site order. An
ordinal read uses the count address and the rectangular row address in the resulting
memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkPreimages

open BurstRAM Compression PrimedStackRAM
open PairSimulation.LocalHistory PairSimulation.TraversalRows
open scoped Classical

variable {a g w : ℕ} (X : State a (packingLaneBits a g))

/-- Number of old positions scanned for children, counting every packing lane at every base
vertex. -/
abbrev oldCount := Fintype.card X.Base * 2^(packingLaneBits a g)
/-- Number of packed sites receiving child rows, one for each base vertex, tag, and residual
lane. -/
abbrev newCount := Fintype.card X.Base * (2^(Shrink.J a) * 2^g)
/-- Number of old children per packed site in either layout, equal to the number of color masks
times the degree. -/
abbrev capacity (a : ℕ) := 2^(Shrink.colors a) * 2^a

theorem oldCount_eq : oldCount X = newCount X * capacity a := by
  simp only [oldCount, newCount, capacity, packingLaneBits, Shrink.colors, Shrink.J, pow_add]
  ring

/-- Enumerate old positions by base vertex, color mask, slot label, tag, and residual lane, in
the order used by the preimage scan. -/
abbrev oldOrder : Order (Shrink.Old X.Base a g) := ⟨oldCount X, (Shrink.oldIndex X.baseIndex).symm⟩
/-- Enumerate packed sites by base vertex, tag, and residual lane to index the count and child
rows. -/
abbrev newOrder : Order (Shrink.Packed X.Base a g) := ⟨newCount X, (Shrink.packedIndex X.baseIndex).symm⟩

/-- Map an old-position word to its packed owner in the chosen layout. A cursor beyond the old
positions maps to zero. -/
noncomputable abbrev place (layout : Bool) : Word w → Word w :=
  encodedPlacement (Shrink.oldIndex X.baseIndex) (Shrink.packedIndex X.baseIndex)
    (X.packingData.placement layout)

/-- The collector's old-site owner array is the first output column of the actual
shrinking scan. The remaining two arrays may occupy any later disjoint regions. -/
def params (shrink : Fin 14 → Word w) (counts rows : Word w) : Fin 6 → Word w :=
  ![Fin.ofNat _ (oldCount X), shrink 10, Fin.ofNat _ (newCount X), counts, Fin.ofNat _ (capacity a), rows]

/-- Bounds placing the count column after the old-site owner column and the rectangular child
table after the counts, all within the word address space. -/
structure Areas (shrink : Fin 14 → Word w) (counts rows : Word w) : Prop where
  ownerEnd : (shrink 10).val + oldCount X ≤ counts.val
  countEnd : counts.val + newCount X ≤ rows.val
  rowEnd : rows.val + newCount X * capacity a ≤ 2^w

variable {X} {shrink : Fin 14 → Word w} {counts rows : Word w}

/-- With contiguous fresh arrays the directory occupies one word per old child and one
count per new position. The first free address is `start + newCount X + oldCount X`. -/
theorem Areas.packed (start : ℕ) (afterOwners : (shrink 10).val + oldCount X ≤ start)
    (room : start + newCount X + oldCount X ≤ 2^w) :
    Areas X shrink (Fin.ofNat _ start) (Fin.ofNat _ (start + newCount X)) := by
  have positive : 0 < oldCount X := Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos _)
  have hc : (Fin.ofNat (2^w) start).val = start := Nat.mod_eq_of_lt (by omega)
  have hr : (Fin.ofNat (2^w) (start + newCount X)).val = start+newCount X := Nat.mod_eq_of_lt (by omega)
  exact ⟨by simpa only [hc] using afterOwners, by rw [hc, hr],
    by simpa only [hr, ← oldCount_eq X] using room⟩

theorem Areas.sizes (h : Areas X shrink counts rows) :
    oldCount X < 2^w ∧ newCount X < 2^w ∧ capacity a < 2^w := by
  have hn : 0 < newCount X := Nat.mul_pos Fintype.card_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  have hc := Nat.le_mul_of_pos_left (capacity a) hn
  have ho := h.ownerEnd
  have hv := h.countEnd
  have hr := h.rowEnd
  have := counts.isLt
  have := rows.isLt
  omega

theorem Areas.dimensions (h : Areas X shrink counts rows) :
    let p := params X shrink counts rows
    (p 0).val = oldCount X ∧ (p 2).val = newCount X ∧ (p 4).val = capacity a :=
  ⟨Nat.mod_eq_of_lt h.sizes.1, Nat.mod_eq_of_lt h.sizes.2.1, Nat.mod_eq_of_lt h.sizes.2.2⟩

theorem Areas.regions (h : Areas X shrink counts rows) : RowRegions (params X shrink counts rows) := by
  let p := params X shrink counts rows
  obtain ⟨hA, hB, hC⟩ := h.dimensions
  exact ⟨by simpa only [hA] using (show (p 1).val + oldCount X ≤ (p 3).val from h.ownerEnd),
    by simpa only [hB] using (show (p 3).val + newCount X ≤ (p 5).val from h.countEnd),
    by simpa only [hB, hC] using (show (p 5).val + newCount X*capacity a ≤ 2^w from h.rowEnd)⟩

/-- The stored owner read at a numeric cursor agrees with the typed packing placement. -/
theorem owner_at (areas : Areas X shrink counts rows) {layout : Bool} {m : Memory w}
    (column : ShrinkRAM.PlacementColumns X.slots X.baseIndex shrink layout m)
    (i : Word w) (hi : i.val < oldCount X) :
    ownerAt (params X shrink counts rows) m i = place X layout i := by
  let j : Fin (oldCount X) := ⟨i.val, hi⟩
  let x := (Shrink.oldIndex X.baseIndex).symm j
  have hnum : Shrink.oldNumber X.baseIndex x = i.val := by
    rw [← Shrink.oldIndex_val, show Shrink.oldIndex X.baseIndex x = j from Equiv.apply_symm_apply _ _]
  have hword : ShrinkRAM.word w (Shrink.oldNumber X.baseIndex x) = i := by
    rw [hnum]; exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have read := congrArg Prod.fst (column.atSite x)
  change (m (shrink 10+ShrinkRAM.word w (Shrink.oldNumber X.baseIndex x)).val).val =
    Shrink.packedNumber X.baseIndex (X.packingData.placement layout x) at read
  rw [hword] at read
  have hv : Fin.ofNat (2^w) j.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  apply Fin.ext
  change (m (shrink 10+i).val).val = (encodedPlacement _ _ _ i).val
  rw [read, ← hv, encodedPlacement_eq _ _ _ areas.sizes.1.le areas.sizes.2.1.le, Shrink.packedIndex_val]

/-- At the same cursor the numerical owner formula on the four input columns gives
the word read by the preimage collector. -/
theorem owner_formula (areas : Areas X shrink counts rows) {layout : Bool} {m : Memory w}
    (column : ShrinkRAM.PlacementColumns X.slots X.baseIndex shrink layout m)
    {color offset mate displacement : ℕ → ℕ}
    (dir : Shrink.Directory X.slots X.baseIndex color offset mate displacement) (j : Fin (oldCount X)) :
    (ownerAt (params X shrink counts rows) m (Fin.ofNat _ j.val)).val =
      (Shrink.row a (Shrink.colors a) (Shrink.J a) g layout color offset mate displacement j.val).owner := by
  rw [owner_at areas column _ (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt (j.isLt.trans areas.sizes.1)]; exact j.isLt)]
  exact (Shrink.owner_encoded X.slots X.baseIndex dir layout areas.sizes.1.le areas.sizes.2.1.le j).symm

variable (X)

/-- Enumerate the old positions assigned to a given packed site in the chosen layout, retaining
their original scan order. -/
noncomputable abbrev children (layout : Bool) (v : Shrink.Packed X.Base a g) :=
  (oldOrder X).restrict (fun u => v = X.packingData.placement layout u)

/-- Physical row counts and ordinal data words, in the restricted old-site order used
by the local history parser. -/
structure Directory (layout : Bool) (counts rows : Word w) (m : Memory w) : Prop where
  count : ∀ v : Shrink.Packed X.Base a g,
    (m (counts.val + (Shrink.packedIndex X.baseIndex v).val)).val = capacity a
  child : ∀ (v : Shrink.Packed X.Base a g) (j : Fin (children X layout v).length),
    (m (rows.val + (Shrink.packedIndex X.baseIndex v).val * capacity a + j.val)).val =
      (Shrink.oldIndex X.baseIndex ((children X layout v).entries j).val).val

open private countAt_val rowAt_val from OAI.Computability.VPVNP.CompressorRecordPreimageScan

theorem directory_of_collected (areas : Areas X shrink counts rows) (layout : Bool) (m : Memory w)
    (collected : PreimagesAt (params X shrink counts rows) (place X layout) m (oldCount X)) :
    Directory X layout counts rows m := by
  let p := params X shrink counts rows
  let o := oldOrder X
  let e := newOrder X
  obtain ⟨hA, hB, hC⟩ := areas.dimensions
  have ownerVal (v) : (siteWord w e v).val = (Shrink.packedIndex X.baseIndex v).val :=
    Nat.mod_eq_of_lt ((Shrink.packedIndex X.baseIndex v).isLt.trans areas.sizes.2.1)
  have valid (v) : siteWord w e v < p 2 := by
    change (siteWord w e v).val < (p 2).val
    rw [ownerVal, hB]; exact (Shrink.packedIndex X.baseIndex v).isLt
  have realize : RepresentsPlacement o e (X.packingData.placement layout) (place X layout (w := w)) :=
    encodedPlacement_represents o e _ areas.sizes.1.le areas.sizes.2.1.le
  constructor
  · intro v
    have h := (collected.rows (siteWord w e v) (valid v)).1
    rw [countAt_val areas.regions (valid v), ownerVal] at h
    refine h.trans ?_
    rw [show siteWord w e v = Fin.ofNat (2^w) (Shrink.packedIndex X.baseIndex v).val from rfl]
    rw [place, encodedPlacement_rowLength _ _ _ areas.sizes.1.le areas.sizes.2.1.le,
      X.packingData.card_placement (by omega)]
  · intro v j
    have h := collected.rows (siteWord w e v) (valid v)
    have ids := preimagePrefix_eq_orderedIds o e (X.packingData.placement layout) (place X layout)
      realize areas.sizes.1.le areas.sizes.2.1.le v
    change rowRepresents m (countAt p (siteWord w e v)) (rowAt p (siteWord w e v))
      (preimagePrefix (place X layout) (siteWord w e v) o.length) at h
    rw [ids] at h
    have k := h.2 ⟨j.val, by simpa only [orderedIds, List.length_ofFn] using j.isLt⟩
    rw [rowAt_val areas.regions (valid v), ownerVal, hC] at k
    simp only [orderedIds, List.getElem_ofFn] at k
    exact (congrArg Fin.val k).trans (Nat.mod_eq_of_lt
      ((Shrink.oldIndex X.baseIndex ((children X layout v).entries j).val).isLt.trans areas.sizes.1))

private theorem clear_cost (cs : List (Report w)) (h : ∀ r ∈ cs, r.probes = 1) :
    RAMBuckets.cost Report.probes cs = 2*cs.length := by
  induction cs with
  | nil => rfl
  | cons r cs ih =>
    rw [RAMBuckets.cost, h r (List.mem_cons_self ..), ih (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      List.length_cons, Nat.mul_succ]
    omega

/-- The count clear and the append pass execute from arbitrary initial scratch contents.
One clear costs two calls-plus-probes per packed position. Appending costs five per
old position. Every address outside the count and row arrays retains its initial word. -/
theorem build (areas : Areas X shrink counts rows) (layout : Bool) (mem : Memory w)
    (column : ShrinkRAM.PlacementColumns X.slots X.baseIndex shrink layout mem) :
    let p := params X shrink counts rows
    let zero := (template SliceRAM.clearOps 0).instantiate w (fun _ => counts)
    let collect := (template collectPreimage 3).instantiate w p
    ∃ cs rs, let m₁ := after mem (eventLog cs)
      let m₂ := after m₁ (eventLog rs)
      runSegment zero.program 8 (some 0) mem (List.replicate (newCount X) []) = some cs ∧
      runSegment collect.program 23 (some 0) m₁ (List.replicate (oldCount X) []) = some rs ∧
      PreimagesAt p (place X layout) m₂ (oldCount X) ∧ Directory X layout counts rows m₂ ∧
      (∀ j, OutsidePreimageWrites p j → m₂ j = mem j) ∧
      endState (some 0) cs = some (Fin.ofNat _ (newCount X)) ∧
      endState (some 0) rs = some (Fin.ofNat _ (oldCount X)) ∧
      cs.length = newCount X ∧ rs.length = oldCount X ∧
      RAMBuckets.cost Report.probes (cs++rs) = 2*newCount X + 5*oldCount X := by
  intro p zero collect
  obtain ⟨hA, hB, hC⟩ := areas.dimensions
  obtain ⟨cs, hc, z, frame, cend, clen, ccost⟩ :=
    SliceRAM.clearPass_run counts (newCount X) (areas.countEnd.trans rows.isLt.le) areas.sizes.2.1 mem
  let m₁ := after mem (eventLog cs)
  have own (i : Word w) (hi : i < p 0) : ownerAt p m₁ i = place X layout i := by
    have hi' : i.val < oldCount X := hA ▸ hi
    have ha : (shrink 10+i).val = (shrink 10).val+i.val := by
      rw [Fin.val_add, Nat.mod_eq_of_lt (by have := areas.ownerEnd; have := counts.isLt; omega)]
    change m₁ (shrink 10+i).val = _
    rw [show m₁ (shrink 10+i).val = mem (shrink 10+i).val from frame _ (.inl (by rw [ha]; have := areas.ownerEnd; omega))]
    exact owner_at areas column i hi'
  have cz (v : Word w) (hv : v < p 2) : m₁ (countAt p v).val = 0 := by
    rw [countAt_val areas.regions hv]
    have hv' : v.val < newCount X := hB ▸ hv
    exact z _ (Nat.le_add_right _ _) (Nat.add_lt_add_left hv' _)
  obtain ⟨rs, hr, done, _, cost, _, _⟩ := PhaseCosts.placementPreimages X.packingData layout
    (by omega) (Shrink.oldIndex X.baseIndex) (Shrink.packedIndex X.baseIndex)
    p areas.regions hA hB hC m₁ own cz
  obtain ⟨rend, rf⟩ := collectPreimages_cursor_frame (k := 0) areas.regions hr
  refine ⟨cs, rs, hc, hr, done, directory_of_collected X areas layout _ done, ?_, cend, by simpa using rend,
    clen, ?_, ?_⟩
  · intro j hj
    have hb : (p 2).val = newCount X := hB
    have hx : j < counts.val ∨ counts.val+(p 2).val ≤ j := hj.1
    exact (rf j hj).trans (frame j (hb ▸ hx))
  · simpa using PhaseCosts.run_length hr
  · rw [RAMBuckets.cost_append, clear_cost cs (fun r h => (ccost r h).1), clen, cost, oldCount_eq]
    ring

section Selected

open NetworkKernel MotifBlocks MotifGrid MotifConversion ShrinkMotif SurvivingSlots

variable {k R : Type*} [_root_.Field k] [CommRing R] {δ factor : ℝ} {b : ℕ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)
variable (ready : Ready (2^a) (Shrink.colors a) (2^b) δ) (s : X.ShrinkSelection B)

local notation "Y" => X.shrinkNext B ready s
/-- The term chosen by the shrink selection in the state's compression step. Its placement
determines the children used by the traversal directory. -/
noncomputable abbrev selectedTerm := (X.shrinkStatePass B κ hκ ready).step.term s
local notation "selected" => selectedTerm X B κ hκ ready s
local notation "side" => X.packingData.shrinkTermLayout B X.shrinkNumber X.packingWidth s

private theorem next_length : (siteOrder Y).length = newCount X := by
  change Fintype.card (X.Base × BitWord (Shrink.J a)) * 2^g =
    Fintype.card X.Base * (2^(Shrink.J a)*2^g)
  rw [Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv (Shrink.J a)), Fintype.card_fin, Nat.mul_assoc]

private theorem next_number (v : Shrink.Packed X.Base a g) :
    ((siteOrder Y).entries.symm (packedSiteEquiv v)).val = (Shrink.packedIndex X.baseIndex v).val := by
  change (bitWordFinEquiv g v.2.2).val + 2^g *
    ((bitWordFinEquiv (Shrink.J a) v.2.1).val + 2^(Shrink.J a) * (X.baseIndex v.1).val) = _
  rw [Shrink.packedIndex_val]
  simp only [Shrink.packedNumber, Shrink.lowNumber, Shrink.join, pow_add]
  ring

/-- The physical owner map agrees on every word with the placement of the selected
shrinking term in the actual input and output state orders. -/
theorem selected_placement :
    encodedPlacement (w := w) (siteOrder X).entries.symm (siteOrder Y).entries.symm (selected).place =
      place X side := by
  funext i
  change (if h : i.val < oldCount X then _ else 0) = (if h : i.val < oldCount X then _ else 0)
  split
  · rename_i h
    let j : Fin (oldCount X) := ⟨i.val,h⟩
    let x := (Shrink.oldIndex X.baseIndex).symm j
    change Fin.ofNat (2^w) ((siteOrder Y).entries.symm ((selected).place ((siteOrder X).entries j))).val =
      Fin.ofNat (2^w) ((Shrink.packedIndex X.baseIndex) (X.packingData.placement side x)).val
    have oldSite : (siteOrder X).entries j = packingInputSites X.Base a g x := by
      apply (siteOrder X).entries.symm.injective
      erw [Equiv.symm_apply_apply]
      change j = (Shrink.oldIndex X.baseIndex) x
      exact (Equiv.apply_symm_apply _ _).symm
    rw [oldSite]
    change Fin.ofNat (2^w) ((siteOrder Y).entries.symm
      (packedSiteEquiv (X.packingData.placement side
        ((packingInputSites X.Base a g).symm (packingInputSites X.Base a g x))))).val = _
    rw [Equiv.symm_apply_apply, next_number]
  · rfl

/-- The concrete raw directory can be passed directly to the DFS layer compiler for
this selected term. Both site orders are those used by the branch's kernel readers. -/
noncomputable def selectedDirectory (areas : Areas X shrink counts rows) (m : Memory w)
    (collected : PreimagesAt (params X shrink counts rows) (place X side) m (oldCount X))
    (limit : ℕ) (before : rows.val + newCount X * capacity a ≤ limit) :
    PairSimulation.TraversalRows.Directory selected (siteOrder X) (siteOrder Y) m limit := by
  let p := params X shrink counts rows
  obtain ⟨hA,hB,hC⟩ := areas.dimensions
  have hB' : (p 2).val = newCount X := hB
  have hC' : (p 4).val = capacity a := hC
  refine ⟨p, hA, hB.trans (next_length X B ready s).symm, areas.regions, ?_, ?_, ?_⟩
  · change rows.val+(p 2).val*(p 4).val ≤ limit
    rwa [hB', hC']
  · erw [selected_placement (w := w) X B κ hκ ready s]
    exact collected
  · intro v hv
    erw [selected_placement (w := w) X B κ hκ ready s]
    let idx : Fin (newCount X) := ⟨v.val, hB' ▸ hv⟩
    let owner := (Shrink.packedIndex X.baseIndex).symm idx
    have he : Fin.ofNat (2^w) ((Shrink.packedIndex X.baseIndex) owner).val = v := by
      rw [show Shrink.packedIndex X.baseIndex owner = idx from Equiv.apply_symm_apply _ _]
      exact Fin.ext (Nat.mod_eq_of_lt v.isLt)
    change (preimagePrefix (encodedPlacement (Shrink.oldIndex X.baseIndex) (Shrink.packedIndex X.baseIndex)
      (X.packingData.placement side)) v (oldCount X)).length ≤ (p 4).val
    rw [← he, encodedPlacement_rowLength _ _ _ areas.sizes.1.le areas.sizes.2.1.le,
      X.packingData.card_placement (by omega), hC']

end Selected

end CompressorRecords.ShrinkPreimages

end VPVNP
end Computability
end OAI
