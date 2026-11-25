import OAI.Computability.MultitapeWeakETH.ChildScan

/-! # Correctness of the child scan in the replayed selected directory -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan

open IntegerMultiplication Code VPVNP Compression NetworkKernel CompressorRecords BurstRAM
open PairSimulation LocalHistory TraversalRows TraversalRoles DescriptorSpace
open private placementLayer from OAI.Computability.VPVNP.PairTraversalStageSize
open private valid_owner from OAI.Computability.VPVNP.PairTraversalNativeLayer
open scoped Fin.CommRing Classical
noncomputable section

variable {w : ℕ} {R : Type} [CommRing R] {N : Network} (t : Term R N) (old : Order N.Site) (next : Order t.output.Site)
  {m : Memory w} {limit : ℕ} (dir : Directory t old next m limit)

omit [CommRing R] in
private theorem directory_row (i : Fin next.length) :
    let xs := (placementLayer t old next).ids i
    rowRepresents m (countAt dir.pub (i.val : Word w)) (rowAt dir.pub (i.val : Word w))
      (xs.map (fun j : ℕ => (j : Word w))) ∧ xs.length ≤ limit ∧
      (∀ j ∈ xs, j ≤ limit ∧ j < 2^w) ∧ (rowAt dir.pub (i.val : Word w)).val+xs.length ≤ 2^w := by
  intro xs
  let π := encodedPlacement old.entries.symm next.entries.symm t.place (w:=w)
  have ho : old.length ≤ 2^w := dir.oldCount ▸ (dir.pub 0).isLt.le
  have hn : next.length ≤ 2^w := dir.newCount ▸ (dir.pub 2).isLt.le
  have hv := valid_owner dir.newCount i
  have list := preimagePrefix_eq_orderedIds old next t.place π (encodedPlacement_represents old next t.place ho hn) ho hn (next.entries i)
  simp only [siteWord,Equiv.symm_apply_apply,Fin.ofNat_eq_cast] at list
  have eq : preimagePrefix π (i.val : Word w) old.length = xs.map (fun j : ℕ => (j : Word w)) := by
    rw [list]
    simp only [xs,placementLayer,List.map_ofFn,Function.comp_def,orderedIds,siteWord,Fin.ofNat_eq_cast]
  have row := dir.collected.rows (i.val : Word w) hv
  change rowRepresents m _ _ (preimagePrefix π _ _) at row
  rw [eq] at row
  have len : xs.length = (preimagePrefix π (i.val : Word w) old.length).length := by simp [eq]
  have le : xs.length ≤ old.length := by
    rw [len]
    exact (List.length_filter_le ..).trans_eq (by simp)
  have bound : old.length ≤ limit := by
    have a := dir.regions.ownersBeforeCounts
    have b := dir.regions.countsBeforeRows
    have endPos := dir.inputEnd
    rw [dir.oldCount] at a
    omega
  have room := (preimage_input_before dir.regions dir.regions.rowsFit hv).2
  refine ⟨row,le.trans bound,?_,(Nat.add_le_add_left (len.trans_le (dir.capacity _ hv)) _).trans room⟩
  intro j hj
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hj
  exact ⟨(old.entries.symm _).isLt.le.trans bound,(old.entries.symm _).isLt.trans_le ho⟩

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
  (f : B.Entry → R) (hf : B.IsSolution f) {A : Type} (read : A × Bits.Word → Bits.Word)

/-- The three header reads and the ensuing scan return exactly the child identifiers in
the selected local parser's order. The same snapshot supplies the directories of all past passes. -/
theorem selected_children (ctx : A) (rd : ∀ h : Word w, read (ctx,wordBits h)=wordBits (m h.val))
    {initial : TaggedLayer} {L : Layout} {past : List (SelectedLevel B f hf)}
    (D : SelectedDirectoryHistory.Past B f hf initial L (endAddress L) past m)
    (i : Fin past.length) (j : Fin (levelLayer B f hf (past[i.val]'i.isLt)).count)
    (room : levelStart L i.val+26 < 2^w) :
    children read (((ctx,wordBits ((levelStart L i.val : ℕ) : Word w)),tally (endAddress L)),tally j.val) =
      ((levelLayer B f hf (past[i.val]'i.isLt)).ids j).map tally := by
  let dir := D.dirs i
  obtain ⟨r,len,ids,fit⟩ := directory_row _ _ _ dir j
  have hd := D.directory i
  have loc (offset : ℕ) (h : offset ≤ 26) :
      (((levelStart L i.val : Word w)+(offset : Word w))).val = levelStart L i.val+offset := by
    rw [← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt]; omega
  apply children_eq read ctx m rd dir.pub _ _ _ _ _ _ _ len ids fit r
  · simpa only [← Nat.cast_ofNat (R:=Word w) (n:=24)] using (loc 24 (by decide) ▸ hd.2.1)
  · simpa only [← Nat.cast_ofNat (R:=Word w) (n:=25)] using (loc 25 (by decide) ▸ hd.2.2.1)
  · simpa only [← Nat.cast_ofNat (R:=Word w) (n:=26)] using (loc 26 (by decide) ▸ hd.2.2.2)

end
end OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan
