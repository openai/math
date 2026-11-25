import OAI.Computability.BorderVNP.PackedBundleDirectoryStep
import OAI.Computability.BorderVNP.PackedBundleSortPhysical

/-! # Complete stable six-word bundle publication from the live marker ranks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BundleDirectory

open VPVNP.BurstRAM RoutingISA RoutingISA.CellPacket
open BottomReports CellPacketGeometry

private theorem loop_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : Layout) (g : ℕ → List BundleHeader) (m₀ : ℕ → ℕ) {width : ℕ}
    (fit : l.Fits w width) (secs : l.Sections g width m₀) (total : «prefix» g l.cells = l.bundles)
    (i : ℕ) (hi : i ≤ l.cells) (s : RoutingISA.Bank w) (m : Memory w) (h : Scan l g m₀ i (.ofWords s m)) :
    BoundedRun pub mac (.whileLt 38 31 cellStep) s m
      (16*(l.cells-i)+30*(l.bundles-«prefix» g i)+1) (Scan l g m₀ l.cells) := by
  by_cases eqn : i = l.cells
  · subst i
    simp only [total,Nat.sub_self,Nat.mul_zero,Nat.zero_add]
    exact ⟨_,s,m,.whileDone (show ¬(s 38).val < (s 31).val by
      change ¬ (NatState.ofWords s m).reg 38 < (NatState.ofWords s m).reg 31
      rw [h.cell,h.cells]; omega),le_rfl,h⟩
  · have lt : i < l.cells := by omega
    obtain ⟨a,t,mt,first,ca,ht⟩ := cell_run pub mac s m l g m₀ fit secs total lt h
    obtain ⟨b,u,mu,tail,cb,hu⟩ := loop_run pub mac l g m₀ fit secs total (i+1) lt t mt ht
    refine ⟨_,u,mu,.whileStep (show (s 38).val < (s 31).val by
      change (NatState.ofWords s m).reg 38 < (NatState.ofWords s m).reg 31
      rwa [h.cell,h.cells]) first tail,?_,hu⟩
    change 1+traceCost (a++b) ≤ _
    rw [show traceCost (a++b) = traceCost a+traceCost b from VPVNP.RAMBuckets.cost_append ..]
    have hmax := prefix_mono g (show i+1 ≤ l.cells from lt)
    rw [total,prefix_succ] at hmax
    rw [prefix_succ] at cb
    have widthWords : (cellWords g i).length = 6*(g i).length := fields_length _
    rw [widthWords] at ca
    omega
termination_by l.cells-i

/-- Running the native producer writes the entire compact table and every cell's
first/past pair in linear time in the actual number of cells and bundles. -/
theorem program_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : RoutingISA.Bank w) (m : Memory w) (l : Layout) (g : ℕ → List BundleHeader) {width : ℕ}
    (loaded : l.loaded (pub 0).val (readings m)) (fit : l.Fits w width)
    (secs : l.Sections g width (readings m)) (total : «prefix» g l.cells = l.bundles) :
    BoundedRun pub mac program s m (setup.slots+16*l.cells+30*l.bundles+1)
      (fun z => z.mem = l.image g (readings m) l.cells) := by
  have run := (setup_run pub mac s m l g loaded fit).seq (fun t mt ht =>
    loop_run pub mac l g (readings m) fit secs total 0 (Nat.zero_le _) t mt ht)
  exact run.mono (by simp [Nat.add_assoc]) (fun _ h => h.mem)

/-- A marker certificate from the geometry circuit supplies every input to the
compact writer, including strictly ordered marker addresses for empty groups. -/
theorem Layout.sections_of_sort (l : Layout) {b : ℕ} (owner : Fin l.bundles → Fin l.cells)
    (header : Fin l.bundles → BundleHeader) (rect : l.cells+6*l.bundles+l.cells ≤ 2^b)
    (m : ℕ → ℕ) (banks : l.rank = l.payload+2^b)
    (actual : BundleSort.SectionSpec rect owner header m l.payload) :
    l.Sections (groups owner header) (2^b) m := by
  have left (c : Fin l.cells) :
      l.payload+(2^b+(Markers.start rect c).val) = l.rank+c.val := by simp [Markers.start,banks,Nat.add_assoc]
  have right (c : Fin l.cells) :
      l.payload+(2^b+(Markers.stop rect c).val) = l.stopRank+c.val := by
    simp [Layout.stopRank,Markers.stop,banks,Nat.add_assoc]
  have select (c : Fin l.cells) : BundleSort.selected owner header c = cellWords (groups owner header) c.val :=
    selected_fields owner header c
  constructor
  · intro i hi
    let c : Fin l.cells := ⟨i,hi⟩
    exact ⟨left c ▸ actual.rankBound (Markers.start rect c),right c ▸ actual.rankBound (Markers.stop rect c)⟩
  · intro i hi
    let c : Fin l.cells := ⟨i,hi⟩
    have order := actual.markerOrder c
    rw [left,right] at order
    have e := (actual.cell c).1
    simp only [sectionRange,left,right,select] at e
    change l.payload+m (l.rank+c.val)+1+(cellWords (groups owner header) c.val).length =
      l.payload+m (l.stopRank+c.val)
    omega
  · intro i hi
    let c : Fin l.cells := ⟨i,hi⟩
    simpa only [sectionRange,left,select,Layout.start] using (actual.cell c).2

/-- Actual per-cell table with ordinals into the global compact row array, and the
exact original header order inside each cell, for one execution of the native code. -/
theorem publish_sort {w b : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : RoutingISA.Bank w) (m : Memory w) (l : Layout) (owner : Fin l.bundles → Fin l.cells)
    (header : Fin l.bundles → BundleHeader) (rect : l.cells+6*l.bundles+l.cells ≤ 2^b)
    (loaded : l.loaded (pub 0).val (readings m)) (fit : l.Fits w (2^b))
    (banks : l.rank = l.payload+2^b) (sort : BundleSort.SectionSpec rect owner header (readings m) l.payload) :
    let g := groups owner header
    BoundedRun pub mac program s m (setup.slots+16*l.cells+30*l.bundles+1) (fun z =>
      z.mem = l.image g (readings m) l.cells ∧ ∀ c : Fin l.cells,
        WordsAt z.mem (l.ranges+2*c.val) [«prefix» g c.val,«prefix» g (c.val+1)] ∧
        WordsAt z.mem (l.output+6*«prefix» g c.val) (BundleSort.selected owner header c)) := by
  intro g
  have total := prefix_groups owner header
  apply (program_runs pub mac s m l g loaded fit (l.sections_of_sort owner header rect _ banks sort) total).mono le_rfl
  intro z he
  refine ⟨he,fun c => ?_⟩
  rw [he,selected_fields]
  exact l.image_cell g (readings m) total fit.rangesOutput _ le_rfl c.val c.isLt

private theorem header_words_at (m : ℕ → ℕ) (base : ℕ) (hs : List BundleHeader)
    (h : WordsAt m base (hs.flatMap BundleHeader.words)) (i : Fin hs.length) :
    WordsAt m (base+6*i.val) hs[i.val].words := by
  have e : hs.take i.val ++ hs[i.val] :: hs.drop (i.val+1) = hs := by
    rw [←List.drop_eq_getElem_cons i.isLt,List.take_append_drop]
  have he := congrArg (List.flatMap BundleHeader.words) e
  simp only [List.flatMap_append,List.flatMap_cons] at he
  have a : WordsAt m base ((hs.take i.val).flatMap BundleHeader.words ++
      (hs[i.val].words ++ (hs.drop (i.val+1)).flatMap BundleHeader.words)) := he ▸ h
  have result := a.right.left
  rw [fields_length,List.length_take,Nat.min_eq_left i.isLt.le] at result
  exact result

/-- Dereferencing any reached local ordinal recovers the six scalar operands of
its unique original source. The same source equivalence enumerates every retained
bundle across all cells, including when two bundle headers have identical values. -/
theorem Layout.image_header (l : Layout) (owner : Fin l.bundles → Fin l.cells)
    (header : Fin l.bundles → BundleHeader) (m : ℕ → ℕ)
    (sep : apart l.ranges (2*l.cells) l.output (6*l.bundles))
    (c : Fin l.cells) (j : Fin (sourceRows owner c.val).length) :
    let g := groups owner header
    WordsAt (l.image g m l.cells) (l.output+6*(«prefix» g c.val+j.val))
      (header (sourceEquiv owner ⟨c,j⟩)).words := by
  intro g
  have hg := (l.image_cell g m (prefix_groups owner header) sep l.cells le_rfl c.val c.isLt).2
  let i : Fin (g c.val).length := ⟨j.val,by simp [g,groups]⟩
  have row := header_words_at _ _ (g c.val) hg i
  have value : (g c.val)[i.val] = header (sourceEquiv owner ⟨c,j⟩) := groups_get owner header c j
  simpa [value,i,Nat.mul_add,Nat.add_assoc] using row

end Packing.BundleDirectory

end BorderVNP
end Computability
end OAI
