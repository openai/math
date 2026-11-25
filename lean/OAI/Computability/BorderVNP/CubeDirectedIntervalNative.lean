import OAI.Computability.BorderVNP.CubeLabelNative
import OAI.Computability.BorderVNP.CubeDirectedIntervalTables
import OAI.Computability.BorderVNP.CubeDirectedIntervalPrepare

/-! # From the native label chooser to the physical directed cable intervals

The input is the original RAM frame and the two sparse geometry arrays. The label pass
preserves these arrays. Its output labels and the preserved geometry jointly describe
the rows needed by the directed interval scan.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.NativeIntervals

open Physical Crossing MeanChoice RoutingISA VPVNP.BurstRAM

private theorem cable_unchanged {t : LabelIndex.Layout} {before after : ℕ → ℕ} {lab : ℕ}
    (keep : ∀ a < lab, after a = before a) (low : t.cables + t.cableCount * 3 ≤ lab)
    {i : ℕ} (hi : i < t.cableCount) :
    LabelIndex.cableAt t after i = LabelIndex.cableAt t before i := by
  dsimp only [LabelIndex.cableAt]
  rw [keep _ (by omega), keep _ (by omega), keep _ (by omega)]

private theorem delivery_unchanged {t : LabelIndex.Layout} {before after : ℕ → ℕ} {lab : ℕ}
    (keep : ∀ a < lab, after a = before a) (low : t.deliveries + t.deliveryCount * 7 ≤ lab)
    {i : ℕ} (hi : i < t.deliveryCount) :
    LabelIndex.deliveryAt t after i = LabelIndex.deliveryAt t before i := by
  dsimp only [LabelIndex.deliveryAt]
  rw [keep _ (by omega), keep _ (by omega)]

private theorem traffic_unchanged (t : LabelIndex.Layout) (before after : ℕ → ℕ)
    (ep : LabelIndex.Endpoints t before) (ep' : LabelIndex.Endpoints t after)
    (hc : ∀ i : Fin t.cableCount, LabelIndex.cableAt t after i = LabelIndex.cableAt t before i)
    (hd : ∀ i : Fin t.deliveryCount, LabelIndex.deliveryAt t after i = LabelIndex.deliveryAt t before i) :
    LabelIndex.fromTables t after ep' = LabelIndex.fromTables t before ep := by
  funext r
  cases r with
  | inl i =>
    dsimp only [LabelIndex.fromTables, LabelIndex.Cable.traffic]
    congr 1
    · exact Fin.ext (congrArg LabelIndex.Cable.src (hc i))
    · exact Fin.ext (congrArg LabelIndex.Cable.dst (hc i))
    · exact congrArg LabelIndex.liveWidth (hc i)
  | inr i =>
    dsimp only [LabelIndex.fromTables]
    congr 1
    · exact Fin.ext (congrArg Prod.fst (hd i))
    · exact congrArg Prod.snd (hd i)

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {C : Type} [Fintype C] [DecidableEq C]
variable {A : Type*} [Fintype A]

/-- Execute the actual label program. Its output codes describe the physical intervals on
the post-run memory, where the sparse cable and delivery columns retain their input values. -/
theorem native_chooser_rows (N : Network D P bits) (cell : N.Site → C) (recv : A → C)
    (dataWidth : A → ℕ) {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (n d : ℕ) (hd : 0 < d) (s : Bank w) (m : Memory w) :
    let before := readings m
    let base := (pub 0).val
    let t := LabelIndex.layout base before
    let lab := before (base+48)
    let l := chooserLayout t base lab (before (base+57)) (before (base+58))
    ∀ (ep : LabelIndex.Endpoints t before) (cells : C ≃ Fin t.cells)
      (edges : N.CrossingEdge cell ↪ Fin t.cableCount) (data : A ↪ Fin t.deliveryCount)
      (hz : d^(n+1) = t.labels),
      RowPlacement (networkRows N cell recv dataWidth) (LabelIndex.fromTables t before ep)
        cells (edges.sumMap data) →
      LabelIndex.Allocated t → t.cables+t.cableCount*3 ≤ lab → t.deliveries+t.deliveryCount*7 ≤ lab →
      lab+t.cells ≤ t.heads → base+56 < t.heads → t.dataMean+t.labels ≤ 2^w →
      LabelIndex.wordEnvelope t.labels (LabelIndex.inputWidth t before) < 2^w →
      ∃ tr out mt, Runs pub macros LabelIndex.directoryProgram s m tr out mt ∧
        traceCost tr ≤ LabelIndex.directoryTicks t (d^(n+1)-1) before ∧
        (∀ a < lab, mt a = m a) ∧
        (∀ c : Fin t.cells, (mt (lab+c.val)).val = (tableCodes t before ep (d^(n+1)-1) c).val) ∧
        ∃ (ord : N.CrossingEdge cell ≃ Fin (Fintype.card (N.CrossingEdge cell)))
          (row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin l.count),
          (∀ e, row (ord e) = edges e) ∧ PhysicalRows N cell l (readings mt) ord row
            (cells.toEmbedding.trans Fin.valEmbedding)
            (meanPackedLabel N cell recv dataWidth ((List.finRange t.cells).map cells.symm) n d hd)
            (productCode n d t.labels hz) := by
  intro before base t lab l ep cells edges data hz place al cab dat sep frame addresses cap
  let z := d^(n+1)-1
  have positive := pow_pos hd (n+1)
  have alphabet : t.labels = z+1 := by dsimp [z]; omega
  obtain ⟨tr,out,mt,run,cost,_,codes,off⟩ :=
    LabelIndex.native_table_codes pub macros z s m ep al alphabet sep frame addresses cap
  have keep (a : ℕ) (ha : a < lab) : readings mt a = before a := congrArg Fin.val (off a ha)
  have hc {i : ℕ} (hi : i < t.cableCount) := cable_unchanged keep cab hi
  have hd' {i : ℕ} (hi : i < t.deliveryCount) := delivery_unchanged keep dat hi
  have post : LabelIndex.Endpoints t (readings mt) :=
    ⟨fun i hi => hc hi ▸ ep.cables i hi, fun i hi => hd' hi ▸ ep.deliveries i hi⟩
  have same := traffic_unchanged t before (readings mt) ep post
    (fun i => hc i.isLt) (fun i => hd' i.isLt)
  have placed : RowPlacement (networkRows N cell recv dataWidth) (LabelIndex.fromTables t (readings mt) post)
      cells (edges.sumMap data) := same ▸ place
  have codes' (c : C) : readings mt (lab+(cells c).val) =
      (tableCodes t (readings mt) post z (cells c)).val := by
    unfold tableCodes
    rw [same]
    exact codes (cells c)
  exact ⟨tr,out,mt,run,cost,off,codes,physicalRows_of_chooser N cell recv dataWidth t
    (readings mt) post cells edges data hd hz placed base lab (before (base+57)) (before (base+58)) codes'⟩


/-- Address and width bounds for the interval pass follow from the incoming cable endpoints,
the assigned label range, and the public ordering of the scratch intervals. -/
theorem chooser_interval_fits (t : LabelIndex.Layout) (before after : ℕ → ℕ)
    (base lab widths ordinals w : ℕ) (ep : LabelIndex.Endpoints t before)
    (keep : ∀ a < lab, after a = before a)
    (codes : ∀ i : Fin t.cells, after (lab+i.val) < t.labels) (positive : 0 < t.labels)
    (cab : t.cables + t.cableCount*3 ≤ lab) (frame : base+58 < lab)
    (lo : lab+t.cells ≤ widths) (sep : widths+t.labels^2 ≤ ordinals)
    (space : ordinals+t.cableCount ≤ 2^w)
    (cap : LabelIndex.wordEnvelope t.labels (LabelIndex.inputWidth t before) < 2^w) :
    (chooserLayout t base lab widths ordinals).Fits w after := by
  let l := chooserLayout t base lab widths ordinals
  have sq := (LabelIndex.wordCaps t before ep w cap).1
  have cols (i : ℕ) (hi : i < t.cableCount) :
      l.src after i = (LabelIndex.cableAt t before i).src ∧
      l.dst after i = (LabelIndex.cableAt t before i).dst ∧
      l.width after i = (LabelIndex.cableAt t before i).width := by
    have c := cable_unchanged keep cab hi
    simpa only [l,chooserLayout,Layout.src,Layout.dst,Layout.width,LabelIndex.cableAt,Nat.mul_comm 3]
      using And.intro (congrArg LabelIndex.Cable.src c)
        (And.intro (congrArg LabelIndex.Cable.dst c) (congrArg LabelIndex.Cable.width c))
  have names (i : ℕ) (hi : i < t.cableCount) :
      l.src after i < t.cells ∧ l.dst after i < t.cells := by
    rw [(cols i hi).1, (cols i hi).2.1]
    exact ep.cables i hi
  change l.Fits w after
  refine ⟨?_,?_,?_,?_,?_,?_,space,?_,?_,?_⟩
  · change base+58 < 2^w; omega
  · change t.cableCount < 2^w; omega
  · change t.labels^2 < 2^w; omega
  · change t.cables+3*t.cableCount ≤ 2^w; omega
  · intro i hi c hc
    change lab+c < 2^w ∧ after (lab+c) < t.labels
    have hn := names i hi
    have hc' : c < t.cells := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hc; omega
    exact ⟨by omega,codes ⟨c,hc'⟩⟩
  · change widths+t.labels^2 ≤ 2^w; omega
  · intro k hk i hi
    change k < t.labels^2 at hk
    change widths+k ≠ ordinals+i; omega
  · intro i hi a ha
    change i < t.cableCount at hi
    have hn := names i hi
    change a ∈ [t.cables+3*i,t.cables+3*i+1,t.cables+3*i+2,lab+l.src after i,lab+l.dst after i] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    change ¬(widths ≤ a ∧ a < widths+t.labels^2) ∧ ¬(ordinals ≤ a ∧ a < ordinals+t.cableCount)
    omega
  · intro i hi k
    have scaled := (LabelIndex.wordCaps t before ep w cap).2.1
    have cableWidth := (Nat.le_mul_of_pos_right _ (pow_pos positive 2)).trans_lt scaled
    let f (j : ℕ) := if l.src after j ≠ l.dst after j ∧ l.key after j = k then l.width after j else 0
    have le := LabelIndex.sumWidth_le (f := f) (g := LabelIndex.Cable.width ∘ LabelIndex.cableAt t before)
      hi (fun j hj => by dsimp [f]; split <;> simp [(cols j hj).2.2])
    apply lt_of_le_of_lt _ (le.trans_lt cableWidth)
    rw [LabelIndex.sumWidth_eq_fin,Fin.sum_univ_eq_sum_range]
    rfl


/-- Execute the chooser and the interval scan consecutively on the original RAM input.
Every final directed width and every positive-width cable's start is the corresponding
physical load or prefix. The final memory still supplies the physical endpoint and
product-label columns, so the same numbering can be used by the host's scatter pass. -/
theorem native_chooser_intervals (N : Network D P bits) (cell : N.Site → C) (recv : A → C)
    (dataWidth : A → ℕ) {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (n d : ℕ) (hd : 0 < d) (s : Bank w) (m : Memory w) :
    let before := readings m
    let base := (pub 0).val
    let t := LabelIndex.layout base before
    let lab := before (base+48)
    let l := chooserLayout t base lab (before (base+57)) (before (base+58))
    ∀ (ep : LabelIndex.Endpoints t before) (cells : C ≃ Fin t.cells)
      (edges : N.CrossingEdge cell ↪ Fin t.cableCount) (data : A ↪ Fin t.deliveryCount)
      (hz : d^(n+1) = t.labels),
      RowPlacement (networkRows N cell recv dataWidth) (LabelIndex.fromTables t before ep)
        cells (edges.sumMap data) →
      LabelIndex.Allocated t → t.cables+t.cableCount*3 ≤ lab → t.deliveries+t.deliveryCount*7 ≤ lab →
      lab+t.cells ≤ t.heads → base+58 < lab → t.dataMean+t.labels ≤ 2^w →
      LabelIndex.wordEnvelope t.labels (LabelIndex.inputWidth t before) < 2^w →
      lab+t.cells ≤ l.widths → l.widths+t.labels^2 ≤ l.ordinals → l.ordinals+t.cableCount ≤ 2^w →
      let label := meanPackedLabel N cell recv dataWidth ((List.finRange t.cells).map cells.symm) n d hd
      let enc := productCode n d t.labels hz
      ∃ tr out mf, Runs pub macros (.seq LabelIndex.directoryProgram prepare) s m tr out mf ∧
        traceCost tr ≤ LabelIndex.directoryTicks t (d^(n+1)-1) before +
          (setup.slots + (4*t.labels^2+2) + (2+t.cableCount*(cableStep.slots+1))) ∧
        (∀ a < lab, readings mf a = before a) ∧
        ∃ (ord : N.CrossingEdge cell ≃ Fin (Fintype.card (N.CrossingEdge cell)))
          (row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin l.count),
          (∀ e, row (ord e) = edges e) ∧ PhysicalRows N cell l (readings mf) ord row
            (cells.toEmbedding.trans Fin.valEmbedding) label enc ∧
          (∀ u, readings mf (l.widths+pairCode enc u) =
            load (cablePair ord (crossSrc N cell) (crossDst N cell) label) (crossWidth N cell ∘ ord.symm) u) ∧
          ∀ e, 0 < crossWidth N cell e → readings mf (l.ordinals+(edges e).val) =
            intervalStart (cablePair ord (crossSrc N cell) (crossDst N cell) label)
              (crossWidth N cell ∘ ord.symm) (ord e) := by
  intro before base t lab l ep cells edges data hz place al cab dat labels frame addresses cap lo sep space label enc
  have frame' : base+56 < t.heads := by omega
  obtain ⟨tr,out,mt,run,cost,off,codes,ord,row,aligned,physical⟩ :=
    native_chooser_rows N cell recv dataWidth pub macros n d hd s m ep cells edges data hz
      place al cab dat labels frame' addresses cap
  have keep (a : ℕ) (ha : a < lab) : readings mt a = before a := congrArg Fin.val (off a ha)
  have positive : 0 < t.labels := hz ▸ pow_pos hd (n+1)
  have bounds (i : Fin t.cells) : readings mt (lab+i.val) < t.labels := by
    change (mt (lab+i.val)).val < t.labels
    rw [codes i]
    exact (tableCodes t before ep (d^(n+1)-1) i).isLt.trans_le (by omega)
  have fit := chooser_interval_fits t before (readings mt) base lab l.widths l.ordinals w
    ep keep bounds positive cab frame lo sep space cap
  have field (j : ℕ) (hj : j ≤ 58) := keep (base+j) (by omega)
  have fields : l.Fields (readings mt) :=
    ⟨field 6 (by decide),field 7 (by decide),field 48 (by decide),field 56 (by decide),
      field 57 (by decide),field 58 le_rfl⟩
  obtain ⟨fs,u,mf,run',cost',_,img⟩ := run_prepare pub macros l out mt fit rfl fields
  have image : l.Image (readings mt) l.count (readings mf) := img
  have retain (a : ℕ) (ha : a < lab+t.cells) : readings mf a = readings mt a :=
    image.outside _ (by omega) (by omega)
  have cols (i : Fin l.count) : l.src (readings mf) i = l.src (readings mt) i ∧
      l.dst (readings mf) i = l.dst (readings mt) i ∧ l.width (readings mf) i = l.width (readings mt) i := by
    have hi : i.val < t.cableCount := i.isLt
    exact ⟨retain _ (show t.cables+3*i.val < lab+t.cells by omega),
      retain _ (show t.cables+3*i.val+1 < lab+t.cells by omega),
      retain _ (show t.cables+3*i.val+2 < lab+t.cells by omega)⟩
  have finalRows : PhysicalRows N cell l (readings mf) ord row (cells.toEmbedding.trans Fin.valEmbedding)
      label enc := by
    constructor
    · intro i
      rw [(cols (row i)).1,(cols (row i)).2.1,(cols (row i)).2.2]
      exact physical.cable i
    · intro c
      exact (retain _ (Nat.add_lt_add_left (cells c).isLt lab)).trans (physical.labels c)
    · intro i hi
      rw [(cols i).1,(cols i).2.1,(cols i).2.2]
      exact physical.holes i hi
  refine ⟨tr++fs,u,mf,run.seq run', (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add cost cost'),
    fun a ha => (retain a (by omega)).trans (keep a ha),ord,row,aligned,finalRows,
    physical.image_load image,?_⟩
  intro e he
  have width : 0 < crossWidth N cell (ord.symm (ord e)) := by rwa [ord.symm_apply_apply]
  rw [← aligned e]
  exact physical.image_intervalStart image (ord e) width

end Cube.NativeIntervals

end BorderVNP
end Computability
end OAI
