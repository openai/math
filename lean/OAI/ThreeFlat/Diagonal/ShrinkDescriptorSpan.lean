import OAI.ThreeFlat.Diagonal.CompressorPostFrame
import OAI.ThreeFlat.Diagonal.CompressorStageWork
import OAI.ThreeFlat.Diagonal.ShrinkCursorLayout

namespace OAI
/-! # Frames and elapsed time of the chronological shrinking-stage scans -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan RAM.HeaderScan NavigationDirectory
open scoped Fin.NatCast

/-- The only mutable field of the public stage header records the elected layout. -/
def fields (K : ℕ) (c : Cursor) (x : Dimensions) (layout : Bool) (i : ℕ) : ℕ :=
  if i=27 then (if layout then 1 else 0) else (allocate K c (.shrink x)).words i

def recipeTicks (f : ℕ → ℕ) : Recipe → ℕ
  | .one row _ len => 11+f len*(2*row.work+4)
  | .seq a b => recipeTicks f a+recipeTicks f b

/-- Each leaf's two bounds come from actual numbered header fields. -/
def Within (f : ℕ → ℕ) (lo hi : ℕ) : Recipe → Prop
  | .one _ i j => i≤63 ∧ j≤63 ∧ lo≤f i ∧ f i+f j≤hi
  | .seq a b => Within f lo hi a ∧ Within f lo hi b

theorem Within.widen {f : ℕ → ℕ} {lo hi lo' hi' : ℕ} (p : Recipe)
    (inner : Within f lo hi p) (left : lo'≤lo) (right : hi≤hi') : Within f lo' hi' p := by
  induction p with
  | one row i j => exact ⟨inner.1,inner.2.1,left.trans inner.2.2.1,inner.2.2.2.trans right⟩
  | seq a b ia ib => exact ⟨ia inner.1,ib inner.2⟩

variable {w : ℕ}

structure RunResult (p : Recipe) (cur : Word w) (pub : Fin 1 → Word w) (m : Memory w)
    (head : ℕ) (f : ℕ → ℕ) (lo hi : ℕ) : Prop where
  fits : (p.install cur).fits cur pub m
  bounded : (p.install cur).bounded cur pub m (hi-lo)
  clocks : ((p.install cur).execute cur pub m).1=recipeTicks f p
  avoids : ∀ a b,b≤lo → (p.install cur).Avoids cur pub m a b
  frame : agreesOutside lo hi ((p.install cur).execute cur pub m).2 m
  header : Scans.Header cur ((p.install cur).execute cur pub m).2 head 63 f

theorem run (p : Recipe) (cur : Word w) (pub : Fin 1 → Word w) (m : Memory w) {head lo hi : ℕ}
    {f : ℕ → ℕ} (h : Scans.Header cur m head 63 f) (earlier : head+64≤lo) (later : hi≤cur.val)
    (within : Within f lo hi p) : RunResult p cur pub m head f lo hi := by
  induction p generalizing m with
  | one row i j =>
    obtain ⟨si,sj,low,high⟩ := within
    have start : (headerRead m cur i).val=f i := h.get i si
    have len : (headerRead m cur j).val=f j := h.get j sj
    have fits : (headerRead m cur i).val+(headerRead m cur j).val<2^w := by
      rw [start,len]; exact (high.trans later).trans_lt cur.isLt
    have frame : agreesOutside lo hi (((Recipe.one row i j).install cur).execute cur pub m).2 m := by
      intro a side
      apply sweep_frame _ _ _ _ fits
      rw [start,len]
      exact side.imp (fun h=>h.trans_le low) (fun h=>high.trans h)
    refine ⟨fits,?_,?_,?_,frame,?_⟩
    · change (headerRead m cur j).val≤hi-lo
      rw [len]; omega
    · change 11+(headerRead m cur j).val*(2*(Template.emit cur row).binds+4)=11+f j*(2*row.work+4)
      rw [len,Template.emit_work]
    · intro a b hb
      exact ⟨fits,.inr (by rw [start]; exact hb.trans low)⟩
    · refine ⟨?_,h.fit,?_⟩
      · rw [frame _ (.inr later)]; exact h.pointer
      · intro i si
        rw [frame _ (.inl (by omega))]; exact h.values i si
  | seq a b ia ib =>
    have left:=ia m h within.1
    have right:=ib ((a.install cur).execute cur pub m).2 left.header within.2
    exact ⟨⟨left.fits,right.fits⟩,⟨left.bounded,right.bounded⟩,congrArg₂ (·+·) left.clocks right.clocks,
      fun i j hj=>⟨left.avoids i j hj,right.avoids i j hj⟩,fun i out=>(right.frame i out).trans (left.frame i out),
      right.header⟩

variable (S : Graph.Stage) (K : ℕ) (c : Cursor) (x : Dimensions) (layout : Bool)
set_option quotPrecheck false
local notation "p" => Resident.pointers K c x
local notation "tail" => (allocate K c (.shrink x)).next.heap
local notation "extra" => ((p).costs+2*(x.motifs+1))

private theorem boundaries :
    c.heap≤(p).demands ∧ (p).demands≤(p).newGraph ∧ (p).newGraph≤(p).costs ∧ extra≤tail := by
  simp [Resident.pointers,allocate,headerWord,extraEnd,headerExtra]; omega

private theorem before_within (tagBits : ℕ) : Within (fields K c x layout) (p).demands (p).newGraph (before S tagBits) := by
  simp [Within,before,fields,Resident.pointers,allocate,headerWord,splitShifts,splitWords,
    colors,offsets,oldBases,demand,demandWords]; omega

private theorem graph_within : Within (fields K c x layout) (p).newGraph (p).costs (afterRecipe S) := by
  simp [Within,afterRecipe,fields,Resident.pointers,allocate,headerWord,nextGraph,graphWords,
    keys,nextSlots,nextWidths,widthWords]; omega

private theorem descriptors_within (kind : ℕ) :
    Within (fields K c x layout) extra tail (NodeRecipe.descriptors S K kind) := by
  simp [Within,NodeRecipe.descriptors,NodeRecipe.localTables,NodeRecipe.ownership,
    NodeRecipe.kernelBase,NodeRecipe.incidentBase,NodeRecipe.halfBase,NodeRecipe.rowsBase,
    NodeRecipe.childrenBase,NodeRecipe.ownerBase,fields,Resident.pointers,allocate,headerWord,
    extraEnd,headerExtra]; omega


/-- The header-relative scan lengths bound the fixed native recipe even before a memory is supplied. -/
theorem Within.ticks {g : ℕ→ℕ} {lo hi : ℕ} {r : Recipe} (hw : Within g lo hi r) :
    recipeTicks g r≤(hi-lo+1)*r.cost := by
  induction r with
  | one row i j =>
    change 11+g j*(2*row.work+4)≤(hi-lo+1)*(15+2*row.work)
    obtain ⟨low,high⟩ := hw.2.2
    have span : g j≤hi-lo := by omega
    have rows := Nat.mul_le_mul_right (2*row.work+4) span
    nlinarith only [rows,Nat.zero_le (hi-lo),Nat.zero_le row.work]
  | seq a b ia ib =>
    simpa only [recipeTicks,Recipe.cost,Nat.mul_add] using Nat.add_le_add (ia hw.1) (ib hw.2)

theorem recipe_charge (bits kind : ℕ) :
    recipeTicks (fields K c x false) (before S bits)+
      max (recipeTicks (fields K c x false) (NodeRecipe.after S K kind))
          (recipeTicks (fields K c x true) (NodeRecipe.after S K kind)) ≤
      ((NavigationDirectory.Stage.shrink x).heapWords+1)*((before S bits).cost+(NodeRecipe.after S K kind).cost) := by
  obtain ⟨a,b,d,e⟩:=boundaries K c x
  have stop : c.heap+(NavigationDirectory.Stage.shrink x).heapWords=tail :=
    (NavigationDirectory.heap_step K c (.shrink x)).symm
  have full (lay) : Within (fields K c x lay) c.heap tail (NodeRecipe.after S K kind) :=
    ⟨Within.widen _ (graph_within S K c x lay) (by omega) (by omega),
      Within.widen _ (descriptors_within S K c x lay kind) (by omega) le_rfl⟩
  have pre : Within (fields K c x false) c.heap tail (before S bits) :=
    Within.widen _ (before_within S K c x false bits) a (by omega)
  have span : tail-c.heap=(NavigationDirectory.Stage.shrink x).heapWords := by omega
  rw [←span,Nat.mul_add]
  exact Nat.add_le_add pre.ticks (max_le (full false).ticks (full true).ticks)

variable (cur : Word w) (pub : Fin 1 → Word w) (m : Memory w)
variable (h : Scans.Header cur m c.header 63 (fields K c x layout)) (earlier : c.header+64≤c.heap)
    (later : (allocate K c (.shrink x)).next.heap≤cur.val)

include h earlier later in
theorem pre_run (tagBits : ℕ) :
    RunResult (before S tagBits) cur pub m c.header (fields K c x layout) (p).demands (p).newGraph := by
  obtain ⟨a,b,d,e⟩:=boundaries K c x
  exact run _ _ _ _ h (earlier.trans a) (by omega) (before_within S K c x layout tagBits)

include h earlier later in
theorem post_run :
    RunResult (afterRecipe S) cur pub m c.header (fields K c x layout) (p).newGraph (p).costs := by
  obtain ⟨a,b,d,e⟩:=boundaries K c x
  exact run _ _ _ _ h ((earlier.trans a).trans b) (by omega) (graph_within S K c x layout)

include h earlier later in
theorem descriptor_run (kind : ℕ) :
    RunResult (NodeRecipe.descriptors S K kind) cur pub m c.header (fields K c x layout) extra tail := by
  obtain ⟨a,b,d,e⟩:=boundaries K c x
  exact run _ _ _ _ h (by omega) later (descriptors_within S K c x layout kind)

include h earlier later in
theorem after_run (kind : ℕ) :
    RunResult (NodeRecipe.after S K kind) cur pub m c.header (fields K c x layout) (p).newGraph tail := by
  obtain ⟨a,b,d,e⟩:=boundaries K c x
  apply run _ _ _ _ h ((earlier.trans a).trans b) later
  exact ⟨Within.widen _ (graph_within S K c x layout) le_rfl (by omega),
    Within.widen _ (descriptors_within S K c x layout kind) (by omega) le_rfl⟩

include h earlier later in
theorem descriptor_avoids_graph_width (kind : ℕ) :
    let graph:=(afterRecipe S).install cur
    let «meta»:=(NodeRecipe.descriptors S K kind).install cur
    let mid:=(graph.execute cur pub m).2
    «meta».Avoids cur pub mid (p).newGraph ((p).newGraph+6*x.newEdges) ∧
      «meta».Avoids cur pub mid (p).newWidths ((p).newWidths+x.newEdges*x.residual) := by
  have graph:=post_run S K c x layout cur pub m h earlier later
  have «meta»:=descriptor_run S K c x layout cur pub _ graph.header earlier later kind
  have graphEnd : (p).newGraph+6*x.newEdges≤extra := by
    simp [Resident.pointers,allocate,headerWord]; omega
  have widthEnd : (p).newWidths+x.newEdges*x.residual≤extra := by
    simp [Resident.pointers,allocate,headerWord]
  exact ⟨«meta».avoids _ _ graphEnd,«meta».avoids _ _ widthEnd⟩

theorem fields_false : fields K c x false=(allocate K c (.shrink x)).words := by
  funext i
  by_cases eqv : i=27
  · subst i; rfl
  · simp [fields,eqv]

theorem elected_header {raw : Memory w}
    (original : Scans.Header cur raw c.header 63 (allocate K c (.shrink x)).words)
    (chosen : Resident.Header x p layout cur m)
    (high : ∀ i,34≤ i → i≤63 → m (c.header+i)=raw (c.header+i)) :
    Scans.Header cur m c.header 63 (fields K c x layout) := by
  refine ⟨chosen.pointer,original.fit,?_⟩
  intro i hi
  by_cases lt : i<34
  · let j : Fin 34 := ⟨i,lt⟩
    have read := congrArg Fin.val (chosen.words j)
    have ef : Resident.value x p layout i=(fields K c x layout) i := by
      by_cases eqv : i=27
      · simp [Resident.value,fields,selected,eqv]
      · simpa [Resident.value,fields,selected,eqv] using (Resident.fields K c x j).symm
    have fits : (fields K c x layout) i<2^w := by
      by_cases eqv : i=27
      · have wide : 1 < 2^w := by have hfit := original.fit; omega
        subst i
        cases layout
        · exact Nat.zero_lt_of_lt wide
        · exact wide
      · rw [fields,ite_eq_right eqv,←original.values i hi]; exact (raw _).isLt
    change (m (c.header+i)).val=((Resident.value x p layout i:ℕ):Word w).val at read
    rwa [ef,Fin.val_cast_of_lt fits] at read
  · rw [high i (by omega) hi,original.values i hi,fields,ite_eq_right (by omega)]

theorem RunResult.clock_bound {r : Recipe} {head lo hi : ℕ} {field : ℕ → ℕ}
    (ok : RunResult r cur pub m head field lo hi) :
    ((r.install cur).execute cur pub m).1≤(hi-lo+1)*r.cost :=
  r.time_le cur pub m (hi-lo) ok.bounded



end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan

end OAI
