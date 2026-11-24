import OAI.Computability.VPVNP.PairTraversalControllerReference
import OAI.Computability.VPVNP.PairTraversalControllerPersistence

/-!
# Memory preserved by every prefix of the native traversal passes

A tag call writes its own tag. A leaf call writes its two header words.
A fiber call also writes its child row, whose length is the count in the
retained raw directory. The scan leaves those input directories intact.
These bounds apply after each reference call, including inside a layer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM PrivateRAM CompressorRecords LocalHistory Compression NetworkKernel
open TraversalRows TraversalRoles DirectoryRun TraversalControllerInputs
open scoped Fin.CommRing

variable {w : ℕ}

/-- Only addresses in the half-open interval can differ after a prefix. -/
def PrefixFrame (lo hi : ℕ) (m : Memory w) (rs : List (Report w)) : Prop :=
  ∀ q ≤ rs.length, ∀ x, x < lo ∨ hi ≤ x → after m (eventLog (rs.take q)) x = m x

variable {lo hi : ℕ} {m : Memory w} {rs ss : List (Report w)}

private theorem replay_append' (m : Memory w) (rs ss : List (Report w)) :
    after m (eventLog (rs ++ ss)) = after (after m (eventLog rs)) (eventLog ss) := by
  simp only [after,eventLog,List.flatMap_append,List.foldl_append]

theorem PrefixFrame.full (h : PrefixFrame lo hi m rs) (x : ℕ) (hx : x < lo ∨ hi ≤ x) :
    after m (eventLog rs) x = m x := by simpa only [List.take_length] using h rs.length le_rfl x hx

theorem PrefixFrame.widen {a b : ℕ} (h : PrefixFrame lo hi m rs) (hl : a ≤ lo) (hh : hi ≤ b) :
    PrefixFrame a b m rs := fun q hq x hx => h q hq x (hx.imp (·.trans_le hl) (hh.trans ·))

private theorem PrefixFrame.nil (lo hi : ℕ) (m : Memory w) : PrefixFrame lo hi m [] := by
  intro q hq x hx
  simp [eventLog,after]

theorem PrefixFrame.append_at {a b : ℕ} (h : PrefixFrame lo hi m rs)
    (h' : PrefixFrame a b (after m (eventLog rs)) ss) (q : ℕ) (hq : q ≤ (rs++ss).length)
    (x : ℕ) (hx : x < lo ∨ hi ≤ x) (hx' : x < a ∨ b ≤ x) :
    after m (eventLog ((rs++ss).take q)) x = m x := by
  rw [List.take_append]
  by_cases le : q ≤ rs.length
  · simpa only [Nat.sub_eq_zero_of_le le,List.take_zero,List.append_nil] using h q le x hx
  · rw [List.take_of_length_le (by omega),replay_append']
    exact (h' (q-rs.length) (by rw [List.length_append] at hq; omega) x hx').trans
      (h.full x hx)

theorem PrefixFrame.append (h : PrefixFrame lo hi m rs)
    (h' : PrefixFrame lo hi (after m (eventLog rs)) ss) : PrefixFrame lo hi m (rs++ss) :=
  fun q hq x hx => h.append_at h' q hq x hx hx

private theorem prefixFrame_of_step (step : ∀ i : Fin rs.length,
    let before := after m (eventLog (rs.take i.val))
    (∀ x, x < lo ∨ hi ≤ x → before x = m x) →
    ∀ x, x < lo ∨ hi ≤ x → after before rs[i.val].events x = before x) : PrefixFrame lo hi m rs := by
  intro q hq
  induction q with
  | zero => exact fun _ _ => rfl
  | succ q ih =>
    let i : Fin rs.length := ⟨q,hq⟩
    have h := ih (Nat.le_of_succ_le hq)
    intro x hx
    rw [List.take_succ_eq_append_getElem hq,replay_append']
    simpa only [i,eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      (step i h x hx).trans (h x hx)

open private events from OAI.Computability.VPVNP.PairTraversalLeafWorker

/-- Prefixes of the leaf scan are confined to the leaf row interval. -/
theorem leaf_prefix (cap base count : ℕ) (m : Memory w) (rs : List (Report w))
    (run : (Pass.leaf (LeafWorker.directory w cap base) count).Run m rs)
    (fit : address cap base count < 2^w) : PrefixFrame base (address cap base count) m rs := by
  apply prefixFrame_of_step
  intro i entry _ x hx
  let n := address cap base i.val
  have bound : i.val < count := i.isLt.trans_eq run.length
  have low : base ≤ n := Nat.le_add_right _ _
  have high : n + 2 ≤ address cap base count := calc
    _ ≤ address cap base (i.val+1) := by simp only [n,address,Nat.mul_succ]; omega
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ bound) _
  have ev := LeafWorker.native cap base i.val 14 entry (by decide)
  have eq := Option.some.inj ((run.atSite i).symm.trans ev)
  rw [eq]
  have hn : (n : Word w).val = n := Nat.mod_eq_of_lt (by omega)
  have hn' : ((n : Word w)+1).val = n+1 := by
    rw [← Nat.cast_one (R := Word w),← Nat.cast_add]
    exact Nat.mod_eq_of_lt (by omega)
  change after entry (events (n : Word w)) x = _
  simp only [events,after,List.foldl_cons,List.foldl_nil,BurstRAM.update,writeMemory,hn,hn',
    ite_eq_right (by omega : x ≠ n),ite_eq_right (by omega : x ≠ n+1)]

/-- Every tag report writes within the current tag interval. -/
theorem tag_prefix (offset cap base count : ℕ) (tag : Word w) (m : Memory w) (rs : List (Report w))
    (run : (Pass.tag (Native.params offset cap base tag) count).Run m rs)
    (fit : offset + address cap base count ≤ 2^w) :
    PrefixFrame (offset+base) (offset+address cap base count) m rs := by
  apply prefixFrame_of_step
  intro i entry _ x hx
  let a := offset + address cap base i.val
  have bound : i.val < count := i.isLt.trans_eq run.length
  have low : offset+base ≤ a := Nat.add_le_add_left (Nat.le_add_right _ _) _
  have high : a < offset+address cap base count := Nat.add_lt_add_left
    (Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left bound (by omega)) _) _
  let p := Native.params offset cap base tag
  have eq := Option.some.inj ((run.atSite i).symm.trans (Native.visit_native p (i.val : Word w) entry))
  have atWord : p 0 + p 1 + p 2 * (i.val : Word w) = (a : Word w) := by
    simp only [p,Native.params,a,address,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,add_assoc]
    rfl
  rw [eq]
  change after entry (Native.events p (i.val : Word w)) x = _
  simp only [Native.events,after,List.foldl_cons,List.foldl_nil,BurstRAM.update,writeMemory,atWord,
    Fin.val_natCast,Nat.mod_eq_of_lt (high.trans_le fit),ite_eq_right (by omega : x ≠ a)]

open private row_end_le from OAI.Computability.VPVNP.PairTraversalRows
open private ready_under from OAI.Computability.VPVNP.PairTraversalDirectoryRun

/-- A fiber call only updates the two row headers and the bounded live
identifier list. The counts for every subsequent call remain readable. -/
theorem fiber_prefix (p : Fin 6 → Word w) (cap previous base : ℕ) (L : Layer)
    (raw m : Memory w) (limit : ℕ)
    (ready : (⟨fun i => countAt p (i.val : Word w),fun i => rowAt p (i.val : Word w)⟩ :
      Source w L).Ready raw limit)
    (ag : ∀ x < limit, m x = raw x) (below : limit ≤ base)
    (capacity : ∀ i, (L.ids i).length ≤ cap) (fit : endPos cap base L < 2^w)
    (rs : List (Report w)) (run : (Pass.fiber (workerData p cap previous base) cap L.count).Run m rs) :
    PrefixFrame base (endPos cap base L) m rs := by
  apply prefixFrame_of_step
  intro i entry prev x hx
  let j : Fin L.count := ⟨i.val,i.isLt.trans_eq run.length⟩
  have hr := ready_under ready (m := entry)
    (fun y hy => (prev y (Or.inl (hy.trans_le below))).trans (ag y hy)) below
  obtain ⟨es,run',image,_,_⟩ := directory_worker p L cap previous base hr.sourceBefore capacity fit
    j entry (hr.rows j)
  have eq := Option.some.inj ((run.atSite i).symm.trans run')
  rw [eq]
  change after entry es x = entry x
  rw [image]
  let n := address cap base j.val
  have lower : base ≤ n := Nat.le_add_right _ _
  have upper : n+2+(L.ids j).length ≤ endPos cap base L := by
    have h := row_end_le cap base L j
    have c := capacity j
    dsimp only [n]
    simp only [address] at h ⊢
    omega
  have hn : ((n : ℕ) : Word w).val = n := Nat.mod_eq_of_lt (by omega)
  have hn' : ((n+1 : ℕ) : Word w).val = n+1 := Nat.mod_eq_of_lt (by omega)
  change DescriptorRows.passMemory entry n _ (n+2) _ _ _ (L.ids j).length x = _
  simp only [DescriptorRows.passMemory,DescriptorRows.rowMemory,writeMemory,hn,hn',
    ite_eq_right (by omega : x ≠ n),ite_eq_right (by omega : x ≠ n+1),
    ite_eq_right (by omega : ¬ (n+2 ≤ x ∧ x < n+2+(L.ids j).length))]

/-- Every reference prefix of all tag jobs stays in their consecutive arena. -/
theorem tag_chain_prefix {offset cap base : ℕ} {ls : List TaggedLayer}
    {m : Memory w} {rs : List (Report w)} (run : RolePasses offset cap base ls m rs)
    (fit : offset+base+tagWords cap ls ≤ 2^w) :
    PrefixFrame (offset+base) (offset+base+tagWords cap ls) m rs := by
  induction run with
  | nil => exact PrefixFrame.nil _ _ _
  | @cons base l ls m rs ss one rest ih =>
    let next := endPos cap base l.layer
    have bound : offset+base+tagWords cap (l::ls) = offset+next+tagWords cap ls := by
      simp [next,endPos,address,tagWords,words,Nat.mul_add,Nat.add_assoc]
    rw [bound] at fit ⊢
    have h₁ : PrefixFrame (offset+base) (offset+next) m rs := tag_prefix offset cap base
      l.layer.count (l.role.code : Word w) m rs one ((Nat.le_add_right _ _).trans fit)
    exact (h₁.widen le_rfl (Nat.le_add_right _ _)).append ((ih fit).widen
      (Nat.add_le_add_left (Nat.le_add_right _ _) _) le_rfl)

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
variable {N Y : Network}

private theorem Segments.head_tail {job : Worker w} {jobs : List (Worker w)}
    (run : DirectoryRun.Segments (job::jobs) m rs) :
    ∃ one rest, rs = one++rest ∧ job.Run m one ∧
      DirectoryRun.Segments jobs (after m (eventLog one)) rest := by
  cases run with
  | cons hr ht => exact ⟨_,_,rfl,hr,ht⟩

/-- Native directory workers preserve all addresses outside the selected
fiber layers, even partway through the current layer. -/
theorem fiber_chain_prefix (raw : Memory w) (limit : ℕ) (c : TermChain A N Y) (r : ChainParsers κ c)
    (ords : ChainOrders c) (old : Order N.Site) (dirs : Directories raw limit c ords old)
    (ho : OrderedChildren c r ords old) (cap previous base : ℕ) (m : Memory w)
    (below : limit ≤ base) (ag : ∀ x < limit, m x = raw x)
    (hc : ∀ L ∈ stepLayers c r ords old, ∀ i, (L.ids i).length ≤ cap)
    (fit : base+words cap (stepLayers c r ords old) < 2^w)
    (rs : List (Report w)) (run : DirectoryRun.Segments (workers c ords old dirs cap previous base) m rs) :
    PrefixFrame base (base+words cap (stepLayers c r ords old)) m rs := by
  induction c generalizing previous base m rs with
  | done => cases run; exact PrefixFrame.nil _ _ _
  | more t data tail ih =>
    let L := stepLayer old ords.1 r.1
    let ls := stepLayers tail r.2 ords.2 ords.1
    let next := endPos cap base L
    have bound : base+words cap (stepLayers (.more t data tail) r ords old) = next+words cap ls := by
      simp [L,ls,next,stepLayers,endPos,address,words,Nat.mul_add,Nat.add_assoc]
    obtain ⟨one,rest,rfl,hr,ht⟩ := Segments.head_tail run
    rw [bound] at fit ⊢
    have h₁ : PrefixFrame base next m one := fiber_prefix dirs.1.pub cap previous base L raw m limit
      (dirs.1.ready r.1 ho.1) ag below (hc _ List.mem_cons_self)
      ((Nat.le_add_right _ _).trans_lt fit) one hr
    have nextge : base ≤ next := Nat.le_add_right _ _
    have h₂ := ih r.2 ords.2 ords.1 dirs.2 ho.2 base next (after m (eventLog one))
      (below.trans nextge) (fun x hx => (h₁.full x (Or.inl (hx.trans_le below))).trans (ag x hx))
      (fun l hl => hc l (List.mem_cons_of_mem L hl)) fit rest ht
    exact (h₁.widen le_rfl (Nat.le_add_right _ _)).append (h₂.widen nextge le_rfl)

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates) (f : B.Entry → A)
variable (hf : B.IsSolution f) {n : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ n)
variable (X : State (S.degreeExponent 0) n) (z : (B.execute f hf T hT X).Choices)
variable (base : ℕ) (raw : Memory w)
variable (ds : let vs := executeLevels B f hf T hT X z
  (i : Fin vs.length) → LevelDirectory vs[i] raw base)

/-- All intermediate descriptor-row memories have the same raw headers and
the same higher words as the row pass's entry memory. -/
theorem selected_rows_prefix (m : Memory w) (ag : ∀ x < base, m x = raw x)
    (rs : List (Report w)) (run : DirectoryRun.Segments (selectedJobs B f hf T hT X z base raw ds) m rs)
    (fit : base+words B.recordLimit (selectedLayers B f hf T hT X z) < 2^w) :
    PrefixFrame base (base+words B.recordLimit (selectedLayers B f hf T hT X z)) m rs := by
  let E := B.execute f hf T hT X
  let data := B.records f hf T hT X
  let c := E.termChain data z
  let ords := branchOrders E data z
  let old := siteOrder X
  let r := selectedParsers B f hf T hT X z
  let dirs := selectedDirectories B f hf T hT X z raw base ds
  let cap := B.recordLimit
  let L := leafLayer old
  let ls := stepLayers c r ords old
  let next := endPos cap base L
  have bound : base+words B.recordLimit (selectedLayers B f hf T hT X z) = next+words cap ls := by
    change base+words cap (L::ls) = _
    simp [next,endPos,address,words,Nat.mul_add,Nat.add_assoc]
  rw [bound] at fit ⊢
  change DirectoryRun.Segments (.leaf cap base old.length :: workers c ords old dirs cap base next) m rs at run
  obtain ⟨one,rest,rfl,hr,ht⟩ := Segments.head_tail run
  have h₁ : PrefixFrame base next m one :=
    leaf_prefix cap base old.length m one hr ((Nat.le_add_right _ _).trans_lt fit)
  have nextge : base ≤ next := Nat.le_add_right _ _
  have h₂ := fiber_chain_prefix raw base c r ords old dirs (selectedParsers_ordered B f hf T hT X z)
    cap base next _ nextge (fun x hx => (h₁.full x (Or.inl hx)).trans (ag x hx))
    (fun l hl => selected_capacity B f hf T hT X z l (List.mem_cons_of_mem L hl)) fit rest ht
  exact (h₁.widen le_rfl (Nat.le_add_right _ _)).append (h₂.widen nextge le_rfl)

/-- Every reference prefix preserves each address outside both arenas,
including the final arc bits in the gap between descriptor rows and tags. -/
theorem selected_reference_frame (offset : ℕ) (ts rs : List (Report w))
    (ht : RolePasses offset B.recordLimit base (selected B f hf T hT X z) raw ts)
    (hr : DirectoryRun.Segments (selectedJobs B f hf T hT X z base raw ds) (after raw (eventLog ts)) rs)
    (fit : offset+base+tagWords B.recordLimit (selected B f hf T hT X z) < 2^w) :
    let size := words B.recordLimit (selectedLayers B f hf T hT X z)
    ∀ q ≤ (ts++rs).length, ∀ x,
      (x < offset+base ∨ offset+base+size ≤ x) → (x < base ∨ base+size ≤ x) →
      after raw (eventLog ((ts++rs).take q)) x = raw x := by
  intro size q hq x htag hrow
  have eqSize : tagWords B.recordLimit (selected B f hf T hT X z) = size :=
    congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  have frameTags := tag_chain_prefix ht fit.le
  rw [eqSize] at fit frameTags
  have frameRows := selected_rows_prefix B f hf T hT X z base raw ds (after raw (eventLog ts))
    (fun x hx => frameTags.full x (Or.inl (hx.trans_le (Nat.le_add_left _ _)))) rs hr
    (show base+size < 2^w by omega)
  exact frameTags.append_at frameRows q hq x htag hrow

/-- The resident scheduler fields survive every partial scan of the actual
selected tag and row workers. The protected low interval contains the raw
level scalars and the high interval starts at the terminal header. -/
theorem selected_reference_schedule {pub : Fin 11 → Word w} {H first pitch offset : ℕ}
    (d : Resident pub raw H first pitch offset B.recordLimit base
      ⟨leafLayer (siteOrder X),.cursor⟩ (levelFibers (executeLevels B f hf T hT X z) ds))
    (headersBefore : ∀ j ≤ (executeLevels B f hf T hT X z).length, first+j*pitch+28 ≤ base)
    (ts rs : List (Report w))
    (ht : RolePasses offset B.recordLimit base (selected B f hf T hT X z) raw ts)
    (hr : DirectoryRun.Segments (selectedJobs B f hf T hT X z base raw ds) (after raw (eventLog ts)) rs)
    (belowHeader : offset+base+tagWords B.recordLimit (selected B f hf T hT X z) ≤ H) :
    ∀ q ≤ (ts++rs).length, let entry := after raw (eventLog ((ts++rs).take q))
      Schedule pub entry offset B.recordLimit base (selected B f hf T hT X z)
        (selectedJobs B f hf T hT X z base raw ds) ∧ (siteCount pub entry 0).val = X.positions := by
  have hfH : H < 2^w := by have := d.headerFits; omega
  have frame := selected_reference_frame B f hf T hT X z base raw ds offset ts rs ht hr (belowHeader.trans_lt hfH)
  have eqSize := congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  change offset+base+words B.recordLimit ((selected B f hf T hT X z).map TaggedLayer.layer) ≤ H at belowHeader
  rw [eqSize] at belowHeader
  exact selected_prefix_schedule B f hf T hT X z raw ds d headersBefore (ts++rs)
    (fun q hq x hx => frame q hq x (Or.inl (hx.trans_le (Nat.le_add_left _ _))) (Or.inl hx))
    (fun q hq j _ => frame q hq _ (Or.inr (by omega)) (Or.inr (by omega)))

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
