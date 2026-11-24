import OAI.Computability.VPVNP.CompressorSlotLevel

/-!
# The physical base matching produced by a shrinking level

The first four passes construct the absolute endpoint tables. The fifth
visits each base slot at lane zero and writes its matching base slot and
its lane displacement. These are exactly the words that serve as the old
base tables of the following compression level.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotLevel

open Compression Compression.PackingData Compression.SurvivingSlots Slots SlotSchedule SlotOwners
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {V H Tag L : Type*} {d c N J nL degree w : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L] [Module (ZMod 2) Tag]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- Exact readback of both base tables under their common numeric base-arc enumeration. -/
structure BaseMatching (G : LiftedSlots (V × Tag) degree L) (target shift : ℕ) (mem : Memory w) : Prop where
  targetAt : ∀ e, (mem (target+(baseIndex vertices tags e).val)).val = (baseIndex vertices tags (G.base.target e)).val
  shiftAt : ∀ e, (mem (shift+(baseIndex vertices tags e).val)).val = (lanes (G.displacement e)).val

/-- The fifth native pass, including the range checks for both of its data-dependent reads. -/
theorem materialize (layout : Bool) (h : Heads) (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (hd : survivingDegree d c subdiv ≤ degree) (hJ : 1 < J) (hzero : (lanes 0).val = 0)
    (hw : 2 < 2^w) (hdw : degree < 2^w) (hlw : nL < 2^w) (m : Memory w) :
    let s : Shape := ⟨N,J,nL,d,c,subdiv,degree⟩
    let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad s)
    let hD := fun b ↦ (slotDirectory_degree P subdiv vertices tags lanes hc layout b).trans (Nat.add_sub_of_le hd)
    let := P.slotIdentifierOrder vertices tags subdiv
    let I := P.regularizedSlotIndexing hc hφ layout subdiv hd tags hJ
    let q := bank s h w .baseMatching
    let worker := ((template SlotBaseScan.code 0).instantiate w q).program
    stopAddress s h < 2^w → Tables D degree (rowsHead s h) (inverseHead s h) hD m →
      ∃ rs, runSegment worker 33 (some 0) m (List.replicate (baseArcs s) []) = some rs ∧
        endState (some 0) rs = some (Fin.ofNat _ (baseArcs s)) ∧
        BaseMatching vertices tags lanes I.graph (targetsHead s h) (shiftsHead s h) (after m (eventLog rs)) ∧
        (∀ a, a < targetsHead s h ∨ stopAddress s h ≤ a → after m (eventLog rs) a = m a) ∧
        RAMBuckets.cost Report.probes rs = 5*(baseArcs s) ∧ ∀ r ∈ rs, r.events.length=32 := by
  intro s D hD order I q worker hfit tab
  have hrowCap : rowsHead s h + owners s * degree ≤ inverseHead s h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right degree (Nat.le_add_right (owners s) (fields s))) _
  have hfld : inverseHead s h+fields s=targetsHead s h := rfl
  have htgt : targetsHead s h+baseArcs s=shiftsHead s h := rfl
  have hsh : shiftsHead s h+baseArcs s=stopAddress s h := rfl
  have q0 : (q 0).val = degree := Nat.mod_eq_of_lt hdw
  have q1 : (q 1).val = nL := Nat.mod_eq_of_lt hlw
  have q2 : (q 2).val = rowsHead s h := Nat.mod_eq_of_lt (by omega : rowsHead s h < 2^w)
  have q3 : (q 3).val = inverseHead s h := Nat.mod_eq_of_lt (by omega : inverseHead s h < 2^w)
  have q4 : (q 4).val = targetsHead s h := Nat.mod_eq_of_lt (by omega : targetsHead s h < 2^w)
  have q5 : (q 5).val = shiftsHead s h := Nat.mod_eq_of_lt (by omega : shiftsHead s h < 2^w)
  have step (e : (V×Tag)×Fin degree) :
      let i := Fin.ofNat (2^w) (baseIndex vertices tags e).val
      (SlotBaseScan.rowAddr q i).val < targetsHead s h ∧ (SlotBaseScan.invAddr q m i).val < targetsHead s h ∧
        SlotBaseScan.target q m i = Fin.ofNat _ (baseIndex vertices tags (I.graph.base.target e)).val ∧
        SlotBaseScan.displacement q m i = Fin.ofNat _ (lanes (I.graph.displacement e)).val := by
    intro i
    have hE : (baseIndex vertices tags e).val < baseArcs s := (baseIndex vertices tags e).isLt
    have hi : i.val = (baseIndex vertices tags e).val := Nat.mod_eq_of_lt (by omega)
    let source := laneZeroRow degree nL (baseIndex vertices tags e).val
    let field := m (rowsHead s h + source)
    have exactRead := base_lookup P subdiv vertices tags lanes hc hφ layout hd hJ hzero m e
      (by change fields s ≤ 2^w; omega) (by change owners s*degree ≤ 2^w; omega) tab
    obtain ⟨hsource, hfield, htarget⟩ := exactRead
    change source < owners s*degree at hsource
    change field.val+1 < fields s at hfield
    have rf : (q 2).val + laneZeroRow (q 0).val (q 1).val i.val < 2^w := by
      rw [q2,q0,q1,hi]; change rowsHead s h+source < 2^w; omega
    have iv : (q 3).val+((m ((q 2).val+laneZeroRow (q 0).val (q 1).val i.val)).val+1) < 2^w := by
      rw [q3,q2,q0,q1,hi]; change inverseHead s h+(field.val+1) < 2^w; omega
    have read := SlotBaseScan.read_addresses q m i hw rf iv
    have out := SlotBaseScan.outputs_eq q m i hw rf iv
    dsimp only at read out
    rw [q0,q1,q2,q3,hi] at read out
    change (SlotBaseScan.rowAddr q i).val = rowsHead s h+source ∧
      (SlotBaseScan.invAddr q m i).val = inverseHead s h+(field.val+1) at read
    rw [htarget] at out
    exact ⟨by rw [read.1]; omega, by rw [read.2]; omega, out⟩
  have outside : SlotBaseScan.ReadsOutside q m (baseArcs s) := by
    intro i hi a ha
    let e := (baseIndex vertices tags (degree := degree)).symm ⟨i,hi⟩
    have he : (baseIndex vertices tags e).val = i := congrArg Fin.val ((baseIndex vertices tags).apply_symm_apply ⟨i,hi⟩)
    obtain ⟨hr, hv, _⟩ := step e
    rw [he] at hr hv
    have ha' : a.val < targetsHead s h := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl|rfl
      · exact hr
      · exact hv
    exact ⟨Or.inl (q4 ▸ ha'), Or.inl (by rw [q5]; omega)⟩
  obtain ⟨rs, run⟩ := SlotBaseScan.run q m (baseArcs s) (by omega) (by omega) (Or.inl (by omega)) outside
  refine ⟨rs,run.executed,run.cursor,⟨?_,?_⟩,?_,run.cost,fun r hr ↦ (run.calls r hr).2⟩
  · intro e
    have hj : (baseIndex vertices tags e).val < baseArcs s := (baseIndex vertices tags e).isLt
    have he := run.first _ hj
    rw [q4,(step e).2.2.1] at he
    rw [he,Fin.val_ofNat, Nat.mod_eq_of_lt (by have ht : (baseIndex vertices tags (I.graph.base.target e)).val < baseArcs s := (baseIndex vertices tags (I.graph.base.target e)).isLt; omega)]
  · intro e
    have hj : (baseIndex vertices tags e).val < baseArcs s := (baseIndex vertices tags e).isLt
    have he := run.second _ hj
    rw [q5,(step e).2.2.2] at he
    rw [he,Fin.val_ofNat,Nat.mod_eq_of_lt ((lanes (I.graph.displacement e)).isLt.trans hlw)]
  · intro a ha
    exact run.frame a (by rw [q4]; omega) (by rw [q5]; omega)

/-- Reports of the five actual passes, in directory order. -/
structure Reports (w : ℕ) where
  /-- Reports assigning each genuine candidate field to its endpoint owner or its reserved hole
  row. -/
  genuine : List (Report w)
  /-- Reports assigning the outgoing and incoming fields of padding arcs to their packed site
  owners. -/
  dummy : List (Report w)
  /-- Reports that append each absolute field identifier to its owner's row. -/
  append : List (Report w)
  /-- Reports that invert the real endpoint rows to recover the rectangular slot of each field. -/
  scatter : List (Report w)
  /-- Reports that follow lane-zero endpoints to write the base matching and its lane
  displacements. -/
  bases : List (Report w)

/-- The five slot-directory report lists in chronological order from the first owner scan
through base matching. -/
def Reports.all (r : Reports w) := r.genuine++r.dummy++r.append++r.scatter++r.bases

/-- Memory after replaying all five slot-directory scans in sequence. -/
def Reports.final (r : Reports w) (m : Memory w) :=
  after (after (after (after (after m (eventLog r.genuine)) (eventLog r.dummy)) (eventLog r.append))
    (eventLog r.scatter)) (eventLog r.bases)

/-- The public banks and local cursor stops used by all five successive scans. -/
def Reports.Native (r : Reports w) (s : Shape) (h : Heads) (m : Memory w) : Prop :=
  let m₁ := after m (eventLog r.genuine)
  let m₂ := after m₁ (eventLog r.dummy)
  let m₃ := after m₂ (eventLog r.append)
  let m₄ := after m₃ (eventLog r.scatter)
  runSegment ((template SlotOwners.genuine 0).instantiate w (bank s h w .genuineOwners)).program 49
      (some 0) m (List.replicate (genuineCount s) []) = some r.genuine ∧
    runSegment ((template SlotOwners.dummy 0).instantiate w (bank s h w .dummyOwners)).program 20
      (some 0) m₁ (List.replicate (dummyCount s) []) = some r.dummy ∧
    runSegment ((template collectPreimage 3).instantiate w (bank s h w .appendFields)).program 23
      (some 0) m₂ (List.replicate (fields s) []) = some r.append ∧
    runSegment ((template SlotScatter.visit 0).instantiate w (bank s h w .invertFields)).program 10
      (some 0) m₃ (List.replicate (owners s*s.newDegree) []) = some r.scatter ∧
    runSegment ((template SlotBaseScan.code 0).instantiate w (bank s h w .baseMatching)).program 33
      (some 0) m₄ (List.replicate (baseArcs s) []) = some r.bases

/-- Exclusive stops are also the values returned by the last visits. -/
def Reports.Cursors (r : Reports w) (s : Shape) : Prop :=
  endState (some 0) r.genuine = some (Fin.ofNat _ (genuineCount s)) ∧
    endState (some 0) r.dummy = some (Fin.ofNat _ (dummyCount s)) ∧
    endState (some 0) r.append = some (Fin.ofNat _ (fields s)) ∧
    endState (some 0) r.scatter = some (Fin.ofNat _ (owners s*s.newDegree)) ∧
    endState (some 0) r.bases = some (Fin.ofNat _ (baseArcs s))

/-- Starting from the selected records and fresh counters, construct the
absolute endpoint arrays and the next base graph in physical RAM. No rank
oracle or sorted input rows are required. -/
theorem run_selected (layout : Bool) (h : Heads) (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (hd : survivingDegree d c subdiv ≤ degree) (hJ : 1 < J) (hlane : (lanes 0).val = 0)
    (hdeg : 0 < degree) (hdw : degree < 2^w) (mem : Memory w) :
    let s : Shape := ⟨N,J,nL,d,c,subdiv,degree⟩
    let g := bank s h w .genuineOwners
    let p := bank s h w .dummyOwners
    let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad s)
    let hD := fun b ↦ (slotDirectory_degree P subdiv vertices tags lanes hc layout b).trans (Nat.add_sub_of_le hd)
    let := P.slotIdentifierOrder vertices tags subdiv
    let I := P.regularizedSlotIndexing hc hφ layout subdiv hd tags hJ
    GenuineTables P subdiv vertices tags lanes layout g mem → DummyTables vertices tags lanes (pad s) p mem →
    h.oldArc+4*(oldBaseArcCount N J d c*nL) ≤ h.scratch → h.role+8 ≤ h.scratch →
    h.subdivisions+4 ≤ h.scratch → h.nextSite+sites s ≤ h.scratch → stopAddress s h < 2^w →
    (∀ u : Word w, u.val < owners s+fields s → mem (h.scratch+fields s+u.val)=0) →
    ∃ r : Reports w, r.Native s h mem ∧ r.Cursors s ∧
      Tables D degree (rowsHead s h) (inverseHead s h) hD (r.final mem) ∧
      BaseMatching vertices tags lanes I.graph (targetsHead s h) (shiftsHead s h) (r.final mem) ∧
      (∀ a, a < h.scratch ∨ stopAddress s h ≤ a → r.final mem a = mem a) ∧
      RAMBuckets.cost Report.probes r.all =
        6*genuineCount s+3*dummyCount s+5*fields s+3*(owners s*degree)+5*baseArcs s ∧
      ∀ rep ∈ r.all, rep.events.length ≤ 48 := by
  intro s g p D hD order I hg hp ho hrole hsub hn hfit hzero
  have input := input_of_tables (degree := degree) P subdiv vertices tags lanes layout mem h hg hp ho hrole hsub hn hfit
  have hrow : rowsHead s h+owners s*degree ≤ inverseHead s h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right degree (Nat.le_add_right (owners s) (fields s))) _
  have hfld : inverseHead s h+fields s=targetsHead s h := rfl
  have htgt : targetsHead s h+baseArcs s=shiftsHead s h := rfl
  have hsh : shiftsHead s h+baseArcs s=stopAddress s h := rfl
  have hbase : h.scratch ≤ rowsHead s h := by unfold rowsHead; omega
  obtain ⟨gs,ds,fs,ss,hgRun,hdRun,hfRun,hsRun,tab,cg,cd,cf,cs,frame,cost,wg,wd,wf,ws⟩ :=
    SlotSchedule.run D g p mem input hdeg hdw hD (by change targetsHead s h < 2^w; omega) hzero
  let m₄ := after (after (after (after mem (eventLog gs)) (eventLog ds)) (eventLog fs)) (eventLog ss)
  have ht : Tables D degree (rowsHead s h) (inverseHead s h) hD m₄ := tab
  obtain ⟨bs, hbRun, cb, matching, frameB, costB, wb⟩ := materialize P subdiv vertices tags lanes layout h hc hφ hd hJ
    hlane hp.twoFits hdw (hg.laneCount ▸ (g 0).isLt) m₄ hfit ht
  change ∀ a, a < targetsHead s h ∨ stopAddress s h ≤ a → after m₄ (eventLog bs) a = m₄ a at frameB
  let r : Reports w := ⟨gs,ds,fs,ss,bs⟩
  refine ⟨r, ⟨hgRun,hdRun,hfRun,hsRun,hbRun⟩, ⟨cg,cd,cf,cs,cb⟩, ⟨?_,?_⟩, matching, ?_, ?_, ?_⟩
  · intro e
    have he : (sortedFields D degree hD e).val < owners s*degree := (sortedFields D degree hD e).isLt
    exact (frameB _ (Or.inl (by omega))).trans (ht.bySlot e)
  · intro e
    have he : (D.address e).val < fields s := (D.address e).isLt
    exact (frameB _ (Or.inl (by omega))).trans (ht.byField e)
  · intro a ha
    have h₁ : a < h.scratch ∨ targetsHead s h ≤ a := by omega
    exact (frameB a (by omega)).trans (frame a h₁)
  · change RAMBuckets.cost Report.probes ((gs++ds++fs++ss)++bs) = _
    rw [RAMBuckets.cost_append,cost,costB]; rfl
  · intro rep hr
    change rep ∈ gs++ds++fs++ss++bs at hr
    simp only [List.mem_append] at hr
    rcases hr with (((hr|hr)|hr)|hr)|hr
    · exact (wg rep hr).le
    · rw [wd rep hr]; decide
    · rw [wf rep hr]; decide
    · rw [ws rep hr]; decide
    · rw [wb rep hr]; decide

end CompressorRecords.SlotLevel

end VPVNP
end Computability
end OAI
