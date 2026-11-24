import OAI.Computability.VPVNP.ShrinkingSlots
import OAI.Computability.VPVNP.CompressorSlotRankRAM
import OAI.Computability.VPVNP.ExpanderSlots
import OAI.Computability.VPVNP.DegreeRefreshTopology

/-!
# Recording the two slot numbers of each surviving arc

In the third scan of Appendix E, each new position receives two lists of
actual arc identifiers, one for each orientation. Translating the original
CD source to lane zero gives the integer key used by the packed graph.
Each key occurs once per incidence list. Counting smaller keys in that list
therefore computes the same slot number as sorting. The two ranks occupy
separate fields at a common absolute arc address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Slots

open Compression Compression.SurvivingSlots Compression.PackingData BurstRAM

/-- The list at one endpoint after the arc-generation scan, in visitation order. -/
structure IncidentRow {E S : Type*} (endpoint : E → S) (s : S) where
  /-- The duplicate-free list of all arc identifiers incident at the row's specified endpoint. -/
  ids : List E
  nodup : ids.Nodup
  complete : ∀ a, a ∈ ids ↔ endpoint a = s

/-- One pass over all generated actual identifiers, appending each to the row
at its endpoint. Incoming and outgoing arrays use the same code with different
endpoint functions. -/
def collectRows {E S : Type*} [DecidableEq S] (atSite : E → S)
    (stream : List E) (rows : S → List E) : S → List E :=
  stream.foldl (fun rs i ↦ Function.update rs (atSite i) (rs (atSite i) ++ [i])) rows

/-- Each local array contains exactly its incident identifiers in scan order. -/
theorem collectRows_eq {E S : Type*} [DecidableEq S] (atSite : E → S) (stream : List E)
    (rows : S → List E) (s : S) :
    collectRows atSite stream rows s = rows s ++ stream.filter (fun i ↦ decide (atSite i = s)) := by
  induction stream generalizing rows with
  | nil => simp [collectRows]
  | cons i xs ih =>
    change collectRows atSite xs (Function.update rows (atSite i) (rows (atSite i) ++ [i])) s = _
    rw [ih]
    by_cases h : atSite i = s
    · simp [h, Function.update, List.append_assoc]
    · simp [h, Ne.symm h, Function.update]

/-- Visiting each generated ID once supplies the incidence rows used by
`actualSlot_numbers` without separate searches over the graph at each site. -/
def collectedRow {E S : Type*} [DecidableEq S] (atSite : E → S) (stream : List E)
    (hn : stream.Nodup) (hall : ∀ i, i ∈ stream) (s : S) : IncidentRow atSite s where
  ids := collectRows atSite stream (fun _ ↦ []) s
  nodup := by simpa [collectRows_eq] using hn.filter (fun i ↦ decide (atSite i = s))
  complete := by intro i; simp [collectRows_eq, hall]

variable {V H Tag L : Type*} {d c N J nL : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)
variable (subdiv : Fin 4 → ℕ)

/-- Forget the absolute lane but retain the entire original CD arc, type and subdivision. -/
def baseId (i : Id P.Motif subdiv) : Id P.BaseMotif subdiv :=
  ⟨i.1, P.baseMotif i.2.1, i.2.2⟩

/-- At either end, normalizing all motif lanes gives a bijection of the actual
incidence fiber with the fiber used in the sorted base graph. -/
def incidentBaseEquiv (layout : Bool) (pick : Fin 4 → PackedRole) (s : Site V Tag L) :
    {i : Id P.Motif subdiv // endpoint (P.survivingRole layout) pick i = s} ≃
      {z : Id P.BaseMotif subdiv // endpoint (P.roleBase layout) pick z = packedBase s} :=
  (endpointFiberEquiv (P.survivingRole layout) pick subdiv s).trans
    ((Equiv.sigmaCongrRight fun t ↦
      (P.baseRoleFiberEquiv (P.survivingRole layout (pick t))
        (P.survivingRole_translate layout (pick t)) (packedBase s) s.2.2).symm.prodCongr
          (Equiv.refl (Fin (subdiv t)))).trans
      (endpointFiberEquiv (P.roleBase layout) pick subdiv (packedBase s)).symm)

@[simp] theorem incidentBaseEquiv_val (layout : Bool) (pick : Fin 4 → PackedRole)
    (s : Site V Tag L) (a) :
    (incidentBaseEquiv P subdiv layout pick s a).val = baseId P subdiv a.val := rfl

private theorem baseRow_nodup (layout : Bool) (pick : Fin 4 → PackedRole) (s : Site V Tag L)
    (r : IncidentRow (endpoint (P.survivingRole layout) pick (subdiv := subdiv)) s) :
    (r.ids.map (baseId P subdiv)).Nodup := by
  apply r.nodup.map_on
  intro x hx y hy h
  let f := incidentBaseEquiv P subdiv layout pick s
  let x' := (⟨x, (r.complete _).mp hx⟩ : {a // endpoint (P.survivingRole layout) pick a = s})
  let y' := (⟨y, (r.complete _).mp hy⟩ : {a // endpoint (P.survivingRole layout) pick a = s})
  exact congrArg Subtype.val (f.injective (Subtype.ext (show (f x').val = (f y').val from h)))

private theorem baseRow_complete (layout : Bool) (pick : Fin 4 → PackedRole) (s : Site V Tag L)
    (r : IncidentRow (endpoint (P.survivingRole layout) pick (subdiv := subdiv)) s)
    (z : Id P.BaseMotif subdiv) :
    z ∈ r.ids.map (baseId P subdiv) ↔ endpoint (P.roleBase layout) pick z = packedBase s := by
  let f := incidentBaseEquiv P subdiv layout pick s
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact (f ⟨a, (r.complete _).mp ha⟩).property
  · intro h
    let z' := (⟨z, h⟩ : {z // endpoint (P.roleBase layout) pick z = packedBase s})
    exact List.mem_map.mpr ⟨(f.symm z').val, (r.complete _).mpr (f.symm z').property,
      congrArg Subtype.val (f.apply_symm_apply z')⟩

/-- The radix of the unconsumed-lane-independent relative key. -/
abbrev keyCount (N J d c : ℕ) (subdiv : Fin 4 → ℕ) :=
  4 * ((N * (J * (d * (2 ^ c * d)))) * ∑ t, subdiv t)

variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J)

/-- Integer key stored in the incoming or outgoing incidence row. -/
def relativeKey (i : Id P.Motif subdiv) : Fin (keyCount N J d c subdiv) :=
  P.slotIdentifier vertices tags subdiv (baseId P subdiv i)

/-- A record ID keeps the original absolute lane of the motif. Dummies are
indexed by their absolute source site and local dummy number. -/
def arcAddress (lanes : L ≃ Fin nL) (deficit : ℕ) :
    (Id P.Motif subdiv ⊕ Site V Tag L × Fin deficit) ↪
      Fin (keyCount N J d c subdiv * nL + (N * (J * nL)) * deficit) := by
  let genuine : Id P.Motif subdiv ↪ Fin (keyCount N J d c subdiv * nL) := {
    toFun := fun i ↦ finProdFinEquiv (relativeKey P subdiv vertices tags i, lanes (P.sourceLane i.2.1))
    inj' := by
      rintro ⟨t, m, h⟩ ⟨t', m', h'⟩ e
      obtain ⟨eb, eg⟩ := Prod.mk.inj (finProdFinEquiv.injective e)
      have ez := P.slotIdentifier_injective vertices tags subdiv eb
      change (⟨t, P.baseMotif m, h⟩ : Id P.BaseMotif subdiv) = ⟨t', P.baseMotif m', h'⟩ at ez
      obtain rfl : t = t' := congrArg Sigma.fst ez
      have emh : (P.baseMotif m, h) = (P.baseMotif m', h') := eq_of_heq (Sigma.mk.inj_iff.mp ez).2
      obtain rfl : m = m' := P.motifLaneEquiv.injective (Prod.ext (Prod.mk.inj emh).1 (lanes.injective eg))
      obtain rfl := Prod.mk.inj emh |>.2
      rfl }
  let site := (vertices.prodCongr ((tags.prodCongr lanes).trans finProdFinEquiv)).trans finProdFinEquiv
  let dummy := (site.prodCongr (Equiv.refl (Fin deficit))).trans finProdFinEquiv
  exact (genuine.sumMap dummy.toEmbedding).trans finSumFinEquiv.toEmbedding

/-- Two directly addressed endpoint fields for each generated actual arc. -/
def endpointAddress {E : Type*} {B : ℕ} (arc : E ↪ Fin B) : E × Fin 2 ↪ Fin (B * 2) :=
  (arc.prodMap (Equiv.refl (Fin 2)).toEmbedding).trans finProdFinEquiv.toEmbedding

/-- Even with unoccupied mixed-radix keys, the space for both endpoint fields
is linear in the number of absolute sites. -/
theorem endpointAddress_size (N J nL d c deficit : ℕ) (subdiv : Fin 4 → ℕ) :
    (keyCount N J d c subdiv * nL + (N * (J * nL)) * deficit) * 2 =
      (N * J * nL) * (2 * (4 * d * (2 ^ c * d) * (∑ t, subdiv t) + deficit)) := by
  unfold keyCount
  ring

/-- Counting smaller keys computes the zero-based position in the sorted row. -/
def rowRank (i : Id P.Motif subdiv) (ids : List (Id P.Motif subdiv)) : ℕ :=
  ids.countP fun j ↦ decide (relativeKey P subdiv vertices tags j < relativeKey P subdiv vertices tags i)

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

private theorem IncidentRow.length_eq_card {E S : Type*} [Fintype E] [DecidableEq E] [DecidableEq S]
    {endSite : E → S} {s} (r : IncidentRow endSite s) : r.ids.length = Fintype.card {a // endSite a = s} := by
  rw [← List.toFinset_card_of_nodup r.nodup, Fintype.card_subtype]
  congr 1
  ext a
  simp [r.complete]

/-- The count in one absolute row is the fixed surviving degree; the role map
may designate either orientation, including roles shared by parallel edges. -/
theorem incidentRow_length (hc : 2 ≤ c) (layout : Bool) (pick : Fin 4 → PackedRole)
    (s : Site V Tag L) (r : IncidentRow (endpoint (P.survivingRole layout) pick (subdiv := subdiv)) s) :
    r.ids.length = survivingDegree d c subdiv := by
  classical
  rw [r.length_eq_card, Fintype.card_congr (incidentBaseEquiv P subdiv layout pick s)]
  exact card_endpoint _ _ _ (P.card_roleBase hc layout) _

variable [Module (ZMod 2) Tag]

/-- Both word-sort ranks agree with the regularized graph, for every absolute
arc and arbitrary input visitation order in the two local lists. -/
theorem actualSlot_numbers (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (layout : Bool) {d' : ℕ} (hd : survivingDegree d c subdiv ≤ d') (hJ : 1 < J)
    (i : Id P.Motif subdiv)
    (outRow : IncidentRow (endpoint (P.survivingRole layout) (sourceRole layout))
      (endpoint (P.survivingRole layout) (sourceRole layout) i))
    (inRow : IncidentRow (endpoint (P.survivingRole layout) (targetRole layout))
      (endpoint (P.survivingRole layout) (targetRole layout) i)) :
    let := P.slotIdentifierOrder vertices tags subdiv
    let I := P.regularizedSlotIndexing hc hφ layout subdiv hd tags hJ
    let z := baseId P subdiv i
    rowRank P subdiv vertices tags i outRow.ids = (I.outgoing (.inl z)).2.val ∧
      rowRank P subdiv vertices tags i inRow.ids = (I.incoming (.inl z)).2.val := by
  let := P.slotIdentifierOrder vertices tags subdiv
  let z := baseId P subdiv i
  let O := outRow.ids.map (baseId P subdiv)
  let D := inRow.ids.map (baseId P subdiv)
  have atBase (pick : Fin 4 → PackedRole) : endpoint (P.roleBase layout) pick z =
      packedBase (endpoint (P.survivingRole layout) pick i) :=
    (incidentBaseEquiv P subdiv layout pick _ ⟨i, rfl⟩).property
  have hO a : a ∈ O.toFinset ↔ endpoint (P.roleBase layout) (sourceRole layout) a =
      endpoint (P.roleBase layout) (sourceRole layout) z := by
    rw [List.mem_toFinset, atBase]; exact baseRow_complete _ _ _ _ _ outRow a
  have hD a : a ∈ D.toFinset ↔ endpoint (P.roleBase layout) (targetRole layout) a =
      endpoint (P.roleBase layout) (targetRole layout) z := by
    rw [List.mem_toFinset, atBase]; exact baseRow_complete _ _ _ _ _ inRow a
  have hn := paddedSlot_numbers (endpoint (P.roleBase layout) (sourceRole layout))
    (endpoint (P.roleBase layout) (targetRole layout))
    (P.roleDisplacement layout (sourceRole layout) (targetRole layout))
    (fun a ↦ (P.survivingSlot_bases_ne hφ layout (subdiv := subdiv) ⟨a.1, a.2.1.1, a.2.2⟩).symm)
    (card_endpoint _ _ subdiv (P.card_roleBase hc layout)) (card_endpoint _ _ subdiv (P.card_roleBase hc layout))
    hd (cycleTags tags) (cycleTags_ne tags hJ) z O.toFinset D.toFinset hO hD
  have rout := (baseRow_nodup P subdiv layout (sourceRole layout) _ outRow).card_eq_countP
    (P := (· < z))
  have rin := (baseRow_nodup P subdiv layout (targetRole layout) _ inRow).card_eq_countP
    (P := (· < z))
  rw [List.countP_map] at rout rin
  exact ⟨rout.symm.trans hn.1.symm, rin.symm.trans hn.2.symm⟩

/-- The numerical incoming field and the source-relative displacement describe the
actual destination of this absolute arc. -/
theorem actualSlot_route (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (layout : Bool) {d' : ℕ} (hd : survivingDegree d c subdiv ≤ d') (hJ : 1 < J)
    (i : Id P.Motif subdiv) :
    let := P.slotIdentifierOrder vertices tags subdiv
    let I := P.regularizedSlotIndexing hc hφ layout subdiv hd tags hJ
    let z := baseId P subdiv i
    let s := endpoint (P.survivingRole layout) (sourceRole layout) i
    let t := endpoint (P.survivingRole layout) (targetRole layout) i
    I.graph.actualTarget (I.outgoing (.inl z), s.2.2) = (I.incoming (.inl z), t.2.2) ∧
      (I.outgoing (.inl z)).1 = packedBase s ∧ (I.incoming (.inl z)).1 = packedBase t := by
  intro order I z s t
  let e := P.survivingLaneEquiv layout subdiv
  have he : (z,s.2.2) = e i := by cases i; rfl
  have h := P.survivingLane_endpoints layout subdiv z s.2.2
  change endpoint _ _ (e.symm (z,s.2.2)) = _ ∧ endpoint _ _ (e.symm (z,s.2.2)) = _ at h
  rw [he, e.symm_apply_apply] at h
  refine ⟨(I.actualTarget (.inl z) s.2.2).trans (congrArg (Prod.mk _) (congrArg (fun v : Site V Tag L ↦ v.2.2) h.2).symm), ?_, ?_⟩
  · exact (I.src_eq (.inl z)).trans (congrArg packedBase h.1).symm
  · exact (I.dst_eq (.inl z)).trans (congrArg packedBase h.2).symm

/-- A dummy's endpoint numbers are obtained by a single addition at both ends.
The arc advances the tag at its base and preserves the absolute lane. -/
theorem dummySlot_route (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (layout : Bool) {d' : ℕ} (hd : survivingDegree d c subdiv ≤ d') (hJ : 1 < J)
    (b : V × Tag) (g : L) (j : Fin (d' - survivingDegree d c subdiv)) :
    let := P.slotIdentifierOrder vertices tags subdiv
    let I := P.regularizedSlotIndexing hc hφ layout subdiv hd tags hJ
    let z := Sum.inr (b,j)
    let rank := survivingDegree d c subdiv + j.val
    (I.outgoing z).2.val = rank ∧ (I.incoming z).2.val = rank ∧
      (I.outgoing z).1 = b ∧ (I.incoming z).1 = cycleTags tags b ∧
      I.graph.actualTarget (I.outgoing z, g) = (I.incoming z, g) := by
  intro order I z rank
  exact ⟨rfl, rfl, rfl, rfl, by simpa [z, paddedShift] using I.actualTarget z g⟩

open BurstRAM.PrivateRAM PrimedStackRAM

/-- Write the known slot of a padding or degree-refresh arc into one endpoint field. -/
def directWrite : List (Op 2 1) := [.publicWord 0 0, .stateWord 1, .write 0 1]

theorem directWrite_native {w : ℕ} (pub : Fin 1 → Word w) (rank : Word w) (mem : Memory w) :
    let M := (template directWrite 1).instantiate w pub
    execute M.program 4 (M.program.start rank) mem [] =
      some ⟨[.tick, .tick, .write (pub 0) rank], some rank⟩ ∧
      after mem [.tick, .tick, .write (pub 0) rank] = writeMemory mem (pub 0) rank ∧
      countProbes [.tick, .tick, .write (pub 0) rank] = 1 := by
  refine ⟨?_, rfl, rfl⟩
  change execute ((template directWrite 1).instantiate w pub).program (1 + directWrite.length)
    ⟨_, rank, fun _ => 0, fun _ => 0⟩ mem [] = _
  rw [execute_template, run_eq_trace]
  rfl

/-- At a refresh, the indexed expander's reverse arc supplies the incoming
slot in the promoted graph. Both fields can be written by `directWrite`. -/
theorem refresh_internal_route {U T K : Type*} [AddCommGroup K] {D h h₀ : ℕ}
    (G : LiftedSlots U D (T × K)) (E : SpectralGeometry.RegularArcGraph (Fin D) h)
    (hD : 1 < D) (hh : h + 1 ≤ h₀) (u : U) (port : Fin D) (g : K) (j : Fin h) :
    (degreeRefresh G E.toSlotGraph hD hh).actualGraph.target
      (((u,port),g), refreshSlots hh (.inr (.inl j))) =
        (((u,(E.reverse (port,j)).1),g), refreshSlots hh (.inr (.inl (E.reverse (port,j)).2))) :=
  degreeRefresh_internal G E.toSlotGraph hD hh u port g j

/-- Encode the relative key into a machine word with headroom for the increment
used by the unsigned rank comparison. -/
def keyWord {w : ℕ} (hfit : keyCount N J d c subdiv < 2 ^ w) (i : Id P.Motif subdiv) : Word w :=
  (relativeKey P subdiv vertices tags i).castLE hfit.le

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [DecidableEq V] [DecidableEq Tag]
  [DecidableEq L] [Module (ZMod 2) Tag] in
/-- A single native call ranks one actual arc in its unsorted endpoint row and
writes that rank. `actualSlot_numbers` identifies these returned words with the
two fields of the regularized graph. -/
theorem recordRank_native {w : ℕ} (hfit : keyCount N J d c subdiv < 2 ^ w)
    (pub : Fin 2 → Word w) (mem : Memory w) (i : Id P.Motif subdiv) (ids : List (Id P.Motif subdiv))
    (hread : ∀ j : Fin ids.length, mem ((pub 0).val + j.val) = keyWord P subdiv vertices tags hfit ids[j.val])
    (hrow : (pub 0).val + ids.length ≤ 2 ^ w) (hlen : ids.length < 2 ^ w) :
    let M := (template (SlotRankRAM.rankCode ids.length) 3).instantiate w pub
    let pivot := keyWord P subdiv vertices tags hfit i
    let rank := Fin.ofNat (2 ^ w) (rowRank P subdiv vertices tags i ids)
    ∃ es, execute M.program (6 * ids.length + 6) (M.program.start pivot) mem [] =
        some ⟨es, some rank⟩ ∧ after mem es = writeMemory mem (pub 1) rank ∧
        countProbes es = ids.length + 1 ∧ es.length + 1 = 6 * ids.length + 6 := by
  let key := keyWord P subdiv vertices tags hfit
  let row := ids.map key
  have hl : row.length = ids.length := List.length_map _
  have hr (j : Fin row.length) : mem ((pub 0).val + j.val) = row[j.val] := by
    simpa [row, key] using hread ⟨j.val, hl ▸ j.isLt⟩
  have hk (x : Word w) (hx : x ∈ row) : x.val + 1 < 2 ^ w := by
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact (Nat.succ_le_of_lt (relativeKey P subdiv vertices tags a).isLt).trans_lt hfit
  have rankEq : (row.filter fun x ↦ decide (x < key i)).length = rowRank P subdiv vertices tags i ids := by
    rw [← List.countP_eq_length_filter, List.countP_map]
    rfl
  have h := SlotRankRAM.rank_native pub (key i) mem row hr (hl ▸ hrow) (hl ▸ hlen) hk
  let Runs (n rank : ℕ) :=
    let M := (template (SlotRankRAM.rankCode n) 3).instantiate w pub
    ∃ es, execute M.program (6*n+6) (M.program.start (key i)) mem [] =
        some ⟨es, some (Fin.ofNat _ rank)⟩ ∧ after mem es = writeMemory mem (pub 1) (Fin.ofNat _ rank) ∧
        countProbes es = n+1 ∧ es.length+1 = 6*n+6
  change Runs row.length ((row.filter fun x ↦ decide (x < key i)).length) at h
  change Runs ids.length (rowRank P subdiv vertices tags i ids)
  rwa [hl, rankEq] at h

/-- Execution of one endpoint call with its actual write log. The number of
keys is fixed by the compressor block. -/
abbrev rankExecution {w : ℕ} (n : ℕ) (pub : Fin 2 → Word w) (pivot : Word w)
    (mem : Memory w) (es : List (Event w)) (rank : Word w) : Prop :=
  let M := (template (SlotRankRAM.rankCode n) 3).instantiate w pub
  execute M.program (6*n + 6) (M.program.start pivot) mem [] = some ⟨es, some rank⟩

/-- Starting with the two incident arrays at the actual source and target,
run both rank calls on the same arc. The second call reads the first call's
post-memory. The resulting arc record contains both correct slot numbers. -/
theorem actualSlot_writeback {w : ℕ} (hfit : keyCount N J d c subdiv < 2 ^ w)
    (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (layout : Bool) {d' : ℕ} (hd : survivingDegree d c subdiv ≤ d') (hJ : 1 < J)
    (hsize : d' < 2 ^ w) (i : Id P.Motif subdiv)
    (outRow : IncidentRow (endpoint (P.survivingRole layout) (sourceRole layout))
      (endpoint (P.survivingRole layout) (sourceRole layout) i))
    (inRow : IncidentRow (endpoint (P.survivingRole layout) (targetRole layout))
      (endpoint (P.survivingRole layout) (targetRole layout) i))
    (mem : Memory w) (po pi : Fin 2 → Word w)
    (hout : ∀ j : Fin outRow.ids.length, mem ((po 0).val + j.val) =
      keyWord P subdiv vertices tags hfit outRow.ids[j.val])
    (hin : ∀ j : Fin inRow.ids.length, mem ((pi 0).val + j.val) =
      keyWord P subdiv vertices tags hfit inRow.ids[j.val])
    (hrowOut : (po 0).val + outRow.ids.length ≤ 2 ^ w) (hrowIn : (pi 0).val + inRow.ids.length ≤ 2 ^ w)
    (hsep : ∀ j : Fin inRow.ids.length, (pi 0).val + j.val ≠ (po 1).val) (hdist : po 1 ≠ pi 1) :
    let := P.slotIdentifierOrder vertices tags subdiv
    let I := P.regularizedSlotIndexing hc hφ layout subdiv hd tags hJ
    let z := Sum.inl (baseId P subdiv i)
    let k := survivingDegree d c subdiv
    let key := keyWord P subdiv vertices tags hfit i
    let outSlot := (I.outgoing z).2.castLE hsize.le
    let inSlot := (I.incoming z).2.castLE hsize.le
    ∃ es fs, rankExecution k po key mem es outSlot ∧ rankExecution k pi key (after mem es) fs inSlot ∧
      after (after mem es) fs (po 1).val = outSlot ∧ after (after mem es) fs (pi 1).val = inSlot ∧
      countProbes es + countProbes fs = 2 * (k + 1) := by
  intro order I z k key outSlot inSlot
  have hlo := incidentRow_length P subdiv hc layout (sourceRole layout) _ outRow
  have hli := incidentRow_length P subdiv hc layout (targetRole layout) _ inRow
  obtain ⟨ho, hi⟩ := actualSlot_numbers P subdiv vertices tags hc hφ layout hd hJ i outRow inRow
  have wo : Fin.ofNat (2 ^ w) (rowRank P subdiv vertices tags i outRow.ids) = outSlot := by
    apply Fin.ext
    change rowRank P subdiv vertices tags i outRow.ids % (2 ^ w) = _
    rw [ho, Nat.mod_eq_of_lt ((I.outgoing z).2.isLt.trans hsize)]
    rfl
  have wi : Fin.ofNat (2 ^ w) (rowRank P subdiv vertices tags i inRow.ids) = inSlot := by
    apply Fin.ext
    change rowRank P subdiv vertices tags i inRow.ids % (2 ^ w) = _
    rw [hi, Nat.mod_eq_of_lt ((I.incoming z).2.isLt.trans hsize)]
    rfl
  obtain ⟨es, he, hm, hp, _⟩ := recordRank_native P subdiv vertices tags hfit po mem i outRow.ids
    hout hrowOut (hlo ▸ hd.trans_lt hsize)
  rw [wo] at hm
  have hread (j : Fin inRow.ids.length) : after mem es ((pi 0).val+j.val) =
      keyWord P subdiv vertices tags hfit inRow.ids[j.val] := by
    simp [hm, writeMemory, hsep j, hin j]
  obtain ⟨fs, hf, hm', hp', _⟩ := recordRank_native P subdiv vertices tags hfit pi (after mem es) i
    inRow.ids hread hrowIn (hli ▸ hd.trans_lt hsize)
  rw [wi] at hm'
  have hv : (po 1).val ≠ (pi 1).val := fun h ↦ hdist (Fin.ext h)
  refine ⟨es, fs, ?_, ?_, ?_, ?_, ?_⟩
  · change rankExecution outRow.ids.length po key mem es _ at he
    simpa only [hlo, wo] using he
  · change rankExecution inRow.ids.length pi key (after mem es) fs _ at hf
    simpa only [hli, wi] using hf
  · rw [hm', hm]; simp [writeMemory, hv]
  · simp [hm', writeMemory]
  · rw [hp, hp', hlo, hli]; omega

omit [Module (ZMod 2) Tag] in
/-- The total number of endpoint-writeback probes in a complete shrinking scan.
Each genuine arc costs one rank scan per endpoint and each dummy costs two
single-word writes. The coefficient of the position count depends only on the
two fixed degrees and the subdivision profile. -/
theorem writeback_probes (hc : 2 ≤ c) (layout : Bool) (deficit : ℕ) :
    let k := survivingDegree d c subdiv
    let cost : Id P.Motif subdiv ⊕ Site V Tag L × Fin deficit → ℕ :=
      Sum.elim (fun _ ↦ 2 * (k + 1)) (fun _ ↦ 2)
    ∑ i, cost i = Fintype.card (Site V Tag L) * (2 * (k * (k + 1) + deficit)) := by
  intro k cost
  let src := endpoint (P.survivingRole layout) (sourceRole layout) (subdiv := subdiv)
  have hcard : Fintype.card (Id P.Motif subdiv) = Fintype.card (Site V Tag L) * k := by
    rw [Fintype.card_congr (Equiv.sigmaFiberEquiv src).symm, Fintype.card_sigma]
    have h s : Fintype.card {a // src a = s} = k := (P.survivingSlot_degree hc layout subdiv s).1
    simp [h]
  simp only [Fintype.sum_sum_type, cost, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, hcard, Fintype.card_prod, Fintype.card_fin]
  ring

end CompressorRecords.Slots

end VPVNP
end Computability
end OAI
