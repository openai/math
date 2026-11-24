import OAI.Computability.VPVNP.CompressorSliceSchedule
import OAI.Computability.VPVNP.CompressorRecordsDemandRAM
import OAI.Computability.VPVNP.CompressorSlotLevelRun
import OAI.Computability.VPVNP.CompressorSlotOwnerAux
import OAI.Computability.VPVNP.CompressorSlotOwnerDecode
import OAI.Computability.VPVNP.CompressorRecordsBundleGather
import OAI.Computability.VPVNP.CompressorRecordRefreshAllSlots
import OAI.Computability.VPVNP.RAMFinite

/-!
# Costs of the physical slot and slice passes of Appendix E

A pass is charged for every worker call and external probe, including visits to
empty records. The site count multiplies constants determined by the degree and
the subdivision template. Field widths affect the values stored in words, while
the directory allocations count fields and candidate intersections.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PhaseCosts

open BurstRAM Compression

variable {w : ℕ}

/-- The native schedule consumes one branch record per executed worker. -/
theorem run_length {C : Type*} {P : BurstRAM.Program w C} {fuel st mem bs rs}
    (hr : runSegment P fuel st mem bs = some rs) : rs.length = bs.length := by
  have h := ((runSegment_iff ..).mp hr).2.2
  simpa [branchPaths] using congrArg List.length h

/-- Each report in a successful native segment obeys the segment worker cap. -/
theorem run_cap {C : Type*} {P : BurstRAM.Program w C} {fuel st mem bs rs}
    (hr : runSegment P fuel st mem bs = some rs) : ∀ r ∈ rs, r.events.length + 1 ≤ fuel :=
  fun r h ↦ localSegment_event_bound ((runSegment_iff ..).mp hr).1 r h

private theorem probeCount_eq_sum (rs : List (Report w)) :
    RAMBuckets.probeCount Report.probes rs = (rs.map Report.probes).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [RAMBuckets.probeCount, ih]

/-- One family of concrete slice workspaces, each starting at the memory handed to it. -/
structure SliceInput (w : ℕ) (old new : List ℕ) where
  /-- Base address of the old field widths supplied to the slice construction. -/
  oldBase : Word w
  /-- Base address of the new field widths against which the slice construction intersects the
  old fields. -/
  newBase : Word w
  /-- Start of the workspace used to build field boundaries, copy records, and adjacency data
  for this slice. -/
  scratch : Word w
  /-- Memory presented to the slice workers, containing the specified old and new width arrays. -/
  initial : Memory w
  workspace : SliceSchedule.Workspace oldBase newBase scratch old.length new.length
  oldSum : old.sum < 2^w
  newSum : new.sum < 2^w
  oldWidths : ∀ i (hi : i < old.length), (initial (oldBase.val+i)).val = old[i]
  newWidths : ∀ j (hj : j < new.length), (initial (newBase.val+j)).val = new[j]

/-- Native segment executions and their physical output tables. -/
def SliceInput.produces {old new : List ℕ} (t : SliceInput w old new)
    (r : SliceSchedule.Passes w) : Prop :=
  SliceSchedule.NativePasses t.oldBase t.newBase t.scratch old.length new.length t.initial r ∧
    SliceSchedule.Stored t.scratch old new t.initial (r.result t.initial)

/-- End-to-end resource bounds for the five passes, together with the resulting physical
tables. `M` and `N` bound the number of source and destination fields per invocation. -/
def SliceCosts {ι : Type*} [Fintype ι] (old new : ι → List ℕ)
    (input : ∀ i, SliceInput w (old i) (new i)) (M N : ℕ) : Prop :=
  ∃ rs : ι → SliceSchedule.Passes w,
    (∀ i, (input i).produces (rs i)) ∧
    (∀ i, ∀ r ∈ (rs i).all, r.events.length + 1 ≤ 38) ∧
    (∑ i, (rs i).all.length) ≤ Fintype.card ι * (2 + 2*(M+N) + 2*(M*N)) ∧
    (∑ i, RAMBuckets.cost Report.probes (rs i).all) ≤
      Fintype.card ι * (4 + 7*(M+N) + 16*(M*N)) ∧
    (∑ i, ((rs i).all.map fun r ↦ r.events.length + 1).sum) ≤
      Fintype.card ι * (16 + 22*(M+N) + 74*(M*N)) ∧
    (∀ i, SliceSchedule.stop (input i).scratch.val (old i).length (new i).length ≤
      (input i).scratch.val + 2 + 2*(M+N) + 5*(M*N))

/-- All slice calls from actual input arrays, with costs summed across sites and a bound
on the largest row address. Empty fields and empty intersections are charged as well. -/
theorem sliceSites {ι : Type*} [Fintype ι] (old new : ι → List ℕ)
    (input : ∀ i, SliceInput w (old i) (new i)) {M N : ℕ}
    (ho : ∀ i, (old i).length ≤ M) (hn : ∀ i, (new i).length ≤ N) :
    SliceCosts old new input M N := by
  classical
  have one (i : ι) := SliceSchedule.build (old i) (new i) (input i).oldBase (input i).newBase
    (input i).scratch (input i).initial (input i).workspace (input i).oldSum (input i).newSum
    (input i).oldWidths (input i).newWidths
  choose rs hnative hstored hcalls hprobe hinst using one
  have hprod (i : ι) := Nat.mul_le_mul (ho i) (hn i)
  have hsum (i : ι) := Nat.add_le_add (ho i) (hn i)
  have hrec (i : ι) := copyRecords_length_le (old i) (new i)
  refine ⟨rs, fun i ↦ ⟨hnative i, hstored i⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i r hr
    simp only [SliceSchedule.Passes.all, List.mem_append] at hr
    rcases hr with (((h|h)|h)|h)|h
    · exact (run_cap (hnative i).preparation.clearNative r h).trans (by decide)
    · exact (run_cap (hnative i).preparation.oldNative r h).trans (by decide)
    · exact (run_cap (hnative i).preparation.newNative r h).trans (by decide)
    · exact run_cap (hnative i).pairs r h
    · exact (run_cap (hnative i).adjacency r h).trans (by decide)
  · rw [← Nat.nsmul_eq_mul, ← Finset.card_univ (α := ι), ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ ↦ by have := hcalls i; have := hsum i; have := hprod i; omega
  · rw [← Nat.nsmul_eq_mul, ← Finset.card_univ (α := ι), ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro i _
    rw [RAMBuckets.cost_eq_length_add_probes, probeCount_eq_sum, hcalls i, hprobe i]
    have := hprod i; have := hsum i; have := hrec i; omega
  · rw [← Nat.nsmul_eq_mul, ← Finset.card_univ (α := ι), ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro i _
    rw [hinst i]
    have := hprod i; have := hsum i; have := hrec i; omega
  · intro i
    unfold SliceSchedule.stop SliceSchedule.frameHead
    have := hprod i; have := hsum i; omega

open Compression.PackingData in
/-- One demand slice invocation per packed bundle, on its actual thick and motif fields. -/
theorem demandSliceCosts {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag]
    [AddCommGroup L] [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
    [DecidableEq V] [DecidableEq Tag] [DecidableEq L] (P : PackingData V H Tag L d c)
    (number : P.BundleNumbering) (order : P.ThickNumbering) (width : Arc V H Tag L d c → ℕ) :
    let old := fun b ↦ orderedWidths (order b) (fun s ↦ width s.1.1)
    let new := fun b ↦ orderedWidths (number b) (fun t ↦ P.abWidth number width t.1)
    ∀ input : ∀ b, SliceInput w (old b) (new b),
      SliceCosts old new input (2^c*d/4) (pieceCount d c) := by
  intro old new input
  apply sliceSites <;> intro b <;> simp [old, new, orderedWidths]

/-- Subdivision slice invocation for every surviving role edge in the selected template. -/
theorem subdivisionSliceCosts {ι : Type*} [Fintype ι] (width : ι → ℕ) (subdiv : Fin 4 → ℕ)
    (role : ι → Fin 4) :
    let old := fun i ↦ [width i]
    let new := fun i ↦ List.ofFn (splitWidth (width i) (subdiv (role i)))
    ∀ input : ∀ i, SliceInput w (old i) (new i),
      SliceCosts old new input 1 (∑ t, subdiv t) := by
  intro old new input
  apply sliceSites
  · simp [old]
  · intro i
    simpa [new] using
      (Finset.single_le_sum (fun t _ ↦ Nat.zero_le (subdiv t)) (Finset.mem_univ (role i)))

/-- A refresh bundle concatenates its original slot widths into a single external word. -/
theorem refreshSliceCosts {ι : Type*} [Fintype ι] {d : ℕ} (width : ι → Fin d → ℕ) :
    let old := fun i ↦ List.ofFn (width i)
    let new := fun i ↦ [∑ k, width i k]
    ∀ input : ∀ i, SliceInput w (old i) (new i), SliceCosts old new input d 1 := by
  intro old new input
  apply sliceSites <;> intro i <;> simp [old, new]

/-- From the actual chosen placement, allocate exactly one bounded row per packed site and
run the native preimage scan. There are `2^c*d` entries in every row, for either layout. -/
theorem placementPreimages {V H Tag L : Type} {d c A B : ℕ}
    [AddCommGroup Tag] [AddCommGroup L] [Finite V] [Finite H] [Finite Tag] [Finite L]
    (P : PackingData V H Tag L d c)
    (layout : Bool) (hc : 0 < c) (old : Position V H Tag L c ≃ Fin A) (new : Site V Tag L ≃ Fin B)
    (p : Fin 6 → Word w) (regions : RowRegions p) (hA : (p 0).val = A) (hB : (p 2).val = B)
    (cap : (p 4).val = 2 ^ c * d) (mem : Memory w)
    (owners : ∀ i : Word w, i < p 0 → ownerAt p mem i = encodedPlacement old new
      (P.placement layout) i)
    (zero : ∀ i : Word w, i < p 2 → mem (countAt p i).val = 0) :
    let place := encodedPlacement old new (P.placement layout) (w := w)
    let M := (PrimedStackRAM.template collectPreimage 3).instantiate w p
    ∃ rs, runSegment M.program 23 (some 0) mem (List.replicate A []) = some rs ∧
      PreimagesAt p place (after mem (eventLog rs)) A ∧
      rs.length = B * (2^c*d) ∧ RAMBuckets.cost Report.probes rs = B * (5*(2^c*d)) ∧
      (∀ r ∈ rs, r.events.length + 1 = 23) ∧
      (p 0).val + (p 2).val + (p 2).val * (p 4).val = B * (1+2*(2^c*d)) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite H
  let := Fintype.ofFinite Tag
  let := Fintype.ofFinite L
  intro place M
  have ha : A ≤ 2^w := hA ▸ (p 0).isLt.le
  have hb : B ≤ 2^w := hB ▸ (p 2).isLt.le
  have hsize : A = B*(2^c*d) := by
    have oldCard := Fintype.card_congr old
    have newCard := Fintype.card_congr new
    rw [Fintype.card_fin] at oldCard newCard
    rw [← oldCard, Fintype.card_congr (Equiv.sigmaFiberEquiv (P.placement layout)).symm,
      Fintype.card_sigma]
    simp only [P.card_placement hc layout, Finset.sum_const, Finset.card_univ, newCard,
      Nat.nsmul_eq_mul]
  have legal (i : Word w) (hi : i < p 0) : place i < p 2 := by
    let j : Fin A := ⟨i.val, hA ▸ hi⟩
    have e : Fin.ofNat (2^w) j.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    change (encodedPlacement _ _ _ i).val < (p 2).val
    rw [← e, encodedPlacement_eq old new _ ha hb j, hB]
    exact (new _).isLt
  have capacity (u : Word w) (hu : u < p 2) : (preimagePrefix place u (p 0).val).length ≤
    (p 4).val := by
    let j : Fin B := ⟨u.val, hB ▸ hu⟩
    obtain ⟨s, hs⟩ := new.surjective j
    have e : Fin.ofNat (2^w) (new s).val = u := hs ▸ Fin.ext (Nat.mod_eq_of_lt u.isLt)
    rw [hA, ← e, encodedPlacement_rowLength old new _ ha hb s, P.card_placement hc layout, cap]
  have start : PreimagesAt p place mem 0 :=
    ⟨owners, fun u hu ↦ by simp [preimagePrefix, rowRepresents, zero u hu]⟩
  obtain ⟨rs, hr, done, hlen, hwork⟩ := collectPreimages_run regions legal capacity start A
    (by simp [hA])
  refine ⟨rs, hr, (by simpa using done), hlen.trans hsize, ?_, fun r h ↦ by rw [(hwork r h).1], ?_⟩
  · change RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) rs = _
    rw [preimagePass_cost (fun r h ↦ (hwork r h).2), hlen, hsize]
    ring
  · rw [hA, hB, cap, hsize]
    ring

/-- Scratch and immutable source arrays for the four ordered slot passes. The genuine
region includes every mixed-radix candidate, including subdivision and thick-wire holes. -/
theorem orderedSlotAllocation (N J lanes d c pad deg : ℕ) (subdiv : Fin 4 → ℕ) :
    let sites := N*(J*lanes)
    let keys := 4*d*(2^c*d)*(∑ t, subdiv t)
    let A := Slots.RecordCount N J lanes d c pad subdiv * 2
    let B := sites*2
    A + (B+A) + (B+A)*deg + A =
        sites * (6*(keys+pad) + 2 + (2+2*(keys+pad))*deg) ∧
    4*(Slots.oldBaseArcCount N J d c * lanes) + sites + 12 =
        sites * (4*d*(2^c*d)+1) + 12 := by
  dsimp only [Slots.RecordCount, Slots.keyCount, Slots.oldBaseArcCount]
  constructor <;> ring

private theorem instruction_total (rs : List (Report w)) (cap : ℕ)
    (h : ∀ r ∈ rs, r.events.length + 1 = cap) :
    (rs.map fun r ↦ r.events.length + 1).sum = rs.length * cap := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rw [List.map_cons, List.sum_cons, h r (by simp), ih (fun q hq ↦ h q (by simp [hq])),
      List.length_cons, Nat.succ_mul, Nat.add_comm]

open scoped Classical in
open PackingData SlotSchedule PrimedStackRAM in
/-- Costs on the actual ordered directory. The candidate count includes holes and the
two sides of each genuine and cyclic padding arc. The scatter visits only the real rows. -/
theorem orderedSlotRun {V H Tag L : Type} {N J lanes d c pad base : ℕ}
    [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c)
      (subdiv : Fin 4 → ℕ)
    (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (laneOrder : L ≃ Fin lanes)
    (layout : Bool) (hc : 2 ≤ c) (g : Fin 8 → Word w) (p : Fin 3 → Word w) (mem : Memory w) :
    let sites := N*(J*lanes)
    let deg := survivingDegree d c subdiv + pad
    let D := slotDirectory P subdiv vertices tags laneOrder layout (pad := pad)
    let G := (Slots.keyCount N J d c subdiv * lanes)*2
    let H₀ := (sites*pad)*2
    let A := Slots.RecordCount N J lanes d c pad subdiv * 2
    let B := sites*2
    let rows := base+A+(B+A)
    let inverse := rows+(B+A)*deg
    let U := 4*d*(2^c*d)*(∑ t, subdiv t)
    ∀ (_ : OwnerInput D g p mem base G H₀), 0 < deg → deg < 2^w → inverse+A < 2^w →
      (∀ u : Word w, u.val < B+A → mem (base+A+u.val) = 0) →
      ∃ gs ds fs ss,
        let m₁ := after mem (eventLog gs)
        let m₂ := after m₁ (eventLog ds)
        let m₃ := after m₂ (eventLog fs)
        let all := gs ++ ds ++ fs ++ ss
        runSegment ((template SlotOwners.genuine 0).instantiate w g).program 49 (some 0) mem
            (List.replicate G []) = some gs ∧
        runSegment ((template SlotOwners.dummy 0).instantiate w p).program 20 (some 0) m₁
            (List.replicate H₀ []) = some ds ∧
        runSegment ((template collectPreimage 3).instantiate w (parameters w base A B deg)).program
            23 (some 0) m₂ (List.replicate A []) = some fs ∧
        runSegment ((template SlotScatter.visit 0).instantiate w
          (scatterParameters w base A B deg)).program
            10 (some 0) m₃ (List.replicate (B*deg) []) = some ss ∧
        Tables D deg rows inverse (slotDirectory_degree P subdiv vertices tags laneOrder hc layout)
          (after m₃ (eventLog ss)) ∧
        all.length = sites * (4*(U+pad)+2*deg) ∧
        RAMBuckets.cost Report.probes all = sites * (22*U+16*pad+6*deg) ∧
        (all.map fun r ↦ r.events.length+1).sum = sites * (144*U+86*pad+20*deg) ∧
        ∀ r ∈ all, r.events.length+1 ≤ 49 := by
  intro sites deg D G H₀ A B rows inverse U input hdeg hdw hfit zero
  obtain ⟨gs,ds,fs,ss,hg,hd,hf,hs,ht,_,_,_,_,_,cost,wg,wd,wf,ws⟩ :=
    SlotSchedule.run D g p mem input hdeg hdw
      (slotDirectory_degree P subdiv vertices tags laneOrder hc layout) hfit zero
  have ng : gs.length = G := (run_length hg).trans (List.length_replicate ..)
  have nd : ds.length = H₀ := (run_length hd).trans (List.length_replicate ..)
  have nf : fs.length = A := (run_length hf).trans (List.length_replicate ..)
  have ns : ss.length = B*deg := (run_length hs).trans (List.length_replicate ..)
  have hG : G = sites*(2*U) := by dsimp [G, sites, U, Slots.keyCount]; ring
  have hH : H₀ = sites*(2*pad) := by dsimp [H₀]; ring
  have hA : A = sites*(2*(U+pad)) := by dsimp [A,sites,U,Slots.RecordCount,Slots.keyCount]; ring
  refine ⟨gs,ds,fs,ss,hg,hd,hf,hs,ht,?_,?_,?_,?_⟩
  · simp only [List.length_append, ng, nd, nf, ns, hG, hH, hA, B]
    ring
  · change RAMBuckets.cost Report.probes _ = _ at cost
    rw [cost]
    change 6*G+3*H₀+5*A+3*(B*deg) = _
    rw [hG,hH,hA]
    dsimp [B]; ring
  · simp only [List.map_append,List.sum_append]
    rw [instruction_total gs 49 (fun r h ↦ by rw [wg r h]),
      instruction_total ds 20 (fun r h ↦ by rw [wd r h]),
      instruction_total fs 23 (fun r h ↦ by rw [wf r h]),
      instruction_total ss 10 (fun r h ↦ by rw [ws r h]), ng, nd, nf, ns, hG, hH, hA]
    dsimp [B]; ring
  · intro r hr
    simp only [List.mem_append] at hr
    rcases hr with ((h|h)|h)|h
    · rw [wg r h]
    · rw [wd r h]; decide
    · rw [wf r h]; decide
    · rw [ws r h]; decide

/-- Accumulate the event counts of each successful call, including guarded workers
which reject invalid addresses. -/
private theorem checked_scan {C : Type*} {P : BurstRAM.Program w C} {fuel steps probes ticks : ℕ}
    (one : ∀ m i r, execute P fuel (P.start i) m [] = some r →
      r.events.length = ticks ∧ r.probes = probes)
    {s : Option (Word w)} {m : Memory w} {rs : List (Report w)}
    (hr : runSegment P fuel s m (List.replicate steps []) = some rs) :
    rs.length = steps ∧ RAMBuckets.cost Report.probes rs = (1+probes)*steps ∧
      (rs.map fun r ↦ r.events.length+1).sum = (ticks+1)*steps ∧
      ∀ r ∈ rs, r.events.length = ticks := by
  induction steps generalizing s m rs with
  | zero =>
    have h : rs = [] := by simpa [runSegment] using hr.symm
    simp [h]
  | succ n ih =>
    cases s with
    | none => simp [List.replicate_succ, runSegment] at hr
    | some s =>
      rw [List.replicate_succ, runSegment] at hr
      cases h : execute P fuel (P.start s) m [] with
      | none => rw [h] at hr; contradiction
      | some r =>
        rw [h] at hr
        obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨hl, hc, hi, hh⟩ := ih htail
        obtain ⟨ht, hp⟩ := one _ _ _ h
        refine ⟨by simp [hl], ?_, ?_, fun rep h ↦ ?_⟩
        · rw [RAMBuckets.cost, hp, hc, Nat.mul_succ]; omega
        · rw [List.map_cons, List.sum_cons, ht, hi, Nat.mul_succ]; omega
        · rcases List.mem_cons.mp h with rfl | h
          · exact ht
          · exact hh _ h

/-- Raw report statistics of a deterministic worker with fixed per-call counts. -/
theorem fixedScanCounts {C : Type*} {P : BurstRAM.Program w C} {fuel steps probes ticks : ℕ}
    (ev : Memory w → Word w → List (Event w))
    (hn : ∀ m i, execute P fuel (P.start i) m [] = some ⟨ev m i, some (i + 1)⟩)
    (he : ∀ m i, (ev m i).length = ticks ∧ countProbes (ev m i) = probes)
    {s : Word w} {m : Memory w} {rs : List (Report w)}
    (hr : runSegment P fuel (some s) m (List.replicate steps []) = some rs) :
    rs.length = steps ∧ RAMBuckets.cost Report.probes rs = (1+probes)*steps ∧
      (rs.map fun r ↦ r.events.length+1).sum = (ticks+1)*steps ∧
      ∀ r ∈ rs, r.events.length = ticks := by
  apply checked_scan _ hr
  intro mem i r h
  rw [hn mem i] at h
  cases h
  exact he mem i

open PrimedStackRAM in
private theorem preimage_scan_cost {p : Fin 6 → Word w} {m : Memory w} {steps : ℕ}
    {rs : List (Report w)}
    (hr : runSegment ((template collectPreimage 3).instantiate w p).program 23
      (some 0) m (List.replicate steps []) = some rs) :
    RAMBuckets.cost Report.probes rs = 5*steps := by
  refine (checked_scan (probes := 4) (ticks := 22) ?_ hr).2.1
  intro mem i rep he
  by_cases h : i < p 0 ∧ ownerAt p mem i < p 2 ∧ mem (countAt p (ownerAt p mem i)).val < p 4
  · rw [collectPreimage_native p mem i h.1 h.2.1 h.2.2] at he
    cases he
    exact collectEvents_work p mem i
  · change execute ((template collectPreimage 3).instantiate w p).program (1+collectPreimage.length)
      ⟨_, i, fun _ ↦ 0, fun _ ↦ 0⟩ mem [] = _ at he
    rw [execute_template, run_eq_trace, collectPreimage_invalid p i _ mem h] at he
    cases he

open PortRefresh.NewSlots in
/-- Instructions of a refreshed incidence worker, including its return. -/
def refreshSlotInstructions : Kind → ℕ
  | .external => 22
  | .expander => 46
  | .padding => 36

open PortRefresh PortRefresh.NewSlots in
/-- Raw costs of successive physical incidence-column scans. -/
theorem refreshWrites {d sites : ℕ} (kind : Fin d → Kind) (pub : Fin d → Public w)
    {ks : List (Fin d)} {m : Memory w} {rs : List (Report w)}
    (runs : AllSlots.Runs kind pub sites ks m rs) :
    rs.length = ks.length*sites ∧
      RAMBuckets.cost Report.probes rs = (ks.map fun k ↦ (1+probeCount (kind k))*sites).sum ∧
      (rs.map fun r ↦ r.events.length+1).sum =
        (ks.map fun k ↦ refreshSlotInstructions (kind k)*sites).sum ∧
      ∀ r ∈ rs, r.events.length+1 ≤ 46 := by
  induction runs with
  | nil => simp
  | cons k head tail ih =>
    have one := fixedScanCounts (events (kind k) (pub k)) (native (kind k) (pub k))
      (events_work (kind k) (pub k)) head
    obtain ⟨hn,hc,hi,hcap⟩ := one
    have cost := ih.2.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.length_append, hn, ih.1, List.length_cons, Nat.succ_mul]; omega
    · rw [RAMBuckets.cost_append, hc, cost, List.map_cons, List.sum_cons]
      cases kind k <;> rfl
    · rw [List.map_append, List.sum_append, hi, ih.2.2.1, List.map_cons, List.sum_cons]
      cases kind k <;> rfl
    · intro r hr
      rcases List.mem_append.mp hr with h | h
      · rw [hcap _ h]
        cases kind k <;> decide
      · exact ih.2.2.2 _ h

open PortRefresh.NewSlots Compression.DegreeRefresh in
private theorem slot_instruction_sum {dH outDegree : ℕ} (hd : dH + 1 ≤ outDegree) (sites : ℕ) :
    ∑ k : Fin outDegree, refreshSlotInstructions (kindOf ((refreshSlots hd).symm k))*sites =
      (22+46*dH+36*(outDegree-(dH+1)))*sites := by
  rw [← (refreshSlots hd).sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, kindOf, refreshSlotInstructions,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  ring

open PortRefresh PortRefresh.NewSlots Compression.DegreeRefresh PrimedStackRAM in
/-- The three external refresh passes followed by all actual incidence writebacks.
These totals apply to the chronologically joined report lists from `external_phases` and
`all_slots`, for any selected expander supplies and any widths. -/
theorem refreshPhaseCounts {sites degree dH outDegree : ℕ} (hd : dH + 1 ≤ outDegree)
    (g : Fin 4 → Word w) (b e : Fin 8 → Word w) (out : Fin outDegree → Public w)
    (m : Memory w) (gs ds es os : List (Report w))
    (hg : runSegment ((template RefreshGather.gather 0).instantiate w g).program 24 (some 0) m
      (List.replicate (sites * degree) []) = some gs)
    (hb : runSegment ((template BundleDirectory.visit 0).instantiate w b).program 28 (some 0)
      (after m (eventLog gs)) (List.replicate sites []) = some ds)
    (he : runSegment ((template RefreshRAM.visit 0).instantiate w e).program 33 (some 0)
      (after (after m (eventLog gs)) (eventLog ds)) (List.replicate (sites * degree) []) = some es)
    (ho : AllSlots.Runs (fun k ↦ kindOf ((refreshSlots hd).symm k)) out sites
      (List.finRange outDegree) (after (after (after m (eventLog gs)) (eventLog ds))
        (eventLog es)) os) :
    let all := gs ++ ds ++ es ++ os
    let pad := outDegree-(dH+1)
    all.length = sites*(2*degree+1+outDegree) ∧
      RAMBuckets.cost Report.probes all = sites*(12*degree + 12 + 7*dH + 4*pad) ∧
      (all.map fun r ↦ r.events.length+1).sum = sites*(57*degree + 50 + 46*dH + 36*pad) ∧
      ∀ r ∈ all, r.events.length+1 ≤ 46 := by
  intro all pad
  have rg := fixedScanCounts (RefreshGather.events g) (RefreshGather.gather_native g)
    (RefreshGather.gather_work g) hg
  have rd := fixedScanCounts (BundleDirectory.events b) (BundleDirectory.visit_native b)
    (BundleDirectory.events_work b) hb
  have re := fixedScanCounts (RefreshRAM.events e) (RefreshRAM.visit_native e)
    (RefreshRAM.events_work e) he
  have ro := refreshWrites _ _ ho
  have workO : RAMBuckets.cost Report.probes os = (6+7*dH+4*pad)*sites := by
    rw [ro.2.1, ← List.ofFn_id, List.map_ofFn, List.sum_ofFn]
    exact slot_cost hd sites
  have ticksO : (os.map fun r ↦ r.events.length+1).sum = (22+46*dH+36*pad)*sites := by
    rw [ro.2.2.1, ← List.ofFn_id, List.map_ofFn, List.sum_ofFn]
    exact slot_instruction_sum hd sites
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [all, List.length_append, rg.1, rd.1, re.1, ro.1, List.length_finRange]; ring
  · simp only [all, RAMBuckets.cost_append, rg.2.1, rd.2.1, re.2.1, workO]; ring
  · simp only [all, List.map_append, List.sum_append, rg.2.2.1, rd.2.2.1, re.2.2.1, ticksO]; ring
  · intro r hr
    simp only [all, List.mem_append] at hr
    rcases hr with ((h|h)|h)|h
    · rw [rg.2.2.2 _ h]; decide
    · rw [rd.2.2.2 _ h]; decide
    · rw [re.2.2.2 _ h]; decide
    · exact ro.2.2.2 _ h

/-- The two preparation scans write the selected role offsets and the cyclic successor of
every packed site. The four subdivision constants belong to the fixed input template. -/
theorem slotOwnerPreparation {C D : Type*} {sites : ℕ} {p : BurstRAM.Program w C}
    {q : BurstRAM.Program w D} {roleBase nextBase : Word w}
    {rv nv : ℕ → Word w} {m : Memory w} {rs ns : List (Report w)}
    (role : SlotOwners.FilledRun p 26 1 25 8 roleBase rv m rs)
    (next : SlotOwners.FilledRun q 19 1 18 sites nextBase nv (after m (eventLog rs)) ns) :
    (rs++ns).length = 8+sites ∧ RAMBuckets.cost Report.probes (rs++ns) = 16+2*sites ∧
      ((rs++ns).map fun r ↦ r.events.length+1).sum = 208+19*sites ∧
      ∀ r ∈ rs++ns, r.events.length+1 ≤ 26 := by
  refine ⟨by rw [List.length_append, role.length, next.length],
    by rw [RAMBuckets.cost_append, role.cost, next.cost], ?_, ?_⟩
  · rw [List.map_append, List.sum_append,
      instruction_total rs 26 (fun r hr ↦ by rw [(role.calls r hr).2]),
      instruction_total ns 19 (fun r hr ↦ by rw [(next.calls r hr).2]), role.length, next.length]
    ring
  · intro r hr
    rcases List.mem_append.mp hr with h | h
    · rw [(role.calls r h).2]
    · rw [(next.calls r h).2]; decide

/-- Exact charged work of all five endpoint passes from the native segment executions
alone. A successful guarded append checks its owner and capacity before its two writes. -/
theorem slotLevelExactCost {s : SlotLevel.Shape} {h : SlotLevel.Heads} {m : Memory w}
    {r : SlotLevel.Reports w} (native : r.Native s h m) :
    RAMBuckets.cost Report.probes r.all =
      6*SlotLevel.genuineCount s + 3*SlotLevel.dummyCount s + 5*SlotLevel.fields s +
        3*(SlotLevel.owners s*s.newDegree) + 5*SlotLevel.baseArcs s := by
  obtain ⟨rg, rd, rf, ri, rb⟩ := native
  have g := fixedScanCounts _ (SlotOwners.genuine_native _) (SlotOwners.genuine_work _) rg
  have d := fixedScanCounts _ (SlotOwners.dummy_native _) (SlotOwners.dummy_work _) rd
  have f := preimage_scan_cost rf
  let ip := SlotLevel.bank s h w .invertFields
  have i := fixedScanCounts (probes := 2) (ticks := 9)
    (fun mem x ↦ SlotScatter.events ip x (mem (ip 0+x).val)) (SlotScatter.visit_native ip)
    (fun _ _ ↦ ⟨rfl,rfl⟩) ri
  have b := fixedScanCounts _ (SlotBaseScan.native _)
    (fun mem x ↦ (SlotBaseScan.events_work _ mem x).symm) rb
  simp only [SlotLevel.Reports.all, RAMBuckets.cost_append, g.2.1, d.2.1, f, i.2.1, b.2.1]

/-- The five selected slot passes from `SlotLevel.run_selected`, including the lane-zero
base matching writeback. All counts and the highest allocated address are linear in the
number of packed sites, independently of the wire widths. -/
theorem slotLevelBounds (s : SlotLevel.Shape) (h : SlotLevel.Heads) (m : Memory w)
    (r : SlotLevel.Reports w) (hnative : r.Native s h m) (hlanes : 1 ≤ s.lanes)
    (hwork : RAMBuckets.cost Report.probes r.all =
      6 * SlotLevel.genuineCount s + 3 * SlotLevel.dummyCount s + 5 * SlotLevel.fields s +
      3 * (SlotLevel.owners s * s.newDegree) + 5 * SlotLevel.baseArcs s) :
    let P := SlotLevel.sites s
    let pad := SlotLevel.pad s
    let U := 4*s.oldDegree*(2^s.colors*s.oldDegree)*(∑ t, s.subdivisions t)
    r.all.length ≤ P*(4*(U+pad) + 3*s.newDegree) ∧
      RAMBuckets.cost Report.probes r.all ≤ P*(22*U+16*pad+11*s.newDegree) ∧
      (∀ rep ∈ r.all, rep.events.length+1 ≤ 49) ∧
      SlotLevel.stopAddress s h ≤ h.scratch +
        P*(6*(U+pad) + 2 + (4+2*(U+pad))*s.newDegree) := by
  intro P pad U
  have hn : s.bases*s.tags ≤ P := by
    change _ ≤ s.bases*(s.tags*s.lanes)
    rw [← Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ hlanes
  have hg : SlotLevel.genuineCount s = P*(2*U) := by
    dsimp [SlotLevel.genuineCount, P, SlotLevel.sites, U, Slots.keyCount]; ring
  have hd : SlotLevel.dummyCount s = P*(2*pad) := by
    dsimp [SlotLevel.dummyCount, P, pad]; ring
  have hf : SlotLevel.fields s = P*(2*(U+pad)) := by
    rw [← SlotLevel.counts_add, hg, hd]; ring
  have ho : SlotLevel.owners s = 2*P := Nat.mul_comm ..
  have hb : SlotLevel.baseArcs s ≤ P*s.newDegree := Nat.mul_le_mul_right _ hn
  obtain ⟨rg,rd,rf,ri,rb⟩ := hnative
  have lens := fun {C : Type} {p : BurstRAM.Program w C} {fuel st mem n} {rs : List (Report w)}
    (hr : runSegment p fuel st mem (List.replicate n []) = some rs) ↦
    (run_length hr).trans (List.length_replicate ..)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [SlotLevel.Reports.all, List.length_append, lens rg, lens rd, lens rf, lens ri,
      lens rb,
      hg, hd, hf, ho]
    linarith only [hb]
  · rw [hwork,hg,hd,hf,ho]
    linarith only [hb]
  · intro rep hr
    simp only [SlotLevel.Reports.all,List.mem_append] at hr
    rcases hr with (((hh|hh)|hh)|hh)|hh
    · exact run_cap rg _ hh
    · exact (run_cap rd _ hh).trans (by decide)
    · exact (run_cap rf _ hh).trans (by decide)
    · exact (run_cap ri _ hh).trans (by decide)
    · exact (run_cap rb _ hh).trans (by decide)
  · dsimp only [SlotLevel.stopAddress, SlotLevel.shiftsHead, SlotLevel.targetsHead,
      SlotLevel.inverseHead, SlotLevel.rowsHead]
    rw [hf, ho]; linarith only [hb]

/-- Gathering one complete classified row and ranking each of its actual pivots. The result
includes each rank call's input memory, returned rank, and write to its physical destination.
For a thick row use `2^c*d/4` pivots. For a motif row use `pieceCount d c`. -/
theorem gatheredRankCosts {row arcs widthBase : ℕ} (g : Fin 3 → Word w) (m : Memory w)
    (gs : List (Report w)) (hg : BundleGather.Gathered g row arcs widthBase m gs)
    (pub : Fin row → Fin 2 → Word w) (mem : Fin row → Memory w)
    (pivot rank : Fin row → Word w) (h : ∀ i, BundleRank.RankWrite row (pub i) (mem i)
      (pivot i) (rank i)) :
    ∃ log : Fin row → List (Event w),
      (∀ i, Slots.rankExecution row (pub i) (pivot i) (mem i) (log i) (rank i) ∧
        after (mem i) (log i) = writeMemory (mem i) (pub i 1) (rank i)) ∧
      gs.length + row = 2*row ∧
      RAMBuckets.cost Report.probes gs + ∑ i, (1+countProbes (log i)) = row*(row+6) ∧
      (gs.map fun r ↦ r.events.length+1).sum + ∑ i, ((log i).length+1) = row*(6*row+19) ∧
      ∀ i, (log i).length+1 = 6*row+6 := by
  classical
  choose log hex hwrite hp ht using h
  refine ⟨log, fun i ↦ ⟨hex i,hwrite i⟩, by rw [hg.run.length]; omega, ?_, ?_, ht⟩
  · simp only [hg.run.cost, hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
    ring
  · rw [instruction_total gs 13 (fun r h ↦ by rw [(hg.run.calls r h).2]), hg.run.length]
    simp only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    ring

/-- The concrete input and gather trace for one row of thick-wire or motif keys. The rank
entry points use the physical source, destination, pivot and input memory of each call. -/
structure RankInput (w row : ℕ) where
  /-- Public heads of the ID row, absolute key column, and output key row used by the gather
  worker. -/
  gatherBank : Fin 3 → Word w
  /-- Number of absolute old arc widths covered by the gather's preservation guarantee. -/
  arcCount : ℕ
  /-- Start of the old arc width column retained during key gathering. -/
  widthBase : ℕ
  /-- Memory containing the collected arc IDs and their keys at the start of the gather scan. -/
  initial : Memory w
  /-- Reports of the native calls that materialize one row of keys from its absolute arc IDs. -/
  gatherLog : List (Report w)
  gathered : BundleGather.Gathered gatherBank row arcCount widthBase initial gatherLog
  /-- Key-row base and rank destination supplied to each pivot's ranking call. -/
  rankBank : Fin row → Fin 2 → Word w
  /-- External memory supplied at the entry to each pivot's ranking call. -/
  memory : Fin row → Memory w
  /-- Comparison key supplied to the ranking worker for each row entry. -/
  pivot : Fin row → Word w
  /-- Rank word to be written for each pivot, counting the row keys strictly below it. -/
  rank : Fin row → Word w
  checked : ∀ i, BundleRank.RankWrite row (rankBank i) (memory i) (pivot i) (rank i)

/-- Actual gather and rank traffic for this row. -/
def RankInput.traffic {n : ℕ} (job : RankInput w n) (log : Fin n → List (Event w)) : ℕ :=
  RAMBuckets.cost Report.probes job.gatherLog + ∑ i, (1+countProbes (log i))

/-- Each proposed event log executes the corresponding rank call, leaves the specified rank at
its destination, and has the exact instruction count. -/
def RankInput.realizes {n : ℕ} (job : RankInput w n) (log : Fin n → List (Event w)) : Prop :=
  ∀ i, Slots.rankExecution n (job.rankBank i) (job.pivot i) (job.memory i) (log i) (job.rank i) ∧
    after (job.memory i) (log i) = writeMemory (job.memory i) (job.rankBank i 1) (job.rank i) ∧
    (log i).length+1 = 6*n+6

theorem RankInput.gather_instruction_count {n : ℕ} (job : RankInput w n) (r : Report w)
    (hr : r ∈ job.gatherLog) : r.events.length+1 = 13 := by rw [(job.gathered.run.calls r hr).2]

private theorem RankInput.logs {n : ℕ} (job : RankInput w n) :
    ∃ log, job.realizes log ∧ job.traffic log = n*(n+6) := by
  obtain ⟨log, h, _, hc, _, ticks⟩ := gatheredRankCosts job.gatherBank job.initial
    job.gatherLog job.gathered
    job.rankBank job.memory job.pivot job.rank job.checked
  exact ⟨log, fun i ↦ ⟨(h i).1,(h i).2,ticks i⟩, hc⟩

/-- One packed shrinking stage's native local row traffic. There is one thick and one
motif key row per outgoing port, one demand slice pass per bundle, and one subdivision
slice pass per role edge of each actual motif. -/
theorem shrinkLocalTraffic {V H Tag L : Type} {d c : ℕ}
    [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [DecidableEq V] [DecidableEq Tag]
      [DecidableEq L]
    (P : PackingData V H Tag L d c) (hc : 2 ≤ c)
    (number : P.BundleNumbering) (order : P.ThickNumbering) (width : Arc V H Tag L d c → ℕ)
    (subdiv : Fin 4 → ℕ) (roleWidth : Fin 4 × P.Motif → ℕ)
    (thickJob : Site V Tag L × Fin d → RankInput w (2 ^ c * d / 4))
    (motifJob : Site V Tag L × Fin d → RankInput w (PackingData.pieceCount d c)) :
    let H₀ := 2^c*d/4
    let Q := PackingData.pieceCount d c
    let S := ∑ t, subdiv t
    let old := fun b ↦ orderedWidths (order b) (fun s ↦ width s.1.1)
    let new := fun b ↦ orderedWidths (number b) (fun t ↦ P.abWidth number width t.1)
    let divided := fun (i : Fin 4 × P.Motif) ↦ List.ofFn (splitWidth (roleWidth i) (subdiv i.1))
    ∀ (input : ∀ b, SliceInput w (old b) (new b))
      (split : ∀ i, SliceInput w [roleWidth i] (divided i)),
      ∃ (thickLog : Site V Tag L × Fin d → Fin H₀ → List (Event w))
        (motifLog : Site V Tag L × Fin d → Fin Q → List (Event w))
          (demand : Site V Tag L × Fin d → SliceSchedule.Passes w)
        (roles : Fin 4 × P.Motif → SliceSchedule.Passes w),
        (∀ b, (thickJob b).realizes (thickLog b) ∧ (motifJob b).realizes (motifLog b)) ∧
        (∀ b, (input b).produces (demand b) ∧ ∀ r ∈ (demand b).all, r.events.length+1 ≤ 38) ∧
        (∀ i, (split i).produces (roles i) ∧ ∀ r ∈ (roles i).all, r.events.length+1 ≤ 38) ∧
        (∑ b, (thickJob b).traffic (thickLog b)) + (∑ b, (motifJob b).traffic (motifLog b)) +
          (∑ b, RAMBuckets.cost Report.probes (demand b).all) +
          (∑ i, RAMBuckets.cost Report.probes (roles i).all) ≤
        Fintype.card (Site V Tag L) * (d*(H₀*(H₀+6) + Q*(Q+6) + 4 + 7*(H₀+Q) + 16*(H₀*Q) +
          4*Q*(4+7*(1+S)+16*S))) := by
  classical
  intro H₀ Q S old new divided input split
  choose tl ht ct using fun b ↦ (thickJob b).logs
  choose ml hm cm using fun b ↦ (motifJob b).logs
  obtain ⟨ds, hs, hdCap, _, cs, _⟩ := demandSliceCosts P number order width input
  obtain ⟨rs, hr, hrCap, _, cr, _⟩ := subdivisionSliceCosts roleWidth subdiv Prod.fst split
  have countM : Fintype.card P.Motif = Fintype.card (Site V Tag L) * d * Q := by
    rw [Fintype.card_congr (Equiv.sigmaFiberEquiv P.bundle).symm, Fintype.card_sigma]
    simp only [P.card_motifs_bundle hc, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Nat.nsmul_eq_mul, Q, PackingData.pieceCount]
  refine ⟨tl,ml,ds,rs,fun b ↦ ⟨ht b,hm b⟩,fun b ↦ ⟨hs b,hdCap b⟩,fun i ↦ ⟨hr i,hrCap i⟩,?_⟩
  simp only [ct,cm,Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Nat.nsmul_eq_mul]
  simp only [Fintype.card_prod,Fintype.card_fin,countM] at cs cr
  dsimp only [H₀,Q,S] at cs cr ⊢
  linarith only [cs, cr]

/-- A concrete input memory and the resulting reports for a reset-cursor scan. -/
structure NativeScan {C : Type*} (P : BurstRAM.Program w C) (fuel calls : ℕ) where
  /-- External memory at the start of this worker's deterministic scan from cursor zero. -/
  initial : Memory w
  /-- Reports returned by executing the specified number of scan calls, each with an empty
  choice stream. -/
  reports : List (Report w)
  executed : runSegment P fuel (some 0) initial (List.replicate calls []) = some reports

open PrimedStackRAM in
/-- The placement, preimage, classification, role-record and auxiliary-table scans feeding
the selected slot workers. Each trace starts from the memory at its actual entry point. -/
structure ShrinkScans (w : ℕ) (s : SlotLevel.Shape) where
  /-- Public parameters for computing placement owners, thickness flags, assigned ports, and
  targets at old positions. -/
  placementBank : Fin 14 → Word w
  /-- Public parameters for appending old positions to the child rows of their packed owners. -/
  preimageBank : Fin 6 → Word w
  /-- Public parameters for classifying old ports by bundle and computing their sorting keys. -/
  classifierBank : Fin 11 → Word w
  /-- Public parameters for collecting absolute old port IDs into thick-wire and motif bucket
  rows. -/
  bundleBank : Fin 6 → Word w
  /-- Public radices and table addresses for writing three role sites and a CD flag for each
  old arc. -/
  demandBank : Fin 11 → Word w
  /-- Layout selector and destination head for publishing the eight endpoint role offsets. -/
  roleBank : Fin 2 → Word w
  /-- Lane and tag counts and destination head for the cyclic site successor scan. -/
  successorBank : Fin 3 → Word w
  /-- Native scan computing a shrinking placement record for each old position. -/
  placement : NativeScan ((template ShrinkRAM.visit 0).instantiate w placementBank).program
    65 (SlotLevel.sites s*(2^s.colors*s.oldDegree))
  /-- Native scan appending each old position to the preimage row of its packed owner. -/
  preimages : NativeScan ((template collectPreimage 3).instantiate w preimageBank).program
    23 (SlotLevel.sites s*(2^s.colors*s.oldDegree))
  /-- Native scan assigning each old outgoing port a bundle bucket and a sorting key. -/
  classifier : NativeScan ((template BundleRAM.visit 0).instantiate w classifierBank).program
    (1+BundleRAM.visit.length) (SlotLevel.sites s*(2^s.colors*s.oldDegree)*s.oldDegree)
  /-- Native scan collecting the classified old port IDs into the corresponding bundle rows. -/
  bundles : NativeScan ((template collectPreimage 3).instantiate w bundleBank).program
    23 (SlotLevel.sites s*(2^s.colors*s.oldDegree)*s.oldDegree)
  /-- Native scan visiting old outgoing ports and writing each role-site and CD record at its
  absolute old arc ID. -/
  demandRoles : NativeScan ((template DemandRAM.visit 0).instantiate w demandBank).program
    65 (SlotLevel.sites s*(2^s.colors*s.oldDegree)*s.oldDegree)
  /-- The eight native calls that publish one role selector for each edge type and side. -/
  roleOffsets : NativeScan ((template SlotOwners.Aux.roleCode 0).instantiate w
    roleBank).program 26 8
  /-- Native scan computing a cyclic tag successor for each packed site. -/
  successors : NativeScan ((template SlotOwners.Aux.nextCode 0).instantiate w successorBank).program
    19 (SlotLevel.sites s)

/-- Concatenate the reports of the seven preparation scans in order for the shrinking phase's
traffic calculation. -/
def ShrinkScans.reports {s : SlotLevel.Shape} (r : ShrinkScans w s) : List (Report w) :=
  r.placement.reports ++ r.preimages.reports ++ r.classifier.reports ++ r.bundles.reports ++
    r.demandRoles.reports ++ r.roleOffsets.reports ++ r.successors.reports

/-- Combine the physical scans with the row work bounded by `shrinkLocalTraffic`. The
coefficient involves only the incoming and outgoing degrees, the color count, the
subdivision template, and the local row coefficient. -/
theorem shrinkDescriptorTraffic (s : SlotLevel.Shape) (h : SlotLevel.Heads) (m : Memory w)
    (r : SlotLevel.Reports w) (hnative : r.Native s h m) (hlanes : 1 ≤ s.lanes)
    (hnonempty : 0 < SlotLevel.sites s) (prep : ShrinkScans w s)
    (hwork : RAMBuckets.cost Report.probes r.all =
      6 * SlotLevel.genuineCount s + 3 * SlotLevel.dummyCount s + 5 * SlotLevel.fields s +
      3 * (SlotLevel.owners s * s.newDegree) + 5 * SlotLevel.baseArcs s)
    {rowWork rowFactor : ℕ} (hrows : rowWork ≤ SlotLevel.sites s * rowFactor) :
    let P := SlotLevel.sites s
    let K := 2^s.colors*s.oldDegree
    let U := 4*s.oldDegree*K*(∑ t, s.subdivisions t)
    let all := prep.reports ++ r.all
    RAMBuckets.cost Report.probes all + rowWork ≤ P *
      (14*K + 25*K*s.oldDegree + 18 + 22*U + 16*SlotLevel.pad s + 11*s.newDegree + rowFactor) ∧
    ∀ rep ∈ all, rep.events.length+1 ≤ 66 := by
  intro P K U all
  have p := fixedScanCounts _ (ShrinkRAM.visit_native prep.placementBank)
    (ShrinkRAM.visit_work prep.placementBank) prep.placement.executed
  have pre := preimage_scan_cost prep.preimages.executed
  have c := fixedScanCounts _ (BundleRAM.visit_native prep.classifierBank)
    (BundleRAM.events_work prep.classifierBank) prep.classifier.executed
  have b := preimage_scan_cost prep.bundles.executed
  have d := fixedScanCounts _ (DemandRAM.visit_native prep.demandBank)
    (DemandRAM.visit_work prep.demandBank) prep.demandRoles.executed
  have role := fixedScanCounts (probes := 1) (ticks := 25) _
    (SlotOwners.Aux.role_native prep.roleBank)
    (fun _ _ ↦ ⟨rfl,rfl⟩) prep.roleOffsets.executed
  have suc := fixedScanCounts (probes := 1) (ticks := 18) _
    (SlotOwners.Aux.next_native prep.successorBank)
    (fun _ _ ↦ ⟨rfl,rfl⟩) prep.successors.executed
  obtain ⟨_, hs, hcap, _⟩ := slotLevelBounds s h m r hnative hlanes hwork
  constructor
  · simp only [all,ShrinkScans.reports,RAMBuckets.cost_append,p.2.1,pre,c.2.1,b,d.2.1,role.2.1,
      suc.2.1]
    dsimp only [P,K,U]
    linarith only [hrows, hs, hnonempty]
  · intro rep hm
    simp only [all,ShrinkScans.reports,List.mem_append] at hm
    rcases hm with ((((((hh|hh)|hh)|hh)|hh)|hh)|hh)|hh
    · exact (run_cap prep.placement.executed _ hh).trans (by decide)
    · exact (run_cap prep.preimages.executed _ hh).trans (by decide)
    · exact (run_cap prep.classifier.executed _ hh).trans (by decide)
    · exact (run_cap prep.bundles.executed _ hh).trans (by decide)
    · exact (run_cap prep.demandRoles.executed _ hh).trans (by decide)
    · exact (run_cap prep.roleOffsets.executed _ hh).trans (by decide)
    · exact (run_cap prep.successors.executed _ hh).trans (by decide)
    · exact (hcap _ hh).trans (by decide)

/-- Coefficient for all row, slot, and slice passes counted above at one selected shrink.
It uses only the degrees, colors, and four subdivision lengths. -/
def shrinkTrafficFactor (s : SlotLevel.Shape) : ℕ :=
  let d := s.oldDegree
  let K := 2^s.colors*d
  let H := K/4
  let Q := PackingData.pieceCount d s.colors
  let S := ∑ t, s.subdivisions t
  let U := 4*d*K*S
  14*K + 25*K*d + 18 + 22*U + 16*SlotLevel.pad s + 11*s.newDegree +
    d*(H*(H+6) + Q*(Q+6) + 4 + 7*(H+Q) + 16*(H*Q) + 4*Q*(4+7*(1+S)+16*S))

/-- Total traffic for the native selected slot directory and all its checked bundle rows
and slice inputs. The numerical premises on the directory are returned by
`SlotLevel.run_selected`. The number of row invocations is proved from the selected
packing data. -/
theorem selectedShrinkTraffic {V H Tag L : Type}
    [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [DecidableEq V] [DecidableEq Tag]
      [DecidableEq L]
    (s : SlotLevel.Shape) (h : SlotLevel.Heads) (m : Memory w) (r : SlotLevel.Reports w)
    (hnative : r.Native s h m) (prep : ShrinkScans w s) (hlanes : 1 ≤ s.lanes)
    (hnonempty : 0 < SlotLevel.sites s)
    (hwork : RAMBuckets.cost Report.probes r.all =
      6 * SlotLevel.genuineCount s + 3 * SlotLevel.dummyCount s + 5 * SlotLevel.fields s +
      3 * (SlotLevel.owners s * s.newDegree) + 5 * SlotLevel.baseArcs s)
    (P : PackingData V H Tag L s.oldDegree s.colors) (hc : 2 ≤ s.colors)
    (sites : Site V Tag L ≃ Fin (SlotLevel.sites s)) (number : P.BundleNumbering)
    (order : P.ThickNumbering) (width : Arc V H Tag L s.oldDegree s.colors → ℕ)
    (roleWidth : Fin 4 × P.Motif → ℕ)
    (thickJob : Site V Tag L × Fin s.oldDegree → RankInput w (2 ^ s.colors * s.oldDegree / 4))
    (motifJob : Site V Tag L × Fin s.oldDegree → RankInput w
      (PackingData.pieceCount s.oldDegree s.colors)) :
    let old := fun b ↦ orderedWidths (order b) (fun x ↦ width x.1.1)
    let new := fun b ↦ orderedWidths (number b) (fun x ↦ P.abWidth number width x.1)
    let divided := fun (i : Fin 4 × P.Motif) ↦ List.ofFn (splitWidth (roleWidth i)
      (s.subdivisions i.1))
    ∀ (input : ∀ b, SliceInput w (old b) (new b)) (split : ∀ i, SliceInput w [roleWidth i]
      (divided i)),
      ∃ (tl : Site V Tag L × Fin s.oldDegree → Fin (2^s.colors*s.oldDegree/4) → List (Event w))
        (ml : Site V Tag L × Fin s.oldDegree → Fin (PackingData.pieceCount s.oldDegree
          s.colors) → List (Event w))
        (ds : Site V Tag L × Fin s.oldDegree → SliceSchedule.Passes w) (rs : Fin 4 × P.Motif →
          SliceSchedule.Passes w),
        (∀ b, (thickJob b).realizes (tl b) ∧ (motifJob b).realizes (ml b)) ∧
        (∀ b, (input b).produces (ds b)) ∧ (∀ i, (split i).produces (rs i)) ∧
        RAMBuckets.cost Report.probes (prep.reports++r.all) +
          ((∑ b, (thickJob b).traffic (tl b)) + (∑ b, (motifJob b).traffic (ml b)) +
          (∑ b, RAMBuckets.cost Report.probes (ds b).all) + (∑ i, RAMBuckets.cost Report.probes
            (rs i).all)) ≤
          SlotLevel.sites s * shrinkTrafficFactor s := by
  intro old new divided input split
  obtain ⟨tl,ml,ds,rs,hrank,hd,hs,hlocal⟩ :=
    shrinkLocalTraffic P hc number order width s.subdivisions roleWidth thickJob motifJob input
      split
  rw [Fintype.card_congr sites, Fintype.card_fin] at hlocal
  exact ⟨tl,ml,ds,rs,hrank,fun b ↦ (hd b).1,fun i ↦ (hs i).1,
    (shrinkDescriptorTraffic s h m r hnative hlanes hnonempty prep hwork hlocal).1⟩

end CompressorRecords.PhaseCosts

end VPVNP
end Computability
end OAI
