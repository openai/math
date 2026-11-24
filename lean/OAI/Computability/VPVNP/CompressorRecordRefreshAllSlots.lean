import OAI.Computability.VPVNP.CompressorRecordRefreshNewSlots
import OAI.Computability.VPVNP.CompressorRecordIncidenceLayout
import OAI.Computability.VPVNP.DegreeRefreshPass

/-!
# All actual incidence columns of a degree refresh

In increasing local-slot order, each native table visits all the new sites.
The scans share external memory. The incoming link is indexed by the target
half-slot, which can have a different local number on an expander arc.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.AllSlots

open BurstRAM PrimedStackRAM NewSlots
open Compression Compression.Refresh Compression.DegreeRefresh

variable {bits d N : ℕ}

section Sequence

variable (kind : Fin d → Kind) (pub : Fin d → Public bits)

/-- The expected incidence row for one local slot and site, computed from the reference memory
and that slot's public operands. -/
abbrev entry (ref : Memory bits) (k : Fin d) (i : Fin N) : Row bits :=
  expected (kind k) (pub k) ref i

/-- Native executions of consecutive slot scans. Each scan starts at site zero
with the actual external memory left by its predecessor. -/
inductive Runs (N : ℕ) : List (Fin d) → Memory bits → List (Report bits) → Prop where
  | nil (m) : Runs N [] m []
  | cons (k : Fin d) {ks m rs ts}
      (head : let M := (template (code (kind k)) 0).instantiate bits (pub k)
        runSegment M.program (1 + (code (kind k)).length) (some 0) m (List.replicate N []) = some rs)
      (tail : Runs N ks (after m (eventLog rs)) ts) : Runs N (k :: ks) m (rs ++ ts)

/-- The slot scans have disjoint inputs and outputs, and each output address identifies its
slot, site, and column uniquely. -/
structure Layout (ref : Memory bits) (N : ℕ) : Prop where
  reads : ∀ k j (i l : Fin N) c a, a ∈ inputs (kind k) (pub k) (word i.val) →
    a ≠ (entry kind pub ref j l).address (pub j) c
  writes : ∀ k j (i l : Fin N) c b,
    (entry kind pub ref k i).address (pub k) c = (entry kind pub ref j l).address (pub j) b →
      k = j ∧ i = l ∧ c = b

variable (ref : Memory bits)

/-- The memory agrees with the immutable input tables of every scan. -/
def Reads (m : Memory bits) (N : ℕ) : Prop :=
  ∀ k (i : Fin N) a, a ∈ inputs (kind k) (pub k) (word i.val) → m a.val = ref a.val

private theorem sameEntry {m : Memory bits} (h : Reads kind pub ref m N) (k : Fin d) (i : Fin N) :
    entry kind pub m k i = entry kind pub ref k i := by
  have ha := h k i
  change row (kind k) (pub k) m (word i.val) = row (kind k) (pub k) ref (word i.val)
  generalize hb : word (bits := bits) i.val = b at ha ⊢
  cases hk : kind k <;> simp [hk,inputs] at ha
  · simp only [row,ha.1,ha.2]
  · simp only [row,ha.1,ha.2.1,ha.2.2]
  · rfl

/-- Rows and frame of the visits for the listed slots. -/
structure Completed (initial final : Memory bits) (ks : List (Fin d)) (N : ℕ) : Prop where
  rows : ∀ k ∈ ks, ∀ (i : Fin N) c,
    final ((entry kind pub ref k i).address (pub k) c).val = (entry kind pub ref k i).value c
  frame : ∀ a, (∀ k ∈ ks, ∀ (i : Fin N) c, a ≠ ((entry kind pub ref k i).address (pub k) c).val) →
    final a = initial a

/-- Any list of local-slot passes, including repeated slots, executes against
one set of physical inputs and writes exactly the indicated rows. -/
theorem runList (layout : Layout kind pub ref N) (ks : List (Fin d)) (m : Memory bits)
    (read : Reads kind pub ref m N) :
    ∃ rs, Runs kind pub N ks m rs ∧ Completed kind pub ref m (after m (eventLog rs)) ks N ∧
      RAMBuckets.cost Report.probes rs = (ks.map fun k => (1 + probeCount (kind k)) * N).sum := by
  induction ks generalizing m with
  | nil => exact ⟨[], .nil _, ⟨by simp, fun _ _ => rfl⟩, rfl⟩
  | cons k ks ih =>
    have same := sameEntry kind pub ref read
    have localLayout : PassLayout (kind k) (pub k) m N :=
      ⟨fun i j c a ha he => layout.reads k k i j c a ha (he.trans (congrArg (fun s : Row bits =>
        s.address (pub k) c) (same k j))),
       fun i j c b he => (layout.writes k k i j c b (by
        change (entry kind pub m k i).address (pub k) c = (entry kind pub m k j).address (pub k) b at he
        rwa [same,same] at he)).2⟩
    obtain ⟨rs,hr,hpre,_,cost⟩ := full_pass (kind k) (pub k) m localLayout
    let next := after m (eventLog rs)
    have frame (a : ℕ) (miss : ∀ (i : Fin N) c, a ≠ ((entry kind pub ref k i).address (pub k) c).val) :
        next a = m a := by
      apply hpre.frame
      intro i _ c
      change a ≠ ((entry kind pub m k i).address (pub k) c).val
      rw [same]
      exact miss i c
    have readNext : Reads kind pub ref next N := fun j i a ha =>
      (frame a.val (fun l c eq => layout.reads j k i l c a ha (Fin.ext eq))).trans (read j i a ha)
    obtain ⟨ts,ht,hcs,hct⟩ := ih next readNext
    have append : after m (eventLog (rs ++ ts)) = after next (eventLog ts) := by
      change List.foldl BurstRAM.update m ((rs ++ ts).flatMap Report.events) = _
      rw [List.flatMap_append,List.foldl_append]
      rfl
    refine ⟨rs ++ ts, .cons k hr ht, ?_, ?_⟩
    · rw [append]
      constructor
      · intro j hj i c
        by_cases used : j ∈ ks
        · exact hcs.rows j used i c
        have eq := (List.mem_cons.mp hj).resolve_right used
        subst j
        rw [hcs.frame _ (fun l hl t b he => used ((layout.writes k l i t c b (Fin.ext he)).1 ▸ hl))]
        have stored := hpre.rows i i.isLt c
        change next ((entry kind pub m k i).address (pub k) c).val = (entry kind pub m k i).value c at stored
        rwa [same] at stored
      · intro a miss
        rw [hcs.frame a (fun l hl => miss l (List.mem_cons_of_mem _ hl))]
        exact frame a (miss k List.mem_cons_self)
    · rw [RAMBuckets.cost_append,hct]
      change RAMBuckets.cost Report.probes rs = _ at cost
      simp [cost]

end Sequence

/-- Addresses of the five read-only tables used to write all refreshed arcs. -/
structure Tables (bits : ℕ) where
  /-- Base address of the table mapping each external bundle to its destination. -/
  target : W bits
  /-- Base address of the total width of each external bundle. -/
  total : W bits
  /-- Base address of the expander destination-port table, indexed by source port and local
  expander slot. -/
  targetPort : W bits
  /-- Base address of the corresponding reverse expander slot numbers at the destination ports. -/
  reverseSlot : W bits
  /-- Base address of the internal widths selected for each site and expander slot. -/
  supply : W bits

private def localCopy {dH d₀ : ℕ} : RefreshSlot dH d₀ → ℕ
  | .inl _ => 0
  | .inr (.inl k) => k.val
  | .inr (.inr k) => k.val

/-- The physical output arrays are those of the incidence-directory interface. -/
def words {dH d₀ : ℕ} (D r : ℕ) (I : Tables bits) (T : IncidenceDirectory bits)
    (c : RefreshSlot dH d₀) : Public bits :=
  ![word D, word dH, word d₀, word r, word (localCopy c), I.target, I.total,
    I.targetPort, I.reverseSlot, I.supply, T.actualOut, T.actualIn, T.width]

/-- Select the outgoing mate, incoming mate, or width column from the actual incidence
directory. -/
def columnBase (T : IncidenceDirectory bits) : Column → W bits
  | .outgoing => T.actualOut
  | .incoming => T.actualIn
  | .width => T.width

/-- Choose the destination slot for an incoming-column write and the source slot for
outgoing-mate and width writes. -/
def rowIndex (s : Row bits) : Column → W bits
  | .outgoing | .width => s.src
  | .incoming => s.dst

private theorem address_eq {dH d₀ : ℕ} (D r : ℕ) (I : Tables bits) (T : IncidenceDirectory bits)
    (k : RefreshSlot dH d₀) (s : Row bits) (c : Column) :
    s.address (words D r I T k) c = columnBase T c + rowIndex s c := by cases c <;> rfl

/-- Every source operand lies outside the three output regions. -/
def InputsApart (T : IncidenceDirectory bits) (kind : Fin d → Kind) (pub : Fin d → Public bits) (N : ℕ) : Prop :=
  ∀ k (i : Fin N) a, a ∈ inputs (kind k) (pub k) (word i.val) →
    ∀ c (j : W bits), j.val < N*d → a ≠ columnBase T c + j

/-- A memory address outside all three output regions. -/
def Outside (T : IncidenceDirectory bits) (extent addr : ℕ) : Prop :=
  ∀ c (j : W bits), j.val < extent → addr ≠ (columnBase T c + j).val

private def columnNumber : Column → Fin 6
  | .outgoing => 3
  | .incoming => 4
  | .width => 5

private theorem columnBase_eq (T : IncidenceDirectory bits) (c : Column) :
    columnBase T c = T.column (columnNumber c) := by cases c <;> rfl

private theorem columnNumber_injective : Function.Injective columnNumber := by
  intro c d he
  cases c <;> cases d <;> first | rfl | contradiction

section Dyadic

open SpectralGeometry MotifConversion

variable {a g a₀ dH : ℕ} {K : Type*} [_root_.Field K] {c₁ c₂ : ℝ}
  (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH)
  (hdH : 0 < dH) (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock K (expanderSupply E hdH conn) (2^a₀) c₁ c₂)
  (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀) (choice : DyadicRefreshChoice X E hdH conn F)
  (I : Tables bits) (T : IncidenceDirectory bits) (ref : Memory bits)

local notation "Nₛ" => Fintype.card X.Base * 2^a * 2^g
local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)
local notation "A" => arcs (D := 2^a) (d₀ := 2^a₀) X.baseIndex (bitWordFinEquiv g)
local notation "Y" => dyadicRefreshNext X E hdH conn F hD hd choice
local notation "Iₛ" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) E hdH conn F choice

/-- This extent is the unchanged number of physical sites. -/
theorem site_count : Nₛ = X.positions := by
  rw [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv (a+g)),
    Fintype.card_fin,pow_add,Nat.mul_assoc]

/-- Contents of the inputs, including the selected motif's supply widths. -/
structure SourceTables : Prop where
  target : ∀ s, (ref (I.target + word (O s).val).val).val = (O (bundleTarget (splitSlots X) s)).val
  total : ∀ s, (ref (I.total + word (O s).val).val).val = ∑ j, bundleWidths (bitWordFinEquiv a) (splitWidths X) s j
  targetPort : ∀ e : Fin (2^a) × Fin dH, (ref (I.targetPort + word (e.1.val*dH + e.2.val)).val).val =
    (E.reverse e).1.val
  reverseSlot : ∀ e : Fin (2^a) × Fin dH, (ref (I.reverseSlot + word (e.1.val*dH + e.2.val)).val).val =
    (E.reverse e).2.val
  supply : ∀ s (k : Fin dH), (ref (I.supply + word ((O s).val*dH+k.val)).val).val = Iₛ s.1 (s.2,k)

/-- Use the final target and total of the native external segment pass. The
remaining inputs are the fixed expander table and the selected motif width
table. -/
theorem SourceTables.ofExternal (q : Fin 8 → W bits) (data : RefreshRAM.Input bits)
    (fit : Nₛ * 2^a ≤ 2^bits) (dir : Directory (splitSlots X) O (splitWidths X) q data fit)
    (done : RefreshRAM.AtCursor q (Nₛ*2^a) data ref (Nₛ*2^a))
    (targetBase : I.target = q 2) (totalBase : I.total = q 4)
    (totals : ∀ s, (RefreshRAM.cell q ref 4 (bundleWord O fit s)).val =
      ∑ j, bundleWidths (bitWordFinEquiv a) (splitWidths X) s j)
    (targetPort : ∀ e : Fin (2^a) × Fin dH, (ref (I.targetPort + word (e.1.val*dH + e.2.val)).val).val =
      (E.reverse e).1.val)
    (reverseSlot : ∀ e : Fin (2^a) × Fin dH, (ref (I.reverseSlot + word (e.1.val*dH + e.2.val)).val).val =
      (E.reverse e).2.val)
    (supply : ∀ s (k : Fin dH), (ref (I.supply + word ((O s).val*dH+k.val)).val).val = Iₛ s.1 (s.2,k)) :
    SourceTables X E hdH conn F choice I ref := by
  have idx (s) : word (bits := bits) (O s).val = bundleWord O fit s :=
    Fin.ext (Nat.mod_eq_of_lt (bundleWord O fit s).isLt)
  refine ⟨fun s => ?_,fun s => ?_,targetPort,reverseSlot,supply⟩
  · rw [targetBase,idx]
    exact (congrArg Fin.val (done.target _ (bundleWord_live O q (fit := fit) dir.degree s))).trans (dir.target s)
  · rw [totalBase,idx]
    exact totals s

/-- Word-size bounds for port count, residual lane count, refreshed degree, and all packed
actual slot identifiers. -/
structure Fits (bits : ℕ) : Prop where
  ports : 2^a < 2^bits
  lanes : 2^g < 2^bits
  degree : 2^a₀ < 2^bits
  ids : Nₛ * 2^a₀ ≤ 2^bits

local notation "classOf" => Equiv.symm (refreshSlots hd)
local notation "tables" => (fun k : Fin (2^a₀) => words (2^a) (2^g) I T (classOf k))
local notation "routine" => (fun k : Fin (2^a₀) => kindOf (classOf k))
local notation "rec" => (entry routine tables ref)

private theorem record_at (input : SourceTables X E hdH conn F choice I ref) (fit : Fits (a₀ := a₀) X bits)
    (i : Fin Nₛ) (c : RefreshSlot dH (2^a₀)) :
    let pub := words (2^a) (2^g) I T c
    Represents X.baseIndex (bitWordFinEquiv g) (expected (kindOf c) pub ref i)
      (slotRecord (splitSlots X) (bitWordFinEquiv a) (splitWidths X) E.toSlotGraph hd Iₛ ((O).symm i) c) := by
  let s := (O).symm i
  let pub := words (2^a) (2^g) I T c
  have dims : Dimensions pub (Fintype.card X.Base) (2^a) (2^g) dH (2^a₀) :=
    ⟨Nat.mod_eq_of_lt fit.ports, Nat.mod_eq_of_lt (by have := fit.degree; omega),
      Nat.mod_eq_of_lt fit.degree,Nat.mod_eq_of_lt fit.lanes,fit.ids⟩
  have hi : i = O s := ((O).apply_symm_apply i).symm
  change Represents _ _ (row _ pub ref (word i.val)) (slotRecord _ _ _ _ hd Iₛ s c)
  rw [hi]
  rcases c with k | k | k
  · cases Subsingleton.elim k 0
    exact external_record X.baseIndex (bitWordFinEquiv g) hd dims (splitSlots X) (bitWordFinEquiv a)
      (splitWidths X) E.toSlotGraph Iₛ s (input.target s) (input.total s)
  · exact expander_record X.baseIndex (bitWordFinEquiv g) hd dims (splitSlots X) (bitWordFinEquiv a)
      (splitWidths X) E.toSlotGraph Iₛ s k (Nat.mod_eq_of_lt (by change k.val < 2^bits; have := fit.degree; have := k.isLt; omega))
      (input.targetPort (s.2,k)) (input.reverseSlot (s.2,k)) (input.supply s k)
  · exact padding_record X.baseIndex (bitWordFinEquiv g) hd dims (splitSlots X) (bitWordFinEquiv a)
      (splitWidths X) E.toSlotGraph Iₛ s k (Nat.mod_eq_of_lt (by change k.val < 2^bits; have := fit.degree; have := k.isLt; omega))

/-- Recover the source arc from its two scan counters. -/
def source (k : Fin (2^a₀)) (i : Fin Nₛ) : ActualArc X.Base (BitWord g) (2^a) (2^a₀) :=
  (promotedSites ((O).symm i),k)

private theorem source_eq {k j : Fin (2^a₀)} {i l : Fin Nₛ} (h : source X k i = source X j l) :
    k = j ∧ i = l :=
  ⟨congrArg Prod.snd h,(O).symm.injective (promotedSites.injective (congrArg Prod.fst h))⟩

private theorem source_covers (e : ActualArc X.Base (BitWord g) (2^a) (2^a₀)) :
    ∃ k i, source X k i = e :=
  ⟨e.2,O (promotedSites.symm e.1),by simp [source]⟩

/-- The state-independent directory and the native slot writer use the same
port identifiers, even though the new base-index codomain is a cardinality cast. -/
theorem actualPort_eq (e : ActualArc X.Base (BitWord g) (2^a) (2^a₀)) :
    IncidenceDirectory.actualPort (w := bits) Y e = word (A e).val := by
  rcases e with ⟨⟨⟨v,j⟩,l⟩,k⟩
  apply congrArg (word (bits := bits))
  change ((j.val + 2^a * (X.baseIndex v).val) * 2^g + (bitWordFinEquiv g l).val) * 2^a₀ + k.val =
    k.val + 2^a₀ * ((bitWordFinEquiv g l).val + 2^g * (j.val + 2^a * (X.baseIndex v).val))
  ring

private theorem ids (input : SourceTables X E hdH conn F choice I ref) (fit : Fits (a₀ := a₀) X bits)
    (k : Fin (2^a₀)) (i : Fin Nₛ) :
    (rec k i).src.val = (A (source X k i)).val ∧
      (rec k i).dst.val = (A ((Y).slots.actualGraph.target (source X k i))).val ∧
      (rec k i).width.val = (Y).width (((source X k i).1.1,(source X k i).2),(source X k i).1.2) := by
  have r := record_at X E hdH conn F hd choice I T ref input fit i (classOf k)
  have h := actual_record X.baseIndex (bitWordFinEquiv g) hD hd (splitSlots X) (bitWordFinEquiv a)
    (splitWidths X) E.toSlotGraph Iₛ ((O).symm i) (classOf k) (rec k i) r
  dsimp only at h
  rw [Equiv.apply_symm_apply] at h
  exact h

include hD in
private theorem row_index_lt (input : SourceTables X E hdH conn F choice I ref) (fit : Fits (a₀ := a₀) X bits)
    (k : Fin (2^a₀)) (i : Fin Nₛ) (c : Column) :
    (rowIndex (rec k i) c).val < Nₛ*2^a₀ := by
  obtain ⟨ho,hi,_⟩ := ids X E hdH conn F hD hd choice I T ref input fit k i
  cases c with
  | outgoing | width => exact ho ▸ (A (source X k i)).isLt
  | incoming => exact hi ▸ (A ((Y).slots.actualGraph.target (source X k i))).isLt

private theorem global_layout (input : SourceTables X E hdH conn F choice I ref) (fit : Fits (a₀ := a₀) X bits)
    (phys : T.Layout Y) (apart : InputsApart T routine tables Nₛ) : Layout routine tables ref Nₛ := by
  have bound := row_index_lt X E hdH conn F hD hd choice I T ref input fit
  constructor
  · intro k j i l c x hx
    rw [address_eq]
    exact apart k i x hx c _ (bound j l c)
  · intro k j i l c b he
    rw [address_eq,address_eq,columnBase_eq,columnBase_eq] at he
    have count : Fintype.card (Y).Base = Fintype.card X.Base * 2^a := by
      change Fintype.card (X.Base × Fin (2^a)) = _
      simp [Fintype.card_prod]
    have key := (phys.apart _ _ _ _ (by rw [count]; exact bound k i c)
      (by rw [count]; exact bound j l b)).mp (congrArg Fin.val he)
    have hcb := columnNumber_injective key.1
    subst b
    obtain ⟨ho,hi,_⟩ := ids X E hdH conn F hD hd choice I T ref input fit k i
    obtain ⟨ho',hi',_⟩ := ids X E hdH conn F hD hd choice I T ref input fit j l
    have hs : source X k i = source X j l := by
      cases c with
      | outgoing | width =>
        exact (A).injective (Fin.ext (ho.symm.trans ((congrArg Fin.val key.2).trans ho')))
      | incoming =>
        exact (Y).slots.actualGraph.target.injective ((A).injective
          (Fin.ext (hi.symm.trans ((congrArg Fin.val key.2).trans hi'))))
    obtain ⟨hk,hj⟩ := source_eq X hs
    exact ⟨hk,hj,rfl⟩

private theorem asWord {v : W bits} {n : ℕ} (h : v.val = n) : v = word n :=
  Fin.ext (h.trans (Nat.mod_eq_of_lt (h ▸ v.isLt)).symm)

private theorem terminal (input : SourceTables X E hdH conn F choice I ref) (fit : Fits (a₀ := a₀) X bits)
    (m : Memory bits) (rows : Completed routine tables ref ref m (List.finRange (2^a₀)) Nₛ) :
    T.ActualColumns Y m := by
  have atSource (e : ActualArc X.Base (BitWord g) (2^a) (2^a₀)) :
      let src := IncidenceDirectory.actualPort (w := bits) Y e
      let dst := IncidenceDirectory.actualPort (w := bits) Y ((Y).slots.actualGraph.target e)
      m (T.actualOut + src).val = dst ∧ m (T.actualIn + dst).val = src ∧
        m (T.width + src).val = CursorRAM.encode bits ((Y).width ((e.1.1,e.2),e.1.2)) := by
    obtain ⟨k,i,rfl⟩ := source_covers X e
    obtain ⟨hs,ht,hw⟩ := ids X E hdH conn F hD hd choice I T ref input fit k i
    have src := (asWord hs).trans (actualPort_eq X E hdH conn F hD hd choice (source X k i)).symm
    have dst := (asWord ht).trans (actualPort_eq X E hdH conn F hD hd choice
      ((Y).slots.actualGraph.target (source X k i))).symm
    have store := rows.rows k (List.mem_finRange k) i
    have ho := store .outgoing
    have hi := store .incoming
    have hl := store .width
    change m (T.actualOut + (rec k i).src).val = (rec k i).dst at ho
    change m (T.actualIn + (rec k i).dst).val = (rec k i).src at hi
    change m (T.width + (rec k i).src).val = (rec k i).width at hl
    rw [src,dst] at ho hi
    rw [src,asWord hw] at hl
    exact ⟨ho,hi,hl⟩
  refine ⟨fun e => (atSource e).1, fun e => ?_, fun e => (atSource e).2.2⟩
  simpa only [Equiv.apply_symm_apply] using (atSource ((Y).slots.actualGraph.target.symm e)).2.1

/-- Starting with the concatenation directory, fixed expander and chosen supply
table, execute every slot scan and obtain all three actual fields of the
refreshed state's incidence directory. Every other memory cell is preserved. -/
theorem all_slots (input : SourceTables X E hdH conn F choice I ref) (fit : Fits (a₀ := a₀) X bits)
    (phys : T.Layout Y) (apart : InputsApart T routine tables Nₛ) :
    ∃ rs, Runs routine tables Nₛ (List.finRange (2^a₀)) ref rs ∧
      T.ActualColumns Y (after ref (eventLog rs)) ∧
      (∀ addr, Outside T (Nₛ*2^a₀) addr → after ref (eventLog rs) addr = ref addr) ∧
      RAMBuckets.cost Report.probes rs = (6 + 7*dH + 4*(2^a₀-(dH+1))) * X.positions := by
  have layout := global_layout X E hdH conn F hD hd choice I T ref input fit phys apart
  obtain ⟨rs,hr,hc,cost⟩ := runList routine tables ref layout (List.finRange (2^a₀)) ref (fun _ _ _ _ => rfl)
  refine ⟨rs,hr,terminal X E hdH conn F hD hd choice I T ref input fit _ hc,?_,?_⟩
  · intro addr outside
    apply hc.frame
    intro k _ i c
    rw [address_eq]
    exact outside c _ (row_index_lt X E hdH conn F hD hd choice I T ref input fit k i c)
  · rw [cost,← List.ofFn_id,List.map_ofFn,List.sum_ofFn,← site_count X]
    exact slot_cost hd Nₛ

end Dyadic

end CompressorRecords.PortRefresh.AllSlots

end VPVNP
end Computability
end OAI
