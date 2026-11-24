import OAI.Computability.VPVNP.PairShrinkRoleBankChild
import OAI.Computability.VPVNP.PairSimulationTerminalSplice
import OAI.Computability.VPVNP.PairVertexLevelBounds
import OAI.Computability.VPVNP.CompressorDescriptorSpace
import OAI.Computability.VPVNP.CompressorRecordsShrinkFrame
import OAI.Computability.VPVNP.CompressorFlowFootprint

/-!
# External reads of the native child decoder

Each child consumes one pointer in the selected DFS row. Each slot probes its
width, and each incoming slot first probes its inverse-incidence entry. The
typed inverse column identifies the second probe even when the memory outside
the old level contains arbitrary words. Guessing and storing the payload bits
uses only private memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.ChildArguments

open BurstRAM Compression CompressorRecords NodeArguments NodeArguments.ChildScan DFS
open scoped Fin.CommRing
open private offset_eq from OAI.Computability.VPVNP.PairNodeChildHeader

variable {w a g endAddr : ℕ} {X : State a g} {T : IncidenceDirectory w} {m : Memory w}

/-- Bounds for the two physical columns visited by the old-slot scan. -/
structure ColumnsBelow (T : IncidenceDirectory w) (X : State a g) (limit : ℕ) : Prop where
  incoming : T.actualIn.val + IncidenceDirectory.slotCount X ≤ limit
  widths : T.width.val + IncidenceDirectory.slotCount X ≤ limit

private theorem field_reads {limit : ℕ} (rep : T.ActualColumns X m)
    (col : ColumnsBelow T X limit) (dir : Bool) (e : (X.Base × BitWord g) × Fin (2 ^ a)) :
    SourceTransport.Reads (· < limit)
      (FieldGuess.headerEvents T m dir (IncidenceDirectory.actualPort X e)) := by
  have bound (base : Word w) (hb : base.val + IncidenceDirectory.slotCount X ≤ limit)
      (f : (X.Base × BitWord g) × Fin (2 ^ a)) :
      (base + IncidenceDirectory.actualPort X f).val < limit := by
    rw [Fin.val_add]
    exact (Nat.mod_le ..).trans_lt ((Nat.add_lt_add_left
      (IncidenceDirectory.actualPort_lt X f) _).trans_le hb)
  intro p v hp
  cases dir <;> simp only [FieldGuess.headerEvents, Bool.false_eq_true, ite_false,
    ite_true, List.mem_append, List.mem_cons, List.not_mem_nil, reduceCtorEq,
    Event.read.injEq, false_or, or_false] at hp
  · exact hp.1 ▸ bound T.width col.widths e
  · rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact bound T.actualIn col.incoming e
    · rw [rep.actualIn]
      exact bound T.width col.widths _

private theorem slot_reads {limit : ℕ} (rep : T.ActualColumns X m) (col : ColumnsBelow T X limit)
    (x : Child X) (slots : List (Bool × Fin (2 ^ a))) :
    SourceTransport.Reads (· < limit) (ChildSlots.events X x.site T m x.data slots) := by
  intro p v hp
  obtain ⟨i, _, h⟩ := List.mem_flatMap.mp hp
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, reduceCtorEq, false_or] at h
  exact h.elim (field_reads rep col i.1 (x.site, i.2) p v)
    ((FlowFootprint.bounds_of_noProbes (· < limit) (fun _ => False)
      (PrivateFields.events_work (w := w) .guess (List.ofFn (x.data i))).2).1 p v)

/-- External reads inside the loop over the child list. -/
theorem scan_reads_below {limit : ℕ} (rep : T.ActualColumns X m)
    (col : ColumnsBelow T X limit) (src : ℕ) (xs : List (Child X))
    (row : src + xs.length ≤ limit) :
    SourceTransport.Reads (· < limit) (events X T m src xs) := by
  induction xs generalizing src with
  | nil => intro p v hp; simp [events] at hp
  | cons x xs ih =>
    intro p v hp
    simp only [events, childEvents, setupEvents, ChildAddress.events, List.mem_append,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, Event.read.injEq, false_or, or_false] at hp
    rcases hp with (⟨rfl, _⟩ | h) | h
    · exact (Nat.mod_le ..).trans_lt (by simp only [List.length_cons] at row; omega)
    · exact slot_reads rep col x _ p v h
    · exact ih (src + 1) (by simp only [List.length_cons] at row; omega) p v h

/-- The two descriptor words and the seven old-level fields are the external
reads of the native child header. -/
theorem header_reads_below {limit : ℕ} (m : Memory w) (node base : Word w)
    (parent : node.val + 1 < limit) (old : base.val + 6 < limit) :
    SourceTransport.Reads (· < limit) (ChildHeader.events m node base) := by
  have offset (b : Word w) (j : ℕ) (h : b.val + j < limit) : (b + (j : Word w)).val < limit := by
    rw [Fin.val_add, Fin.val_natCast]
    exact (Nat.mod_le ..).trans_lt ((Nat.add_le_add_left (Nat.mod_le ..) _).trans_lt h)
  intro p v hp
  simp only [ChildHeader.events, offset_eq, List.mem_cons, List.not_mem_nil, reduceCtorEq,
    Event.read.injEq, false_or, or_false] at hp
  rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · omega
  · exact offset node 1 parent
  · omega
  all_goals (apply offset; omega)

/-- The physical child-stage trace reads only the selected row, its directory
and its incoming and width columns. This also applies to a singleton refresh. -/
theorem trace_reads_below {limit : ℕ} (rep : T.ActualColumns X m) (col : ColumnsBelow T X limit)
    (node base : Word w) (src : ℕ) (xs : List (Child X)) (parent : node.val + 1 < limit)
    (old : base.val + 6 < limit) (row : src + xs.length ≤ limit) :
    SourceTransport.Reads (· < limit) (ChildHeader.events m node base ++ events X T m src xs) :=
  fun p v hp => (List.mem_append.mp hp).elim (header_reads_below m node base parent old p v)
    (scan_reads_below rep col src xs row p v)

variable {A : Arena} {older cap : ℕ} {desc : Word w → Descriptor w X}
  {node : Word w} {saved : Scratch w endAddr} {bs rest : List Bool}
  {out : Outcome w endAddr (List (Child X))}

/-- Complete child reads are strictly below the terminal header whenever the
parent row, old directory words and the two live columns lie below it. -/
theorem reader_reads_below {limit : ℕ} (rep : T.ActualColumns X m) (col : ColumnsBelow T X limit)
    (parent : node.val + 1 < limit) (old : (desc node).directoryBase.val + 6 < limit)
    (row : (desc node).source + (desc node).sites.length ≤ limit)
    (read : reader A T m older cap desc node saved bs = some (out, rest)) :
    SourceTransport.Reads (· < limit) out.trace := by
  obtain ⟨sites, result, _⟩ := reader_some A T m older cap desc read
  have len : out.value.length = (desc node).sites.length := by
    simpa using congrArg List.length sites
  rw [congrArg Outcome.trace result]
  exact trace_reads_below rep col node _ _ _ parent old (len ▸ row)

open DescriptorSpace TraversalRoles TraversalRows VertexLevelBounds
open private incidence_end_le from OAI.Computability.VPVNP.CompressorDescriptorSpace

/-- In the descriptor allocation both columns end before the DFS row table. -/
theorem ColumnsBelow.packed (L : Layout) (level : Fin L.levels)
    (rows : IncidenceDirectory.slotCount X ≤ slotCapacity L) :
    ColumnsBelow (packedIncidence L w level (IncidenceDirectory.slotCount X)) X (endAddress L) := by
  let n := IncidenceDirectory.slotCount X
  have packed : incidenceStart L level + 6 * n ≤ endAddress L :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left 6 rows) _).trans
      ((incidence_end_le L level).trans (levelStart_mono L level.isLt))
  constructor
  · change (incidenceStart L level + 4 * n) % (2 ^ w) + n ≤ endAddress L
    have := Nat.mod_le (incidenceStart L level + 4 * n) (2 ^ w)
    omega
  · change (incidenceStart L level + 5 * n) % (2 ^ w) + n ≤ endAddress L
    have := Nat.mod_le (incidenceStart L level + 5 * n) (2 ^ w)
    omega

/-- The whole reserved child row fits inside the selected tag sequence's row
table, including the payload of its last site. -/
theorem selected_row_end (base cap : ℕ) (tags : List TaggedLayer) (j : Fin tags.length)
    (id : Fin tags[j].layer.count) :
    address cap (layerBase cap base tags j.val) id.val + 2 + cap ≤
      base + words cap (tags.map TaggedLayer.layer) := by
  have step := Nat.mul_le_mul_left (cap + 2) id.isLt
  have finish := layerBase_mono cap base tags j.isLt
  rw [layerBase_succ cap base tags j] at finish
  simp only [endPos, address, layerBase, List.take_length] at finish ⊢
  rw [Nat.mul_succ] at step
  omega

/-- Starting the child header at scalar 14 leaves all seven fields inside the
old level, before the first DFS row. -/
theorem old_fields_below (L : Layout) (level : Fin L.levels)
    (wide : 21 ≤ levelHeaderWords L) :
    (((levelStart L level + 14 : ℕ) : Word w)).val + 6 < endAddress L := by
  have next := levelStart_mono L level.isLt
  change levelStart L (level.val + 1) ≤ endAddress L at next
  have advance : levelStart L (level.val + 1) = levelStart L level + levelWords L := by
    simp only [levelStart, Nat.succ_mul, Nat.add_assoc]
  have width : levelHeaderWords L ≤ levelWords L := by unfold levelWords; omega
  rw [Fin.val_natCast]
  have := Nat.mod_le (levelStart L level + 14) (2 ^ w)
  omega

/-- Specialize the read bound to a popped descriptor at its selected row
address, with the old field bank starting at scalar 14 of the preceding
physical level. -/
theorem selected_reads_below (L : Layout) (level : Fin L.levels)
    (rep : T.ActualColumns X m)
    (columns : T = packedIncidence L w level (IncidenceDirectory.slotCount X))
    (rows : IncidenceDirectory.slotCount X ≤ slotCapacity L)
    (oldFields : 21 ≤ levelHeaderWords L)
    (tags : List TaggedLayer) (j : Fin tags.length) (id : Fin tags[j].layer.count)
    (addressEq : node.val = address cap (layerBase cap (endAddress L) tags j.val) id.val)
    (directory : (desc node).directoryBase = ((levelStart L level + 14 : ℕ) : Word w))
    (source : (desc node).source = node.val + 2)
    (capacity : (desc node).sites.length ≤ cap) (H : Word w)
    (before : endAddress L + words cap (tags.map TaggedLayer.layer) ≤ H.val)
    (read : reader A T m older cap desc node saved bs = some (out, rest)) :
    SourceTransport.Reads (· < H.val) out.trace := by
  have base : endAddress L ≤ H.val := (Nat.le_add_right ..).trans before
  have col := ColumnsBelow.packed (w := w) L level rows
  have room := (selected_row_end (endAddress L) cap tags j id).trans before
  rw [← addressEq] at room
  refine reader_reads_below rep ?_ ?_ ?_ ?_ read
  · rw [columns]
    exact ⟨col.incoming.trans base, col.widths.trans base⟩
  · omega
  · rw [directory]
    exact (old_fields_below L level oldFields).trans_le base
  · rw [source]
    omega

/-- The register-bank initializer precedes the decoder with local ticks. Thus
every external read of the hosted segment belongs to the child decoder. -/
theorem bank_reads_of_reader {data : ℕ → Prop}
    (safe : ∀ child tail, reader A T m older cap desc node saved bs = some (child, tail) →
      SourceTransport.Reads data child.trace)
    (got : BankChild.reader A T m older cap desc node saved bs = some (out, rest)) :
    SourceTransport.Reads data out.trace := by
  cases h : reader A T m older cap desc node saved bs with
  | none => simp [BankChild.reader, ShrinkRole.bind, Setup.ticks, Setup.reader, h] at got
  | some result =>
    obtain ⟨child, tail⟩ := result
    have eqn : (⟨child.value, List.replicate (2 ^ a) .tick ++ child.trace, child.updated⟩ :
        Outcome w endAddr (List (Child X))) = out := by
      simpa [BankChild.reader, ShrinkRole.bind, Setup.ticks, Setup.reader, h] using
        (congrArg (Option.map Prod.fst) got)
    intro p v hp
    rw [← eqn] at hp
    exact safe child tail h p v (by simpa using hp)

/-- A strict read bound excludes both physical terminal control addresses. -/
theorem worker_reads_of_below (H : Word w) (fit : H.val + 32 ≤ 2 ^ w)
    {es : List (Event w)} (below : SourceTransport.Reads (· < H.val) es) :
    SourceTransport.Reads (TerminalLink.workerCell H) es := by
  intro p v hp
  have low := below p v hp
  have last : (H + 31).val = H.val + 31 := by
    have numeral : (31 : Word w).val = 31 := by
      change 31 % (2 ^ w) = 31
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, numeral,
      Nat.mod_eq_of_lt (by omega)]
  exact ⟨low.ne, by omega⟩

end PairSimulation.ShrinkRole.ChildArguments

end VPVNP
end Computability
end OAI
