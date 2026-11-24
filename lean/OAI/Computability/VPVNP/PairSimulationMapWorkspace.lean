import OAI.Computability.VPVNP.PairSimulationMapCallSetup
import OAI.Computability.VPVNP.PairSimulationNodeFieldSpace

/-!
# Physical workspace of a selected map call

The live-word capacity estimates of Section 13 apply to every payload offset
of every selector sequence, including sequences ultimately rejected by the
width guards. Given the physical slice positions and separated scratch blocks,
these estimates construct the workspace consumed by the executable map.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapWorkspace

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifEntry MapLookup MapPortAgreement
open MapResidentAgreement MapEntryTable NodeArguments
open CursorBounds Filter
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H')
  {w n u t p r k : ℕ}

/-- Capacity available throughout the numerically bounded workspace of one selected node. -/
structure Capacity (w n limit : ℕ) : Prop where
  selectorBits : B.selectorBits ≤ w
  demandBits : ∀ z e, baseDemand B z e ≤ w
  payloadBits : ∀ s e, basePayload B s e ≤ w
  room : limit < 2 ^ w
  fields : ∀ a ≤ limit, ReadEndsFit B w n a

variable [DecidableEq J] {B} {z : B.grid.demands} {j : J}
  (P : MapEntry.Program B z j p r k)
  (demand : D → ℕ) (v : E → ℕ)

/-- Natural addresses of the operand slices and scratch blocks. The histogram may be
shared across successive calls. -/
structure Regions (D E : Type) where
  /-- Natural start address of each demand or supply endpoint's raw bit slice in private
  memory. -/
  base : LabelField D E → ℕ
  /-- Natural base address of the incident-port directory that stores pointers to the supply
  selector suffixes. -/
  directory : ℕ
  /-- Natural start address of the private array of decoded selector ordinals, one per copy. -/
  source : ℕ
  /-- Natural start address of the private array of parameter labels returned by the selected
  rows. -/
  target : ℕ
  /-- Natural base address of the parameter histogram whose counters may be shared across map
  calls. -/
  hist : ℕ

variable (R : Regions D E)

/-- Actual raw half-wire width, including all selector suffix bits on supply. -/
def rawWidth (selectorBits u : ℕ) : LabelField D E → ℕ
  | .inl (_, e) => demand e
  | .inr (_, e) => v e + u * selectorBits

/-- All physical ranges fit in a common prefix. The source and target sides
may use the same addresses wherever their values agree. -/
structure Ordered (u t limit : ℕ) : Prop where
  inputEnd : ∀ f, R.base f + rawWidth demand v B.selectorBits u f ≤ R.directory
  directoryEnd : R.directory + (ports G j P.edgeOrder).length ≤ R.source
  selectorEnd : R.source + u ≤ R.target
  labelEnd : R.target + u ≤ limit
  histogramEnd : R.hist + t ≤ limit
  histApart : R.target + u ≤ R.hist ∨ R.hist + t ≤ R.directory

variable {demand v} (d : DemandBits src dst demand j)
  (x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j)

private theorem len_le (θ : Fin u → Selector B) (f : LabelField D E) :
    (MapRowLoop.buffers B z j demand v d x R.base θ 0).len f ≤
      rawWidth demand v B.selectorBits u f := by
  rcases f with ⟨b, e⟩ | ⟨b, e⟩
  · cases b
    · by_cases h : j = src e <;> simp [MapRowLoop.buffers, MapRow.endpoint, rawWidth, h]
    · by_cases h : j = dst e <;> simp [MapRowLoop.buffers, MapRow.endpoint, rawWidth, h]
  · cases b
    · by_cases h : j = G.src e <;> simp [MapRowLoop.buffers, MapRow.endpoint, rawWidth, h]
    · by_cases h : j = G.dst e <;> simp [MapRowLoop.buffers, MapRow.endpoint, rawWidth, h]

/-- Construct the full native workspace using a bound on copy count and the physical
address inequalities. All selector-dependent obligations follow from capacity. -/
noncomputable def workspace {limit : ℕ} (C : Capacity B w n limit) (hu : u ≤ n)
    (h : Ordered P demand v R u t limit) :
    MapEntry.Program.Workspace P demand v d x t w := by
  have hds : R.directory ≤ R.source := (Nat.le_add_right ..).trans h.directoryEnd
  have hst : R.source ≤ R.target := (Nat.le_add_right ..).trans h.selectorEnd
  have htl : R.target ≤ limit := (Nat.le_add_right ..).trans h.labelEnd
  have hdl := hds.trans (hst.trans htl)
  have hbase f : R.base f ≤ limit :=
    (Nat.le_add_right ..).trans ((h.inputEnd f).trans hdl)
  let pb (a : Port G j) := R.base (MapDirectoryInit.portField a)
  have pend (a : Port G j) : pb a + (v (edge a) + u * B.selectorBits) ≤ R.directory := by
    cases a with
    | inl e => exact h.inputEnd (.inr (false, e.val))
    | inr e => exact h.inputEnd (.inr (true, e.val))
  have pval (a : Port G j) : (pb a : BurstRAM.Word w).val = pb a :=
    Nat.mod_eq_of_lt ((hbase _).trans_lt C.room)
  let a := anchorPort G j
  refine ⟨fun q ↦ (pb q : BurstRAM.Word w), (R.directory : BurstRAM.Word w), R.base,
    R.source, R.target, R.hist, ?_, ?_, ?_, ?_, ?_, ?_, h.histogramEnd.trans C.room.le,
    h.selectorEnd, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((Nat.le_add_left ..).trans h.directoryEnd).trans_lt
      ((hst.trans htl).trans_lt C.room)
  · exact ((Nat.le_add_left ..).trans ((Nat.le_add_left ..).trans (pend a))).trans_lt
      (hdl.trans_lt C.room)
  · rw [pval]
    exact (pend a).trans_lt (hdl.trans_lt C.room)
  · rw [pval]
    exact Or.inl ((pend a).trans hds)
  · exact h.selectorEnd.trans_lt (htl.trans_lt C.room)
  · exact h.labelEnd.trans_lt C.room
  · exact h.histApart.imp (fun e ↦ h.selectorEnd.trans ((Nat.le_add_right ..).trans e))
      (fun e ↦ e.trans hds)
  · exact h.histApart.imp id (fun e ↦ e.trans (hds.trans hst))
  · intro θ f l
    have lt := Nat.add_lt_add_left (l.isLt.trans_le (len_le (z := z) R d x θ f)) (R.base f)
    have hend := lt.trans_le (h.inputEnd f)
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (hend.trans (hdl.trans_lt C.room))]
    exact hend.trans_le hds
  · intro θ i
    constructor
    · intro g
      cases g with
      | inl e => exact C.demandBits z e
      | inr e => exact C.payloadBits (θ i) e
    · intro f
      have reads := C.fields (R.base f) (hbase f) u hu z θ i
      rcases f with ⟨b, e⟩ | ⟨b, e⟩
      · exact reads.1 e
      · simpa only [MapRowLoop.buffers, MapRow.group, Sum.elim_inr,
          MapRowLoop.prefix_eq_offset] using reads.2.1 e
    · intro f
      have endLe := Nat.add_le_add_left (len_le (z := z) R d x θ f) (R.base f)
      exact (endLe.trans (h.inputEnd f)).trans_lt (hdl.trans_lt C.room)
  · intro θ e
    cases u with
    | zero => simp [totalWidth]
    | succ k =>
      exact (C.fields (R.base (MapDirectoryInit.portField a)) (hbase _) _ hu z θ 0).2.2.1 e

private theorem word_ne {a b w : ℕ} (h : a < b) (hb : b < 2 ^ w) :
    (a : BurstRAM.Word w) ≠ (b : BurstRAM.Word w) := by
  intro he
  have eq := congrArg Fin.val he
  change a % (2 ^ w) = b % (2 ^ w) at eq
  rw [Nat.mod_eq_of_lt (h.trans hb), Nat.mod_eq_of_lt hb] at eq
  omega

omit [Fintype J] [Fintype D] in
private theorem demand_len (q : Bool × D) :
    (MapRow.endpoint src dst j demand d q).1 ≤ demand q.2 := by
  rcases q with ⟨b, e⟩
  cases b
  · by_cases h : j = src e <;> simp [MapRow.endpoint, h]
  · by_cases h : j = dst e <;> simp [MapRow.endpoint, h]

omit [DecidableEq J] in
private theorem port_raw (q : Port G j) :
    rawWidth demand v B.selectorBits u (MapDirectoryInit.portField q) =
      v (edge q) + u * B.selectorBits := by
  cases q <;> rfl

/-- The histogram may be below the directory or above the label staging. Either
physical ordering prevents setup stores from changing any histogram counter. -/
theorem histogram_apart {limit : ℕ} (C : Capacity B w n limit)
    (h : Ordered P demand v R u t limit) (l : Fin t) (i : Fin (ports G j P.edgeOrder).length) :
    ((R.hist + l.val : ℕ) : BurstRAM.Word w) ≠
      (R.directory : BurstRAM.Word w) + (i.val : BurstRAM.Word w) := by
  rw [← Nat.cast_add]
  have di := (Nat.add_lt_add_left i.isLt R.directory).trans_le h.directoryEnd
  have tl := (Nat.add_lt_add_left l.isLt R.hist).trans_le h.histogramEnd
  rcases h.histApart with before | after
  · apply Ne.symm
    exact word_ne (di.trans_le (by have := h.selectorEnd; omega)) (tl.trans C.room)
  · apply word_ne
    · have ht := Nat.add_lt_add_left l.isLt R.hist
      omega
    · exact (di.trans_le (by have := h.selectorEnd; have := h.labelEnd; omega)).trans C.room

/-- A raw descriptor and the actual stored half-wire bits suffice to build the
initializer's input. The physical ordering proves all directory disjointness tests. -/
theorem input {limit : ℕ} (A : Allocation B z j r k) (loc : A.Address → Fin p)
    (args : MapCallSetup.Arg D E ≃ Fin (Fintype.card (MapCallSetup.Arg D E)))
    (C : Capacity B w n limit) (hu : u ≤ n) (h : Ordered (A.program loc) demand v R u t limit)
    (ptr : Fin r) (c : BurstRAM.PrivateRAM.Config w p r) :
    let X := workspace (A.program loc) R d x C hu h
    (∀ a, c.privateMem (c.reg ptr + ((args a).val : BurstRAM.Word w)) =
      MapCallSetup.values A loc X a) →
    (∀ (q : Port G j) (l : Fin (v (edge q) + u * B.selectorBits)),
      c.privateMem ((R.base (MapDirectoryInit.portField q) + l.val : ℕ) : BurstRAM.Word w) =
        PrimedInputRAM.encodeBit w (field x q l)) →
    (∀ (q : Bool × D) (l : Fin (MapRow.endpoint src dst j demand d q).1),
      c.privateMem ((R.base (.inl q) + l.val : ℕ) : BurstRAM.Word w) =
        PrimedInputRAM.encodeBit w ((MapRow.endpoint src dst j demand d q).2 l)) →
    MapCallSetup.Input A args loc X ptr c := by
  intro X descriptor supply dem
  have dlim : R.directory ≤ limit := by
    have := h.directoryEnd; have := h.selectorEnd; have := h.labelEnd; omega
  have di (i : MapDirectoryInit.Row A) : R.directory + i.val < 2 ^ w := by
    have hi := i.isLt
    have de := h.directoryEnd
    change R.directory + (ports G j A.edgeOrder).length ≤ R.source at de
    exact (show R.directory + i.val < limit by
      have := h.selectorEnd; have := h.labelEnd; omega).trans C.room
  refine ⟨descriptor, ?_, fun _ ↦ rfl, ?_, dem, ?_, ?_⟩
  · intro e
    have eh := h.inputEnd (.inr (false, e))
    change R.base (.inr (false, e)) + (v e + u * B.selectorBits) ≤ R.directory at eh
    exact (show v e ≤ limit by omega).trans_lt C.room
  · intro q l
    change c.privateMem ((R.base (MapDirectoryInit.portField q) : BurstRAM.Word w) + _) = _
    simpa only [Nat.cast_add] using supply q l
  · intro q l i
    have endLe := h.inputEnd (MapDirectoryInit.portField q)
    rw [port_raw] at endLe
    have hi := (Nat.add_lt_add_left l.isLt (R.base (MapDirectoryInit.portField q))).trans_le endLe
    change (R.base (MapDirectoryInit.portField q) : BurstRAM.Word w) + _ ≠
      (R.directory : BurstRAM.Word w) + _
    rw [← Nat.cast_add, ← Nat.cast_add]
    exact word_ne (hi.trans_le (Nat.le_add_right ..)) (di i)
  · intro q l i
    have eh := h.inputEnd (.inl q)
    change R.base (.inl q) + demand q.2 ≤ R.directory at eh
    have hi := (Nat.add_lt_add_left (l.isLt.trans_le (demand_len d q)) _).trans_le eh
    change ((R.base (.inl q) + l.val : ℕ) : BurstRAM.Word w) ≠ (R.directory : BurstRAM.Word w) + _
    rw [← Nat.cast_add]
    exact word_ne (hi.trans_le (Nat.le_add_right ..)) (di i)

section Selected

open CursorNetwork Compression CompressorRecords TraversalRows

variable {S : BlockSchedule K}

omit [DecidableEq J] in
/-- Every node in every selected descriptor branch has the map capacity required above.
The threshold is chosen before the branch, its coefficient specialization, and the node. -/
theorem eventually_selected_capacity (F : DescriptorSpace.Shape) (T : S.Templates)
    (u₀ : PairExponents T.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    {start first extra : ℕ → ℕ} (hs : PolynomiallyBounded start)
    (hf : PolynomiallyBounded first) (he : PolynomiallyBounded extra) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u₀.θ : ℝ) n * S.laneBits ≤ lanes)
        (R₀ : Type*) [CommRing R₀] (f : T.Entry → R₀) (hsol : T.IsSolution f),
        let X := pairInput S labels hD
        let count := blockCount (u₀.θ : ℝ) n
        let exec := T.execute f hsol count hT X
        let layout := DescriptorSpace.cursorLayout F b S.steps u₀.θ (start n) n
        let arena : Arena := ⟨first n, frameStride (slotDegree S) n⟩
        ∀ choice : exec.Choices, ∀ v node,
          node ∈ (selectedTrees T f hsol count hT X choice
            (DescriptorSpace.endAddress layout) v).preorder →
            Capacity B (wordBits b n) n (arena.base node + arena.stride + extra n) := by
  have hb' : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  filter_upwards [eventually_selected_node_fields B F T u₀ b hb hs hf he,
    MapStream.eventually_polynomial_field_addresses B b hb' (fun _ ↦ 0)
      (PolynomiallyBounded.const 0)] with n selected widths
  intro base lanes labels hD hT R₀ _ f hsol X count exec layout arena choice v node member
  have room := selected labels hD hT R₀ f hsol choice v node member
  exact ⟨widths.1, widths.2.1, widths.2.2.1, room.1, room.2.1⟩

omit [DecidableEq J] in
/-- A polynomial upper limit on the shared scratch region also supports every field
read in the whole prefix. This covers operands materialized above the node's own frame. -/
theorem eventually_capacity (b : ℕ) (hb : 1 ≤ b) (limit : ℕ → ℕ)
    (hl : PolynomiallyBounded limit) :
    ∀ᶠ n : ℕ in atTop, Capacity B (wordBits b n) n (limit n) := by
  filter_upwards [MapStream.eventually_polynomial_field_addresses B b hb limit hl,
    CursorRAM.eventual_word_room b hb hl] with n widths room
  exact ⟨widths.1, widths.2.1, widths.2.2.1, room, fun addr ha u hu z θ i ↦
    widths.2.2.2 u hu z θ i addr ha⟩

end Selected

end PairSimulation.MapWorkspace

end VPVNP
end Computability
end OAI
