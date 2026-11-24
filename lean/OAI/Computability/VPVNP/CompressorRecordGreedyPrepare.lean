import OAI.Computability.VPVNP.CompressorRecordGreedyInit
import OAI.Computability.VPVNP.CompressorRecordGreedyWalk

/-!
# Preparing a greedy vertex record in a fresh burst call

Eight header words in external memory identify the current level's mate,
displacement and assignment arrays, its first record, and the record stride.
One finite instruction table uses the persistent vertex index to initialize
its label, write the two header fields and emit all operand rows. It returns
the next vertex index. The public slot-number table is independent of the
graph, the current level and the word width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression

variable {V : Type*} {N w width d : ℕ}

/-- The eight control words for preparing a greedy record, including its first address and its
stride of two header words plus operand width. -/
def controlWords (L : WalkLayout w N width) (T : PortTables w) : List (Word w) :=
  [T.degree, T.outgoing, T.incoming, T.displacements, T.labels, T.zero, L.base 0,
    Fin.ofNat _ (2 + width)]

private def loadControls (d : ℕ) : List (Op 13 (d+1)) :=
  [.stateWord 0, .constant 11 1, .constant 12 0] ++
    ([2,3,4,5,6,7,8,9] : List (Fin 13)).flatMap fun dst =>
      [.read dst 12, .binary .add 12 12 11]

private def putHeader (d : ℕ) : List (Op 13 (d+1)) :=
  [.binary .mul 10 0 9, .binary .add 1 8 10, .binary .add 10 6 0, .constant 12 0,
   .write 10 12, .write 1 10, .binary .add 10 1 9, .binary .add 1 1 11, .write 1 10, .binary .add 1 1 11]

private def nextVertex (d : ℕ) : List (Op 13 (d+1)) := [.constant 11 1, .binary .add 0 0 11]

/-- The shared record writer runs once the eight controls occupy registers 2 through 9. -/
def prepareBody (rows : OperandRows d) : List (Op 13 (d+1)) :=
  putHeader d ++ initRows rows ++ nextVertex d

/-- Native preparation code that loads the eight control words and initializes the vertex
record and its operand rows. -/
def prepareCode (rows : OperandRows d) : List (Op 13 (d+1)) :=
  loadControls d ++ prepareBody rows

/-- Instantiate the record-preparation machine with the given word width and public slot-number
table. -/
def prepareMachine (w : ℕ) (rows : OperandRows d) :=
  (template (prepareCode rows) 0).instantiate w (slotNumbers w d)

private theorem loaded (L : WalkLayout w N width) (T : PortTables w) (m : Memory w)
    (control : Stores m 0 (controlWords L T)) (s : Word w) (d : ℕ) :
    ∃ es rs, trace (slotNumbers w d) s (loadControls d) (fun _ => 0) m = some (es,rs,m) ∧
      es.length = 19 ∧ countProbes es = 8 ∧ RowInput T s 0 rs ∧ rs 11 = 1 ∧
      rs 8 = L.base 0 ∧ rs 9 = Fin.ofNat _ (2 + width) := by
  obtain ⟨h2,h3,h4,h5,h6,h7,h8,h9,_⟩ := control
  simp (config := {decide := true}) [loadControls, trace, Op.effect, BinaryOp.eval, countProbes,
    Function.update]
  simp only [zero_add] at h3 h4 h5 h6 h7 h8 h9
  exact ⟨⟨rfl, rfl, h2, h3, h4, h5, h6, h7⟩, rfl, h8, h9⟩

private theorem index_add (a b : ℕ) :
    (Fin.ofNat _ a : Word w) + Fin.ofNat _ b = Fin.ofNat _ (a + b) := by
  apply Fin.ext
  simp only [Fin.val_ofNat, Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]

private theorem index_mul (a b : ℕ) :
    (Fin.ofNat _ a : Word w) * Fin.ofNat _ b = Fin.ofNat _ (a * b) := by
  apply Fin.ext
  simp only [Fin.val_ofNat, Fin.val_mul, Nat.mod_mul_mod, Nat.mul_mod_mod]

private theorem base_index (L : WalkLayout w N width) (i : ℕ) :
    L.base 0 + Fin.ofNat _ i * Fin.ofNat _ (2 + width) = L.base i := by
  simp only [WalkLayout.base, Nat.zero_mul, Nat.add_zero, index_mul, index_add]

private theorem base_next (L : WalkLayout w N width) (i : ℕ) :
    L.base i + Fin.ofNat _ (2 + width) = L.base (i+1) := by
  simp only [WalkLayout.base, index_add, Nat.succ_mul, Nat.add_assoc]

private theorem header_written (L : WalkLayout w N width) (T : PortTables w)
    (m : Memory w) (i : Fin N) (d : ℕ) (rs : Regs w 13) (labels : T.labels = Fin.ofNat _ L.origin)
    (h : RowInput T (Fin.ofNat _ i.val) 0 rs) (unit : rs 11 = 1)
    (first : rs 8 = L.base 0) (stride : rs 9 = Fin.ofNat _ (2+width)) :
    ∃ es out, trace (slotNumbers w d) (Fin.ofNat _ i.val) (putHeader d) rs m =
        some (es, out, writeRow (writeMemory m (L.label i) 0) (L.base i.val) [L.label i, L.base (i.val+1)]) ∧
      es.length = 10 ∧ countProbes es = 3 ∧
      RowInput T (Fin.ofNat _ i.val) (L.base i.val + 1 + 1) out := by
  have hl : T.labels + (Fin.ofNat _ i.val) = L.label i := by rw [labels, index_add]; rfl
  simp (config := {decide := true}) [-Fin.ofNat_eq_cast, putHeader, trace, Op.effect, BinaryOp.eval, countProbes, Function.update,
    writeRow, h.vertex, h.labels, unit, first, stride, base_index, base_next, hl]
  exact ⟨h.vertex, rfl, h.degree, h.outgoing, h.incoming, h.shifts, h.labels, h.zero⟩

/-- Both directed mate arrays are outside the entire prepared directory. -/
def GraphOutside (L : WalkLayout w N width) (T : PortTables w) (order : V ≃ Fin N) : Prop :=
  ∀ e : V × Fin d, ∀ b ∈ [T.outgoing, T.incoming],
    (b + portNumber order e).val < L.origin ∨ L.limit ≤ (b + portNumber order e).val

theorem GraphOutside.free {L : WalkLayout w N width} {T : PortTables w} {order : V ≃ Fin N}
    (g : GraphOutside (d := d) L T order) (start size : ℕ)
    (hstart : L.origin ≤ start) (hend : start + size ≤ L.limit) :
    T.Free (d := d) order start size := by
  intro e b hb
  obtain h | h := g e b hb
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

private theorem base_bounds (L : WalkLayout w N width) (i : Fin N) :
    (L.base i.val).val = L.origin + N + i.val * (2 + width) ∧
    (L.base i.val).val + (2 + width) ≤ L.limit := by
  have h := Nat.mul_le_mul_right (2 + width) (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at h
  have := L.fits
  have hv : L.origin + N + i.val * (2 + width) < 2 ^ w := by omega
  refine ⟨Nat.mod_eq_of_lt hv, ?_⟩
  change (L.origin + N + i.val * (2 + width)) % (2 ^ w) + (2 + width) ≤ L.origin + N + N * (2 + width)
  rw [Nat.mod_eq_of_lt hv]
  omega

/-- Installing a vertex record from loaded controls. Both the low-address
initializer and the scheduler's frame-based initializer run this same suffix. -/
theorem prepareBody_trace (L : WalkLayout w N width) (T : PortTables w) (G : SlotGraph V d)
    (order : V ≃ Fin N) (rows : OperandRows d) (m : Memory w) (i : Fin N)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order m)
    (space : L.limit < 2 ^ w) (outside : GraphOutside (d := d) L T order)
    (size : (rowWords T G order (order.symm i) rows).length = width)
    (r : Regs w 13) (hr : RowInput T (Fin.ofNat _ i.val) 0 r) (hu : r 11 = 1)
    (hfirst : r 8 = L.base 0) (hstride : r 9 = Fin.ofNat _ (2+width)) :
    let ptrs := fun k : Fin N ↦ rowWords T G order (order.symm k) rows
    ∃ es last, trace (slotNumbers w d) (Fin.ofNat _ i.val) (prepareBody rows) r m =
        some (es, last, writeRow (writeMemory m (L.label i) 0) (L.base i.val) (L.record ptrs i)) ∧
      last 0 = Fin.ofNat _ (i.val+1) ∧ es.length ≤ 12 + 8*rows.length + 6*width ∧
      countProbes es = 3 + rows.length + width := by
  let s : Word w := Fin.ofNat _ i.val
  let b := L.base i.val
  let dest := b + 1 + 1
  let header := [L.label i, L.base (i.val+1)]
  let cleared := writeMemory m (L.label i) 0
  let mid := writeRow cleared b header
  let ptrs := fun k : Fin N => rowWords T G order (order.symm k) rows
  have hlen : (ptrs i).length = width := size
  obtain ⟨bs, bound⟩ := base_bounds L i
  change b.val = _ at bs
  change b.val + (2 + width) ≤ _ at bound
  have hd : dest.val = b.val + 2 := advance_val b 2 (by omega)
  have labBounds : (L.label i).val + 1 ≤ L.limit := by
    simp only [WalkLayout.label_val, WalkLayout.limit]
    have := i.isLt
    omega
  have repClear : T.Represents G order cleared := keep_tables T G order m (L.label i) [0]
    (by change (L.label i).val + 1 ≤ 2^w; omega) rep
    (outside.free _ 1 (by simp) labBounds)
  have repMid : T.Represents G order mid := keep_tables T G order cleared b header
    (by change b.val + 2 ≤ 2 ^ w; omega) repClear (outside.free _ 2 (by omega) (by omega))
  obtain ⟨bEvents, r', hb, hlb, hpb, hr'⟩ := header_written L T m i d r labels hr hu hfirst hstride
  have input : RowInput T (vertexNumber order (order.symm i)) dest r' := by
    simpa [vertexNumber, dest, b] using hr'
  obtain ⟨c, r'', hc, hlc, hpc, hr''⟩ := initRows_trace T G order s (order.symm i) rows mid dest r'
    input repMid (by rw [size]; omega) (outside.free _ _ (by omega) (by rw [size]; omega))
  let final := writeRow mid dest (ptrs i)
  let res := Fin.ofNat (2 ^ w) (i.val + 1)
  have hr0 : r'' 0 = s := by simpa [s, vertexNumber] using hr''.vertex
  have hres : s + 1 = res := index_add i.val 1
  let last := Function.update (Function.update r'' (11 : Fin 13) 1) 0 res
  have ht : trace (slotNumbers w d) s (nextVertex d) r'' final =
      some ([.tick, .tick], last, final) := by
    simp (config := {decide := true}) [-Fin.ofNat_eq_cast, nextVertex, trace, Op.effect, BinaryOp.eval, last, hr0]
    change Function.update (Function.update r'' (11 : Fin 13) 1) 0 (s + 1) = _
    rw [hres]
  let es := (bEvents ++ c) ++ [.tick, .tick]
  have he : trace (slotNumbers w d) s (prepareBody rows) r m = some (es, last, final) := by
    change trace (slotNumbers w d) s (putHeader d) r m = some (bEvents, r', mid) at hb
    change trace (slotNumbers w d) s (initRows rows) r' mid = some (c, r'', final) at hc
    simp [prepareBody, trace_append, hb, hc, ht, es]
  have hfinal : final = writeRow cleared b (L.record ptrs i) := by
    change writeRow (writeRow cleared b header) dest (ptrs i) = writeRow cleared b (header ++ ptrs i)
    rw [writeRow_append]
    rfl
  have hcBound := initRows_length_le T G order (order.symm i) rows
  rw [size] at hcBound hpc
  refine ⟨es, last, hfinal ▸ he, by simp [last, res], ?_, ?_⟩
  · simp [es, hlb, hlc]; omega
  · simp [es, probes_append, hpb, hpc, countProbes]; omega

/-- The call installs the complete record and clears the corresponding mutable
label. All inputs other than the fixed slot numbers come from external memory. -/
theorem prepare_one (L : WalkLayout w N width) (T : PortTables w) (G : SlotGraph V d)
    (order : V ≃ Fin N) (rows : OperandRows d) (m : Memory w) (i : Fin N)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order m)
    (control : Stores m 0 (controlWords L T)) (space : L.limit < 2 ^ w)
    (outside : GraphOutside (d := d) L T order)
    (size : (rowWords T G order (order.symm i) rows).length = width) :
    let P := (prepareMachine w rows).program
    let words := fun k : Fin N => rowWords T G order (order.symm k) rows
    ∃ es, execute P (1 + (prepareCode rows).length) (P.start (Fin.ofNat _ i.val)) m [] =
        some ⟨es, some (Fin.ofNat _ (i.val + 1))⟩ ∧
      after m es = writeRow (writeMemory m (L.label i) 0) (L.base i.val)
        (L.record (fun k => words k) i) ∧
      es.length ≤ 32 + 8 * rows.length + 6 * width ∧
      countProbes es = 11 + rows.length + width := by
  let s : Word w := Fin.ofNat _ i.val
  obtain ⟨a,r,ha,hla,hpa,hr,hu,hfirst,hstride⟩ := loaded L T m control s d
  obtain ⟨b,last,hb,hresult,hlen,hprobes⟩ :=
    prepareBody_trace L T G order rows m i labels rep space outside size r hr hu hfirst hstride
  have he : trace (slotNumbers w d) s (prepareCode rows) (fun _ ↦ 0) m =
      some (a++b,last,writeRow (writeMemory m (L.label i) 0) (L.base i.val)
        (L.record (fun k ↦ rowWords T G order (order.symm k) rows) i)) := by
    rw [prepareCode,trace_append,ha]
    simp only [Option.bind_some]
    rw [hb]; rfl
  refine ⟨a++b, ?_, trace_after he, ?_, ?_⟩
  · let M := prepareMachine w rows
    change execute M.program (1 + (prepareCode rows).length) ⟨M.entry, s, fun _ => 0, fun _ => 0⟩ m [] = _
    dsimp only [M, prepareMachine]
    rw [execute_template, run_eq_trace, he]
    simp [hresult]
  · rw [List.length_append, hla]; omega
  · rw [probes_append,hpa,hprobes]; omega

end CompressorRecords.Greedy

end VPVNP
end Computability
end OAI
