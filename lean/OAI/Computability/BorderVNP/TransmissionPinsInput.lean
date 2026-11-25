import OAI.Computability.BorderVNP.TransmissionPinsRead
import OAI.Computability.BorderVNP.RoutingISABoot
import OAI.Computability.BorderVNP.TeamTapeInput
import OAI.Computability.BorderVNP.TeamTapeInputEmitChunks
import OAI.Computability.VPVNP.RAMRecordIndex

/-! # Pin lookup in the initialized memory of the actual processor tapes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP BurstRAM

/-- The three fields extracted from each processor tape by the public input parser. -/
structure ProcessorFields (L : Layout) where
  /-- The whole literal, including its pinned program prefix and length words. -/
  literal : Fin L.processors → List Bool
  /-- The separate exterior bit strings in physical order. -/
  exterior : Fin L.processors → List (List Bool)
  /-- The final, literal-width array carrying the additional pins. -/
  pins : Fin L.processors → List Bool
  /-- Each literal has the publicly specified bit count. -/
  literal_length (i) : (literal i).length = L.literal
  /-- Each processor has an exterior block for every other team. -/
  exterior_count (i) : (exterior i).length = L.teams-1
  /-- Each partner block occupies the public link width. -/
  link_length (i) (bs : List Bool) (h : bs ∈ exterior i) : bs.length = L.link
  /-- The additional pin array has exactly the same width as the literal. -/
  pins_length (i) : (pins i).length = L.literal

namespace ProcessorFields

variable {L : Layout} (r : ProcessorFields L)

/-- The exterior fields occupy a consecutive array of link-width blocks. -/
theorem exterior_length (i : Fin L.processors) : (r.exterior i).flatten.length = (L.teams-1) * L.link := by
  have lengths : (r.exterior i).map List.length = (r.exterior i).map (fun _ => L.link) :=
    List.map_congr_left (r.link_length i)
  simp [List.length_flatten, lengths, r.exterior_count]

/-- One complete RAM initialization segment as returned by the processor's input parser. -/
def row (i : Fin L.processors) : List Bool :=
  TeamTapeInput.inputData (r.literal i) (r.exterior i) (r.pins i)

/-- The actual concatenation of the processor segments in memory address order. -/
def header : List Bool := (List.ofFn r.row).flatten

/-- The consecutive additional pins obtained by omitting each literal and exterior block. -/
def pinBits : List Bool := (List.ofFn r.pins).flatten

/-- Every physical processor segment occupies exactly one stride. -/
theorem row_length (i : Fin L.processors) : (r.row i).length = L.stride := by
  simp [row, TeamTapeInput.inputData, r.literal_length, r.exterior_length, r.pins_length,
    Layout.stride, Layout.offset, Nat.add_assoc]

/-- The initialized memory occupies the full declared processor interval. -/
theorem header_length : r.header.length = L.processors * L.stride := by
  simp [header, List.length_flatten, List.map_ofFn, Function.comp_def, r.row_length]

/-- The total flat width of all additional pin blocks. -/
theorem pinBits_length : r.pinBits.length = L.count := by
  simp [pinBits, List.length_flatten, List.map_ofFn, Function.comp_def, r.pins_length, Layout.count]

/-- Read a rectangular array of processor rows at its row-major address. -/
theorem getElem?_rows {α : Type*} {N W : ℕ} (f : Fin N → List α)
    (hw : ∀ i, (f i).length = W) (i : Fin N) (j : ℕ) (hj : j < W) :
    (List.ofFn f).flatten[i.val * W + j]? = (f i)[j]? := by
  apply (RAMSort.getElem?_flatten_rect (rows := List.ofFn f) (W := W) ?_
    (by simp : i.val < (List.ofFn f).length) hj).trans
  · simp only [List.getElem_ofFn, Fin.eta]
  · intro a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    exact hw k

/-- Reading an actual live pin address gives the corresponding entry in the
concatenated secondary fields, for every flat index. -/
theorem header_pin (x : ℕ) (hx : x < L.count) :
    r.header[livePinAddress L.teams L.literal L.link x]? = r.pinBits[x]? := by
  change x < L.processors * L.literal at hx
  have hl : 0 < L.literal := Nat.pos_of_ne_zero (by intro h; simp [h] at hx)
  let i : Fin L.processors := ⟨x / L.literal, (Nat.div_lt_iff_lt_mul hl).2 hx⟩
  have hj := Nat.mod_lt x hl
  have hj' : L.offset + x % L.literal < L.stride := by unfold Layout.stride; omega
  have lookup := getElem?_rows r.row r.row_length i (L.offset+x%L.literal) hj'
  have pinsLookup := getElem?_rows r.pins r.pins_length i (x%L.literal) hj
  have hflat : i.val * L.literal + x%L.literal = x := Nat.div_add_mod' x L.literal
  rw [hflat] at pinsLookup
  rw [header, livePinAddress_layout, Nat.add_assoc, lookup, pinBits, pinsLookup]
  unfold row TeamTapeInput.inputData
  have hlen : (r.literal i ++ (r.exterior i).flatten).length = L.offset := by
    simp [Layout.offset, r.literal_length, r.exterior_length]
  rw [List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left]

/-- A literal lookup reads the original program-prefix or free literal bit at its offset. -/
theorem header_literal (i : Fin L.processors) (j : Fin L.literal) :
    r.header[i.val*L.stride+j.val]? = (r.literal i)[j.val]? := by
  have hj : j.val < L.stride := by unfold Layout.stride; omega
  rw [header, getElem?_rows r.row r.row_length i j hj]
  unfold row TeamTapeInput.inputData
  have lit : j.val < (r.literal i).length := by rw [r.literal_length]; exact j.isLt
  rw [List.append_assoc, List.getElem?_append_left lit]

/-- The genuine input segment agrees word for word with the initialized processor tapes. -/
def ContainsInput {w : ℕ} (m : Memory w) : Prop :=
  ∀ a < r.header.length, m a = TeamTapeInputEmit.headerWord w r.header a

/-- The time-zero memory reconstructed from the actual read/write records has the input segment. -/
theorem containsInput_initial (w : ℕ) :
    r.ContainsInput (RAMMemory.initialMemory r.header.length (TeamTapeInputEmit.headerWord w r.header)) :=
  fun _ h ↦ ite_eq_left h

/-- Booting a frame above the input segment preserves every actual processor bit. -/
theorem ContainsInput.boot {w : ℕ} {r : ProcessorFields L} {m : Memory w} (h : r.ContainsInput m)
    (pub : Arg → Word w) (count : ℕ) (above : r.header.length ≤ (pub 0).val) :
    r.ContainsInput (bootMemory pub m count) := by
  intro a ha
  have lt : a < (pub 0).val := ha.trans_le above
  simpa [bootMemory, Nat.not_le.mpr lt] using h a ha

/-- A later store outside the input segment preserves the actual processor words. -/
theorem ContainsInput.store {w : ℕ} {r : ProcessorFields L} {m : Memory w} (h : r.ContainsInput m)
    (a : ℕ) (v : Word w) (above : r.header.length ≤ a) : r.ContainsInput (Function.update m a v) :=
  fun _ hi ↦ (Function.update_of_ne (hi.trans_le above).ne ..).trans (h _ hi)

/-- Every preserved live-word probe decodes the secondary pin at the same flat index. -/
theorem ContainsInput.pin {w : ℕ} {r : ProcessorFields L} {m : Memory w} (h : r.ContainsInput m)
    (x : ℕ) (hx : x < L.count) :
    m (livePinAddress L.teams L.literal L.link x) = TeamTapeInputEmit.headerWord w r.pinBits x := by
  rw [h _ (r.header_length ▸ livePinAddress_lt L hx)]
  simp only [TeamTapeInputEmit.headerWord, r.header_pin x hx]

/-- A preserved literal probe returns the original bit of that processor's literal. -/
theorem ContainsInput.literal {w : ℕ} {r : ProcessorFields L} {m : Memory w}
    (h : r.ContainsInput m) (i : Fin L.processors) (j : Fin L.literal) :
    m (i.val*L.stride+j.val) = TeamTapeInputEmit.headerWord w (r.literal i) j.val := by
  have hj : j.val < L.stride := by unfold Layout.stride; omega
  have ha : i.val * L.stride + j.val < r.header.length := by
    rw [r.header_length]
    exact (Nat.add_lt_add_left hj _).trans_le ((Nat.succ_mul _ _).symm ▸
      Nat.mul_le_mul_right L.stride i.isLt)
  rw [h _ ha]
  simp only [TeamTapeInputEmit.headerWord, r.header_literal]

/-- In the transcript checker's actual time-zero memory, the addressed word encodes
the same bit as the flat index into the collected pin fields. -/
theorem initialized_pin (w x : ℕ) (hx : x < L.count) :
    RAMMemory.initialMemory r.header.length (TeamTapeInputEmit.headerWord w r.header)
        (livePinAddress L.teams L.literal L.link x) =
      TeamTapeInputEmit.headerWord w r.pinBits x :=
  (r.containsInput_initial w).pin x hx

end ProcessorFields

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
