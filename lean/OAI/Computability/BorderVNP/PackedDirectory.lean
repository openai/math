import OAI.Computability.BorderVNP.PackedDeliveries

/-! # Public interval directory for the deliveries in Proposition 7.2

One row describes a positive-width intersection of a public field with a block. The private
directory crosses blocks of reserved processor-tail bits. The literal and additional-pin
directories cross blocks of consecutive slots at the initial sites.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

/-- Half-open intersection of the field starting at `start` with one block. The first
coordinate is the absolute start, and the second is the number of occupied bits. -/
def slice (start len block step : ℕ) : ℕ × ℕ :=
  let left := (start / block + step) * block
  let beginAt := max start left
  (beginAt, min (start + len) (left + block) - beginAt)

/-- The actual occupied positions are exactly the positions common to field and block. -/
theorem mem_slice_iff (start len block step i : ℕ) :
    let p := slice start len block step
    (p.1 ≤ i ∧ i < p.1 + p.2) ↔
      (start ≤ i ∧ i < start + len ∧
        (start / block + step)*block ≤ i ∧ i < (start / block + step)*block + block) := by
  dsimp [slice]
  omega

/-- Each field bit belongs to a unique intersecting block. At most `len / block + 2`
candidate intervals must be examined. -/
theorem slice_cover {start len block : ℕ} (hb : 0 < block) (i : Fin len) :
    ∃! k : Fin (len / block + 2), let p := slice start len block k
      p.1 ≤ start + i ∧ start + i < p.1 + p.2 := by
  have hstart := Nat.div_le_div_right (c := block) (Nat.le_add_right start i)
  have ha := Nat.mod_add_div start block
  have hx := Nat.mod_add_div (start+i) block
  have hl := Nat.mod_add_div len block
  have h1 := Nat.mod_lt start hb
  have h2 := Nat.mod_lt (start+i) hb
  have h3 := Nat.mod_lt len hb
  have h4 : (start+i)/block < start/block + len/block + 2 := by
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm (start/block), Nat.mul_comm (len/block)]
    omega
  let k : Fin (len / block + 2) := ⟨(start+i)/block - start/block, by omega⟩
  have hk : start/block + k.val = (start+i)/block := Nat.add_sub_of_le hstart
  refine ⟨k, (mem_slice_iff ..).mpr ?_, fun j hj ↦ ?_⟩
  · rw [hk, Nat.mul_comm]
    have := i.isLt
    omega
  · have h := (mem_slice_iff ..).mp hj
    have hi : (start+i)/block = start/block + j.val := by
      apply Nat.le_antisymm
      · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb).mpr (by simpa [Nat.succ_mul] using h.2.2.2))
      · exact (Nat.le_div_iff_mul_le hb).mpr h.2.2.1
    exact Fin.ext (by omega)

/-- With one padded string at most as long as a processor tail, the third candidate is
unnecessary, even for a string beginning at the last bit of its tail. -/
theorem short_slice_cover {start len block : ℕ} (hb : 0 < block) (hs : len ≤ block) (i : Fin len) :
    ∃! k : Fin 2, let p := slice start len block k
      p.1 ≤ start + i ∧ start + i < p.1 + p.2 := by
  obtain ⟨k,hk,hu⟩ := slice_cover (start := start) hb i
  have hin := (mem_slice_iff ..).mp hk
  have lo := (Nat.le_div_iff_mul_le hb).mpr hin.2.2.1
  have hi := interval_two_blocks start len block hs i
  have small : k.val < 2 := by omega
  refine ⟨⟨k.val,small⟩,hk,fun j hj => ?_⟩
  have hj2 : j.val < len / block + 2 := lt_of_lt_of_le j.isLt (Nat.le_add_left 2 _)
  have h := hu ⟨j.val,hj2⟩ hj
  exact Fin.ext (congrArg (fun a : Fin (len / block + 2) => a.val) h)

/-- The fields fixed in the public placement frame. `fields` is one for ordinary literal
pins and two when the additional pinned field is also present. -/
structure Layout where
  /-- Number of teams. -/
  teams : ℕ
  /-- Number of processors per team. -/
  processors : ℕ
  /-- Width of a processor's literal field. -/
  literal : ℕ
  /-- Width of one exterior field in a processor's slots. -/
  link : ℕ
  /-- Number of initial sites per copy of the batch network. -/
  sites : ℕ
  /-- Number of raw slots in a site block. -/
  block : ℕ
  /-- Padded length of one private site description. -/
  description : ℕ
  /-- Number of bottom bundle/site pairs. -/
  entries : ℕ
  /-- Literal and optional extra pin fields per processor. -/
  fields : ℕ

/-- Seven public words consumed by the routing table builder. -/
structure Row where
  /-- Team supplying the live value. -/
  team : ℕ
  /-- Processor within that team. -/
  processor : ℕ
  /-- Zero for a literal, one for an additional pinned field. -/
  field : ℕ
  /-- First bit within the source field. -/
  offset : ℕ
  /-- Final cell receiving the data. -/
  cell : ℕ
  /-- First receiving slot within the chosen cell's bank. -/
  slot : ℕ
  /-- Number of consecutive bits copied. -/
  width : ℕ
  deriving DecidableEq

/-- Order used by the wire router's seven-word ABI. -/
def Row.words (row : Row) : List ℕ :=
  [row.team, row.processor, row.field, row.offset, row.cell, row.slot, row.width]

/-- Consecutive initial slots between the starts of successive processors' literal fields. -/
def Layout.stride (d : Layout) : ℕ := d.fields*d.literal + (d.teams-1)*d.link

/-- Padded descriptions are enumerated by bundle, site, and then tail piece. -/
def Layout.privateRow (d : Layout) (placed : ℕ → ℕ × ℕ) (j step : ℕ) : Row :=
  let tail := d.literal/2
  let start := j*d.description
  let p := slice start d.description tail step
  let processor := start/tail + step
  ⟨processor/d.processors, processor%d.processors, 0,
    d.literal-tail + (p.1-processor*tail), (placed j).1, (placed j).2+(p.1-start), p.2⟩

/-- Live deliveries are enumerated by team, processor, field and intersected site block.
The slot within the cell's bank advances by the bit's offset inside that site block. -/
def Layout.liveRow (d : Layout) (placed : ℕ → ℕ × ℕ) (team proc field step : ℕ) : Row :=
  let start := proc*d.stride + field*(d.literal+(d.teams-1)*d.link)
  let p := slice start d.literal d.block step
  let site := start/d.block + step
  let dest := placed (team*d.sites + site)
  ⟨team, proc, field, p.1-start, dest.1, dest.2+(p.1-site*d.block), p.2⟩

/-- Row-major candidate counts. Empty intersections are omitted by the writer. -/
def Layout.candidates (d : Layout) : ℕ :=
  2*d.entries + d.teams*d.processors*d.fields*(d.literal/d.block+2)

/-- Decode one candidate in directory order. The private placements are indexed by
bottom bundle and site and the live placements by team and initial site. -/
def Layout.row (d : Layout) (privatePlace livePlace : ℕ → ℕ × ℕ) (i : ℕ) : Row :=
  if i < 2*d.entries then d.privateRow privatePlace (i/2) (i%2)
  else
    let j := i-2*d.entries
    let k := d.literal/d.block+2
    let slot := j/k
    let proc := slot/d.fields
    d.liveRow livePlace (proc/d.processors) (proc%d.processors) (slot%d.fields) (j%k)

/-- Reading the actual rows in order visits exactly the positive intersections. -/
def Layout.directory (d : Layout) (privatePlace livePlace : ℕ → ℕ × ℕ) : List Row :=
  ((List.range d.candidates).map (d.row privatePlace livePlace)).filter (fun r => 0 < r.width)

/-- Sparse output never exceeds the number of candidates. -/
theorem Layout.directory_length_le (d : Layout) (p l : ℕ → ℕ × ℕ) :
    (d.directory p l).length ≤ d.candidates := by
  unfold directory
  simpa only [List.length_map, List.length_range] using List.length_filter_le _ ((List.range d.candidates).map (d.row p l))

end Packing.Directory

end BorderVNP
end Computability
end OAI
