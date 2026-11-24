import OAI.Computability.VPVNP.CompressorDescriptorSpace
import OAI.Computability.VPVNP.CompressorExecutionLevels
import OAI.Computability.VPVNP.CompressorSourceTransport
import OAI.Computability.VPVNP.CompressorRecordRefreshLifetime

/-!
# Retaining the data of each selected pass for native site reads

The completed pass owns all the tables of its input level. Its selected
output graph lives in the successor incidence bank. Later passes can
replace the successor scalars and scratch tables while preserving that
bank. Each stored occurrence keeps the memory image in which its physical
parser data was produced and an agreement on both regions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SelectedPayloadHistory

open BurstRAM Compression DescriptorSpace SourceTransport
variable {w : ℕ} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)

/-- Pointer words and the packed canonical incidence of an input graph.
Scratch begins at the exclusive end of this range. -/
def GraphCells (L : Layout) (j x : ℕ) : Prop :=
  levelStart L j+L.shape.scalarFields ≤ x ∧ x < arrayBase L j

/-- All the producing level's fields, plus the pointer and incidence bank
of the state produced by that pass. -/
def Cells (L : Layout) (i x : ℕ) : Prop :=
  (levelStart L i ≤ x ∧ x < levelStart L (i+1)) ∨ GraphCells L (i+1) x

private theorem array_mono (L : Layout) : Monotone (arrayBase L) := by
  intro i j h
  exact Nat.add_le_add_right (Nat.add_le_add_right (levelStart_mono L h) _) _

private theorem array_before (L : Layout) (i : ℕ) : arrayBase L i ≤ levelStart L (i+1) := by
  simp only [arrayBase,incidenceStart,levelStart,levelWords,Nat.succ_mul,Nat.add_assoc]
  omega

/-- Earlier payloads occupy addresses below the final state's first scratch
table, including the last producing pass's successor incidence. -/
theorem cells_interval {L : Layout} {i n x : ℕ} (hi : i < n) (hx : Cells L i x) :
    levelsBase L ≤ x ∧ x < arrayBase L n := by
  have low (j : ℕ) : levelsBase L ≤ levelStart L j := Nat.le_add_right ..
  have high : levelStart L n ≤ arrayBase L n := by unfold arrayBase incidenceStart; omega
  have edge := levelStart_mono L (show i+1 ≤ n from hi)
  rcases hx with ⟨a,b⟩|⟨a,b⟩
  · exact ⟨(low i).trans a,b.trans_le (edge.trans high)⟩
  · exact ⟨(low _).trans ((Nat.le_add_right ..).trans a),b.trans_le (array_mono L hi)⟩

/-- At the very next pass only its input pointer and incidence bank can
overlap a previous payload. Every older successor already precedes it. -/
theorem cells_before_or_input {L : Layout} {i n x : ℕ} (hi : i < n) (hx : Cells L i x) :
    (levelsBase L ≤ x ∧ x < levelStart L n) ∨ GraphCells L n x := by
  have low := (cells_interval hi hx).1
  rcases hx with ⟨_,b⟩|h
  · exact Or.inl ⟨low,b.trans_le (levelStart_mono L hi)⟩
  · rcases eq_or_lt_of_le (show i+1 ≤ n from hi) with e|e
    · exact Or.inr (e ▸ h)
    · exact Or.inl ⟨low,h.2.trans_le ((array_before L _).trans (levelStart_mono L e))⟩

/-- A predicate describing the physical parser data of an actual selected
pass, with its chronological index available to compute physical addresses. -/
abbrev Data := ℕ → SelectedLevel B f hf → Memory w → Prop

/-- Store actual producing memory images, preserving the physical words
needed to recover each pass's data in the terminal memory. -/
def Past (L : Layout) (data : Data (w := w) B f hf) (past : List (SelectedLevel B f hf)) (m : Memory w) : Prop :=
  ∀ i : Fin past.length, ∃ source, data i.val past[i] source ∧ Agree (Cells L i.val) source m

variable {B f hf} {L : Layout} {data : Data (w := w) B f hf} {past : List (SelectedLevel B f hf)}
variable {m m' : Memory w} {v : SelectedLevel B f hf}

theorem Past.empty : Past B f hf L data [] m := fun i => Fin.elim0 i

/-- Recover a stable physical predicate from its producing snapshot. -/
theorem Past.atLevel (h : Past B f hf L data past m) (i : Fin past.length)
    (stable : ∀ source, data i.val past[i] source → Agree (Cells L i.val) source m → data i.val past[i] m) :
    data i.val past[i] m := by
  obtain ⟨source,p,agree⟩ := h i
  exact stable source p agree

theorem Past.transfer (h : Past B f hf L data past m)
    (frame : ∀ x, levelsBase L ≤ x → x < arrayBase L past.length → m' x = m x) :
    Past B f hf L data past m' := by
  intro i
  obtain ⟨source,p,same⟩ := h i
  refine ⟨source,p,fun x hx => ?_⟩
  obtain ⟨lo,hi⟩ := cells_interval i.isLt hx
  exact (same x hx).trans (frame x lo hi).symm

/-- Capture the completed level and retain the selected parser data for
every older occurrence, including the immediately preceding output graph. -/
theorem Past.append (h : Past B f hf L data past m)
    (emitted : data past.length v m')
    (older : ∀ x, levelsBase L ≤ x → x < levelStart L past.length → m' x = m x)
    (input : Agree (GraphCells L past.length) m m') :
    Past B f hf L data (past++[v]) m' := by
  intro j
  by_cases old : j.val < past.length
  · obtain ⟨source,p,same⟩ := h ⟨j.val,old⟩
    simp only [Fin.getElem_fin,List.getElem_append_left old]
    refine ⟨source,p,fun x hx => (same x hx).trans ?_⟩
    rcases cells_before_or_input old hx with ⟨lo,hi⟩|live
    · exact (older x lo hi).symm
    · exact input x live
  · have bound : j.val < past.length+1 := by simpa using j.isLt
    have eqn : j.val = past.length := by omega
    simp only [Fin.getElem_fin]
    rw [List.getElem_concat_length eqn j.isLt,eqn]
    exact ⟨m',emitted,fun _ _ => rfl⟩

/-- Footprints of native worker batches may include scheduler addresses,
input scalars, input scratch, and any successor data. -/
theorem Past.append_reports (h : Past B f hf L data past m) (rs : List (Report w))
    (emitted : data past.length v (after m (eventLog rs)))
    (writes : Writes (fun x => x < levelsBase L ∨
      (levelStart L past.length ≤ x ∧ x < levelStart L past.length+L.shape.scalarFields) ∨
      arrayBase L past.length ≤ x) (eventLog rs)) :
    Past B f hf L data (past++[v]) (after m (eventLog rs)) := by
  apply h.append emitted
  · intro x lo hi
    have lower : levelStart L past.length ≤ arrayBase L past.length := by unfold arrayBase incidenceStart; omega
    exact after_outside m writes (by omega)
  · intro x hx
    have lo : levelsBase L ≤ levelStart L past.length := Nat.le_add_right ..
    exact (after_outside m writes (by obtain ⟨a,b⟩ := hx; omega)).symm

section Refresh

open Compression.Refresh Compression.DegreeRefresh SpectralGeometry PortRefresh PortRefresh.Allocation

variable {a a₀ g dH t i : ℕ} {K K' : ℝ} {X : State a (a+g)}
variable {E : RegularArcGraph (Fin (2^a)) dH} {hdH : 0 < dH}
variable {conn : (arcSupportGraph E.multiplicity).Connected}
variable {F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K'}
variable {choice : DyadicRefreshChoice X E hdH conn F} {ties : Fin t ≃ Tie (2^a)} {start stride : ℕ}

/-- Recover the native refresh builder's segment rows, term records and
dense demands from the historical snapshot of the selected occurrence. -/
theorem refresh_stored {fit : Fintype.card X.Base*2^a*2^g*2^a ≤ 2^w}
    (stored : PortRefresh.Build.Stored X E hdH conn F choice ties start stride fit m)
    (wide : 2+2^a*dH ≤ stride) (room : (plan X a₀ dH t stride start).stop ≤ 2^w)
    (lower : levelStart L i ≤ start)
    (upper : (plan X a₀ dH t stride start).supply ≤ levelStart L (i+1))
    (same : Agree (Cells L i) m m') :
    PortRefresh.Build.Stored X E hdH conn F choice ties start stride fit m' :=
  stored.transfer wide room (fun x lo hi => (same x (Or.inl ⟨lower.trans lo,hi.trans_le upper⟩)).symm)

end Refresh
end CompressorRecords.SelectedPayloadHistory

end VPVNP
end Computability
end OAI
