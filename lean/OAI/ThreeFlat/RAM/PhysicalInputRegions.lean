import Mathlib.Tactic

namespace OAI
/-! # Disjoint RAM regions for preparing an H invocation from its paired bit tape -/

namespace ThreeFlat.RAM.PhysicalInputRegions

/-- Counts are natural addresses. An endpoint contains the two catalyst halves,
and multiplication words are included in the H footprint. -/
structure Size where
  endpoints : ℕ
  advice : ℕ
  parameters : ℕ
  footprint : ℕ
  expandedCells : ℕ
  localCells : ℕ
  ports : ℕ
  width : ℕ

namespace Size

variable (s : Size)

def rawParams := 2*s.endpoints+s.advice
def rawTable := s.rawParams+s.parameters
def packedWords := 11*(s.localCells+s.ports)
def rawCount := s.rawTable+s.width*s.packedWords
def parameterBase := s.footprint
def templateBase := s.parameterBase+s.parameters
def gateBase := s.templateBase+11*s.expandedCells
def portBase := s.gateBase+11*s.localCells
def packedEnd := s.portBase+11*s.ports
def scratch := max s.rawCount s.packedEnd
def limit := s.scratch+s.rawCount

theorem packedEnd_eq : s.packedEnd=s.gateBase+s.packedWords := by
  unfold packedEnd portBase packedWords
  omega

theorem scratch_after_raw : s.rawCount≤s.scratch := le_max_left _ _
theorem scratch_after_packed : s.packedEnd≤s.scratch := le_max_right _ _

theorem regions : s.footprint ≤ s.parameterBase ∧
    s.parameterBase+s.parameters ≤ s.templateBase ∧ s.templateBase+11*s.expandedCells ≤ s.gateBase ∧
    s.gateBase+11*s.localCells ≤ s.portBase ∧ s.portBase+11*s.ports ≤ s.scratch ∧
    s.rawCount ≤ s.scratch :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, s.scratch_after_packed,s.scratch_after_raw⟩

theorem fit (h : s.limit<2^s.width) :
    s.footprint<2^s.width ∧ s.gateBase<2^s.width ∧ s.packedEnd<2^s.width ∧
    s.scratch+s.rawTable+s.width*s.packedWords<2^s.width := by
  obtain ⟨a,b,c,d,e,_⟩ := s.regions
  change s.scratch+s.rawCount<2^s.width at h
  have endEq := s.packedEnd_eq
  have aft := s.scratch_after_packed
  unfold rawCount at h
  omega

/-- The reservation is linear in the expanded template and H workspace. Only the
two polynomial local tables pay the input bit-packing factor. -/
theorem limit_le : s.limit ≤ s.footprint+s.parameters+11*s.expandedCells+s.packedWords+2*s.rawCount := by
  unfold limit scratch
  rw [s.packedEnd_eq]
  unfold gateBase templateBase parameterBase
  omega

end Size

end ThreeFlat.RAM.PhysicalInputRegions

end OAI
