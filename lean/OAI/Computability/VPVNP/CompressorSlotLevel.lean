import OAI.Computability.VPVNP.CompressorSlotPipeline
import OAI.Computability.VPVNP.CompressorSlotOwnerDirectory
import OAI.Computability.VPVNP.CompressorSlotBaseScan

/-!
# The shrinking level's slot directory

The current level supplies the old-arc records, the chosen layout's role
table, the fixed subdivision counts and the cyclic tag-successor table.
From the current level counts one computes all five native pass frames.
The last two arrays are the next graph's base-slot matching and displacement.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotLevel

open Compression Compression.PackingData Compression.SurvivingSlots Slots SlotSchedule SlotOwners
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

/-- Counts at a shrinking level. The four subdivisions are chosen for the new degree. -/
structure Shape where
  /-- Number of old base vertices whose tags form the next level's packed base vertices. -/
  bases : ℕ
  /-- Number of tag values per old base vertex in the packed graph. -/
  tags : ℕ
  /-- Number of residual lanes over each packed base vertex. -/
  lanes : ℕ
  /-- Degree of the input slot graph used to enumerate the old arc records. -/
  oldDegree : ℕ
  /-- Number of bits in an old position's color mask. -/
  colors : ℕ
  /-- Number of surviving subdivisions for each of the four role edge types. -/
  subdivisions : Fin 4 → ℕ
  /-- Target degree of the next graph after padding with dummy slots. -/
  newDegree : ℕ

/-- Source tables selected by the current branch and the start of fresh scratch space. -/
structure Heads where
  /-- Start of the old arc records containing three role sites and a CD indicator for each arc. -/
  oldArc : ℕ
  /-- Start of the eight-entry table selecting a source and target role for each edge type. -/
  role : ℕ
  /-- Start of the four published subdivision counts indexed by edge type. -/
  subdivisions : ℕ
  /-- Start of the table of cyclic tag successors used to choose dummy target sites. -/
  nextSite : ℕ
  /-- First fresh word for constructing the endpoint owner, count, row, and inverse tables. -/
  scratch : ℕ

variable (s : Shape) (h : Heads)

/-- Number of packed sites across all base vertices, tags, and residual lanes. -/
def sites := s.bases*(s.tags*s.lanes)
/-- Number of dummy slots per packed site needed to bring the surviving degree up to the new
degree. -/
def pad := s.newDegree-survivingDegree s.oldDegree s.colors s.subdivisions

/-- Number of endpoint fields scanned in the genuine candidate range, counting both ends even
for candidates that decode to holes. -/
def genuineCount := (keyCount s.bases s.tags s.oldDegree s.colors s.subdivisions * s.lanes)*2
/-- Number of endpoint fields in the dummy range, two per padding slot at every packed site. -/
def dummyCount := (sites s * pad s)*2
/-- Total number of absolute endpoint field addresses in the genuine candidate and dummy
ranges. -/
def fields := RecordCount s.bases s.tags s.lanes s.oldDegree s.colors (pad s) s.subdivisions*2
/-- Number of real endpoint owners, with separate outgoing and incoming rows at each packed
site. -/
def owners := sites s*2
/-- Number of outgoing slots over packed base vertices, before lifting the matching to residual
lanes. -/
def baseArcs := s.bases*s.tags*s.newDegree

/-- First word of the rectangular endpoint rows, after the field owner column and all append
counters. -/
def rowsHead := h.scratch+fields s+(owners s+fields s)
/-- Start of the table mapping absolute field IDs back to rectangular slots, after the reserved
row space. -/
def inverseHead := rowsHead s h+(owners s+fields s)*s.newDegree
/-- Start of the base-target column, immediately after the inverse field table. -/
def targetsHead := inverseHead s h+fields s
/-- Start of the base arc displacement column, immediately after the base targets. -/
def shiftsHead := targetsHead s h+baseArcs s
/-- First free address after the base-target and displacement columns built by the five slot
passes. -/
def stopAddress := shiftsHead s h+baseArcs s

theorem counts_add : genuineCount s+dummyCount s = fields s := by
  dsimp [genuineCount,dummyCount,sites,fields,RecordCount]; ring

/-- Pass order used by the descriptor controller. -/
inductive Phase where
  | genuineOwners | dummyOwners | appendFields | invertFields | baseMatching
  deriving DecidableEq

/-- Exclusive cursor stop for the selected owner, append, inverse, or base-matching scan. -/
def limit : Phase → ℕ
  | .genuineOwners => genuineCount s
  | .dummyOwners => dummyCount s
  | .appendFields => fields s
  | .invertFields => owners s*s.newDegree
  | .baseMatching => baseArcs s

/-- Number of public parameter words required by the worker for each slot phase. -/
abbrev arity : Phase → ℕ
  | .genuineOwners => 8
  | .dummyOwners => 3
  | .appendFields | .baseMatching => 6
  | .invertFields => 2

/-- The five public banks. Each worker starts its own cursor at zero. -/
def bank (w : ℕ) : (phase : Phase) → Fin (arity phase) → Word w
  | .genuineOwners => (Fin.ofNat (2^w)) ∘ ![s.lanes, ∑ t, s.subdivisions t,
      oldBaseArcCount s.bases s.tags s.oldDegree s.colors, h.oldArc, h.role, h.subdivisions, owners s, h.scratch]
  | .dummyOwners => (Fin.ofNat (2^w)) ∘ ![pad s, h.nextSite, h.scratch+genuineCount s]
  | .appendFields => SlotSchedule.parameters w h.scratch (fields s) (owners s) s.newDegree
  | .invertFields => SlotSchedule.scatterParameters w h.scratch (fields s) (owners s) s.newDegree
  | .baseMatching => (Fin.ofNat (2^w)) ∘ ![s.newDegree,s.lanes,rowsHead s h,inverseHead s h,targetsHead s h,shiftsHead s h]

/-- The controller row begins with the dispatch tag, initial cursor and exclusive stop. -/
def frame {w : ℕ} (tag : Phase → Word w) (phase : Phase) : List (Word w) :=
  tag phase :: 0 :: Fin.ofNat _ (limit s phase) :: List.ofFn (bank s h w phase)

variable {V H Tag L : Type*} {d c N J nL degree w : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- Assemble the array-scan input from the paper's actual selected role and
original-arc words, using only the four numerical input-region bounds. -/
theorem input_of_tables (layout : Bool) (mem : Memory w) (h : Heads) :
    let s : Shape := ⟨N,J,nL,d,c,subdiv,degree⟩
    let g := bank s h w .genuineOwners
    let p := bank s h w .dummyOwners
    let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad s)
    GenuineTables P subdiv vertices tags lanes layout g mem → DummyTables vertices tags lanes (pad s) p mem →
    h.oldArc+4*(oldBaseArcCount N J d c*nL) ≤ h.scratch → h.role+8 ≤ h.scratch →
    h.subdivisions+4 ≤ h.scratch → h.nextSite+sites s ≤ h.scratch → stopAddress s h < 2^w →
    OwnerInput D g p mem h.scratch (genuineCount s) (dummyCount s) := by
  intro s g p D hg hp hold hrole hsub hnext fit
  have hstop : h.scratch+fields s ≤ stopAddress s h := by
    unfold stopAddress shiftsHead targetsHead inverseHead rowsHead; omega
  have hf : h.scratch+fields s < 2^w := hstop.trans_lt fit
  have counts := counts_add s
  have start : (g 7).val = h.scratch := Nat.mod_eq_of_lt (by omega : h.scratch < 2^w)
  have startD : (p 2).val = h.scratch+genuineCount s := Nat.mod_eq_of_lt (by omega : h.scratch+genuineCount s < 2^w)
  have old : (g 3).val = h.oldArc := Nat.mod_eq_of_lt (by omega : h.oldArc < 2^w)
  have role : (g 4).val = h.role := Nat.mod_eq_of_lt (by omega : h.role < 2^w)
  have sub : (g 5).val = h.subdivisions := Nat.mod_eq_of_lt (by omega : h.subdivisions < 2^w)
  have next : (p 1).val = h.nextSite := Nat.mod_eq_of_lt (by omega : h.nextSite < 2^w)
  refine ⟨counts,start,startD,?_,?_,?_,?_⟩
  · intro i hi a ha; rw [← start]
    exact genuineInputs_before P subdiv vertices tags lanes hg (g 7)
      (by rw [old,start]; exact hold) (by rw [role,start]; exact hrole) (by rw [sub,start]; exact hsub) i hi a ha
  · intro i hi; rw [← start]
    exact dummyInput_before vertices tags lanes hp (g 7) (by rw [next,start]; exact hnext) i hi
  · intro i hi
    exact genuine_directory P subdiv vertices tags lanes layout g mem hg (Fin.ofNat _ i) ((Nat.mod_le ..).trans_lt hi)
  · intro i hi
    have hv : (Fin.ofNat (2^w) i).val = i := Nat.mod_eq_of_lt (by omega)
    have h := dummy_directory P subdiv vertices tags lanes (pad := pad s) layout p mem hp (Fin.ofNat _ i)
      ((Nat.mod_le ..).trans_lt hi) (by change fields s ≤ _; omega)
    rw [hv] at h
    exact h

end CompressorRecords.SlotLevel

end VPVNP
end Computability
end OAI
