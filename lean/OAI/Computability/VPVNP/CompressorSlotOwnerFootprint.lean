import OAI.Computability.VPVNP.CompressorSlotLevelRun
import OAI.Computability.VPVNP.CompressorRecordsOrdinalFootprint
import OAI.Computability.VPVNP.RAMChoicePrefix

/-!
# External addresses touched by the endpoint-owner scans

The genuine scan reads from the old arc, selected role and subdivision
tables, then writes the genuine prefix of the owner stream. The dummy scan
reads the cyclic successor table and writes the trailing dummy fields. The
bounds apply to the emitted probes of every call in the two native segments.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotOwnerFootprint

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SourceTransport SlotLevel Slots
open Compression Compression.PackingData

variable {w : ℕ}

/-- A half-open external array of the given length. -/
def interval (base count addr : ℕ) : Prop := base ≤ addr ∧ addr < base+count

/-- Size in words of the old arc record table, with three role sites and a CD flag per absolute
old arc. -/
def oldWords (s : Shape) := 4*(oldBaseArcCount s.bases s.tags s.oldDegree s.colors*s.lanes)

/-- Addresses in the old arc, role, or subdivision tables that the genuine owner scan may read. -/
def genuineRead (s : Shape) (h : Heads) (addr : ℕ) : Prop :=
  interval h.oldArc (oldWords s) addr ∨ interval h.role 8 addr ∨ interval h.subdivisions 4 addr

/-- The cyclic successor table range read by the dummy endpoint owner scan. -/
def dummyRead (s : Shape) (h : Heads) := interval h.nextSite (sites s)

/-- The leading scratch interval that receives owner words for genuine candidate fields. -/
def genuineWrite (s : Shape) (h : Heads) := interval h.scratch (genuineCount s)

/-- The trailing owner interval, immediately after the genuine fields, that receives owner
words for dummy fields. -/
def dummyWrite (s : Shape) (h : Heads) := interval (h.scratch+genuineCount s) (dummyCount s)

private theorem genuine_event_addresses (g : Fin 8 → Word w) (m : Memory w) (i : Word w) :
    (∀ a v, Event.read a v ∈ SlotOwners.genuineEvents g m i → a ∈ SlotOwners.genuineInputs g m i) ∧
      (∀ a v, Event.write a v ∈ SlotOwners.genuineEvents g m i → a = g 7+i) := by
  constructor
  · intro a v hv
    simp [SlotOwners.genuineEvents] at hv
    simp only [SlotOwners.genuineInputs, List.mem_cons]
    rcases hv with h | h | h | h <;> tauto
  · intro a v hv
    simp [SlotOwners.genuineEvents] at hv
    exact hv.1

private theorem dummy_event_addresses (p : Fin 3 → Word w) (m : Memory w) (i : Word w) :
    (∀ a v, Event.read a v ∈ SlotOwners.dummyEvents p m i → a = p 1+SlotOwners.dummySource p i) ∧
      (∀ a v, Event.write a v ∈ SlotOwners.dummyEvents p m i → a = p 2+i) := by
  constructor <;> intro a v hv <;> simp [SlotOwners.dummyEvents] at hv <;> exact hv.1

private theorem word_inc (i : ℕ) :
    Fin.ofNat (2^w) i + 1 = Fin.ofNat _ (i+1) := by
  apply Fin.ext
  simp [Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]

private theorem owner_end (s : Shape) (h : Heads) : h.scratch+fields s ≤ stopAddress s h := by
  dsimp [stopAddress, shiftsHead, targetsHead, inverseHead, rowsHead]; omega

/-- For the exact native genuine run, every emitted read and write lies in its
declared physical array. Its eight role offsets remain bounded across the scan. -/
theorem genuine (s : Shape) (h : Heads) (initial : Memory w) (rs : List (Report w))
    (arcEnd : h.oldArc+oldWords s ≤ h.scratch) (roleEnd : h.role+8 ≤ h.scratch)
    (subEnd : h.subdivisions+4 ≤ h.scratch) (fit : stopAddress s h < 2^w) :
    let g := bank s h w .genuineOwners
    let P := ((template SlotOwners.genuine 0).instantiate w g).program
    (g 0).val = s.lanes → (g 1).val = ∑ t, s.subdivisions t →
    (g 2).val = oldBaseArcCount s.bases s.tags s.oldDegree s.colors →
    (∀ j < 8, (initial (h.role+j)).val < 3) →
    runSegment P 49 (some 0) initial (List.replicate (genuineCount s) []) = some rs →
    Reads (genuineRead s h) (eventLog rs) ∧ Writes (genuineWrite s h) (eventLog rs) := by
  intro g P lanes sub bases roles run
  have room := (owner_end s h).trans_lt fit
  have both := counts_add s
  have g3 : (g 3).val = h.oldArc := Nat.mod_eq_of_lt (by omega : h.oldArc < 2^w)
  have g4 : (g 4).val = h.role := Nat.mod_eq_of_lt (by omega : h.role < 2^w)
  have g5 : (g 5).val = h.subdivisions := Nat.mod_eq_of_lt (by omega : h.subdivisions < 2^w)
  have g7 : (g 7).val = h.scratch := Nat.mod_eq_of_lt (by omega : h.scratch < 2^w)
  let cursor (j : ℕ) := Fin.ofNat (2^w) j
  let inv (_ : ℕ) (m : Memory w) := ∀ j < 8, (m (h.role+j)).val < 3
  apply OrdinalRun.footprint P 49 cursor (genuineCount s) inv _ _ _ 0 _ initial rs (by simp) roles run
  intro j hj m hm bits rep hex
  have eq := (execute_prefix_unique (SlotOwners.genuine_native g m (cursor j))
    (show execute P 49 (P.start (cursor j)) m ([]++bits) = some rep from hex)).2
  subst rep
  have hc : (cursor j).val = j := Nat.mod_eq_of_lt (by omega)
  have hi : (cursor j).val < 4*(g 2).val*(g 1).val*(g 0).val*2 := by
    rw [hc, bases, sub, lanes]
    simpa only [genuineCount, keyCount, oldBaseArcCount, Nat.mul_assoc] using hj
  have within := SlotOwners.genuine_inputs_ranges g m (cursor j)
    (by rw [g3,bases,lanes]; change h.oldArc+oldWords s ≤ _; omega)
    (by rw [g4]; omega) (by rw [g5]; omega) (by simpa only [g4] using hm) hi
  have ha : (g 7+cursor j).val = h.scratch+j := by
    rw [Fin.val_add,g7,hc,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨rd,wr⟩ := genuine_event_addresses g m (cursor j)
  have writes : Writes (genuineWrite s h) (SlotOwners.genuineEvents g m (cursor j)) := by
    intro a v hv
    change h.scratch ≤ a.val ∧ a.val < h.scratch+genuineCount s
    rw [wr a v hv,ha]; omega
  refine ⟨congrArg some (word_inc j), ?_, ?_, writes⟩
  · intro k hk
    rw [after_outside m writes (by change ¬ (h.scratch ≤ h.role+k ∧ _); omega)]
    exact hm k hk
  · intro a v hv
    simpa only [g3,g4,g5,bases,lanes,genuineRead,interval,oldWords] using within a (rd a v hv)

/-- Every dummy call reads its source site's cyclic successor, even when
the selected side is the outgoing end. Its write lies in the dummy suffix. -/
theorem dummy (s : Shape) (h : Heads) (initial : Memory w) (rs : List (Report w))
    (nextEnd : h.nextSite+sites s ≤ h.scratch) (fit : stopAddress s h < 2^w)
    (hw : 2 < 2^w) :
    let p := bank s h w .dummyOwners
    let P := ((template SlotOwners.dummy 0).instantiate w p).program
    (p 0).val = pad s →
    runSegment P 20 (some 0) initial (List.replicate (dummyCount s) []) = some rs →
    Reads (dummyRead s h) (eventLog rs) ∧ Writes (dummyWrite s h) (eventLog rs) := by
  intro p P padding run
  have room := (owner_end s h).trans_lt fit
  have both := counts_add s
  have p1 : (p 1).val = h.nextSite := Nat.mod_eq_of_lt (by omega : h.nextSite < 2^w)
  have p2 : (p 2).val = h.scratch+genuineCount s :=
    Nat.mod_eq_of_lt (by omega : h.scratch+genuineCount s < 2^w)
  let cursor (j : ℕ) := Fin.ofNat (2^w) j
  apply OrdinalRun.footprint P 20 cursor (dummyCount s) (fun _ _ => True) _ _ _ 0 _
    initial rs (by simp) trivial run
  intro j hj m _ bits rep hex
  have eq := (execute_prefix_unique (SlotOwners.dummy_native p m (cursor j))
    (show execute P 20 (P.start (cursor j)) m ([]++bits) = some rep from hex)).2
  subst rep
  have hc : (cursor j).val = j := Nat.mod_eq_of_lt (by omega)
  have within := SlotOwners.dummy_input_range p (cursor j) (sites s) (by rw [p1]; omega) hw
    (by rw [hc,padding]; exact hj)
  have ha : (p 2+cursor j).val = h.scratch+genuineCount s+j := by
    rw [Fin.val_add,p2,hc,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨rd,wr⟩ := dummy_event_addresses p m (cursor j)
  refine ⟨congrArg some (word_inc j), trivial, ?_, ?_⟩
  · intro a v hv
    rw [rd a v hv]; simpa only [p1,dummyRead,interval] using within
  · intro a v hv
    change _ ≤ a.val ∧ a.val < h.scratch+genuineCount s+dummyCount s
    rw [wr a v hv,ha]; omega

variable {V H Tag L : Type*} {d c N J nL degree : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- Read and write footprints of the first two reports of a selected shrinking
level. They follow from the actual stored table representation at the level's
initial memory and the five native segments supplied by the level run. -/
theorem of_tables (layout : Bool) (h : Heads) (mem : Memory w) (rs : SlotLevel.Reports w) :
    let s : Shape := ⟨N,J,nL,d,c,subdiv,degree⟩
    SlotOwners.GenuineTables P subdiv vertices tags lanes layout (bank s h w .genuineOwners) mem →
    SlotOwners.DummyTables vertices tags lanes (pad s) (bank s h w .dummyOwners) mem →
    h.oldArc+oldWords s ≤ h.scratch → h.role+8 ≤ h.scratch → h.subdivisions+4 ≤ h.scratch →
    h.nextSite+sites s ≤ h.scratch → stopAddress s h < 2^w → rs.Native s h mem →
    (Reads (genuineRead s h) (eventLog rs.genuine) ∧ Writes (genuineWrite s h) (eventLog rs.genuine)) ∧
    (Reads (dummyRead s h) (eventLog rs.dummy) ∧ Writes (dummyWrite s h) (eventLog rs.dummy)) := by
  intro s hg hd ha hr hs hn fit run
  have rg : (bank s h w .genuineOwners 4).val = h.role :=
    Nat.mod_eq_of_lt (by have := (owner_end s h).trans_lt fit; omega : h.role < 2^w)
  have roles (j : ℕ) (hj : j < 8) : (mem (h.role+j)).val < 3 := by
    let t : Fin 4 := ⟨j/2, by omega⟩
    let side : Fin 2 := ⟨j%2, by omega⟩
    have ix : 2*t.val+side.val = j := by dsimp [t,side]; omega
    have hslot := hg.role t side
    rw [rg,ix] at hslot
    rw [hslot]; cases endRole layout (decide (side=1)) t <;> decide
  exact ⟨genuine s h mem rs.genuine ha hr hs fit hg.laneCount hg.subdivCount hg.baseCount roles run.1,
    dummy s h _ rs.dummy hn fit hd.twoFits hd.padCount run.2.1⟩

end CompressorRecords.SlotOwnerFootprint

end VPVNP
end Computability
end OAI
