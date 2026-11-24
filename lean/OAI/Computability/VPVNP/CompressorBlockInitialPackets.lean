import OAI.Computability.VPVNP.CompressorBlockCursorPacket
import OAI.Computability.VPVNP.CompressorBlockRoleZero

/-!
# The four chronological source visits at level zero

The scalar publisher, array-head publisher, cursor scan and role store run
in order. The source trace certifies each visit's stop test and memory
footprint, and leaves the initial cursor incidence and persistent metadata
available even when the block count is zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockInitialPackets

open BurstRAM BlockPlanner DescriptorSpace CursorNetwork BlockHeaderRun BlockHeaderStartup
open scoped Fin.CommRing

variable {w : ℕ}

/-- The four level-zero visits in execution order, ending with the store of the cursor role. -/
def order (L : Layout) (a : ℕ) : List BlockPlanner.Visit :=
  BlockHeaderPlan.initial L.shape a ++ [BlockRoleZero.visit]

/-- The initial scalar report and the following pointer report evaluated in its post-memory. -/
def headLogs (L : Layout) (a : ℕ) (m : Memory w) : List (Report w) :=
  let first := header w L 0
  [scalarReport (Scalars.initialRow (.terminal a)) (first+6) first m,
    headReport L 0 (initialMemory a L m)]

/-- The cursor scan reports that populate the six incidence columns beginning at level zero's
incidence base. -/
def cursorLogs (L : Layout) (w a b l width : ℕ) : List (Report w) :=
  let p := CursorRAM.publicWords w b l a width (incidenceStart L 0)
  CursorRAM.scanReports p 0 (CursorRAM.rowCount b l a)

/-- The full level-zero report sequence for header publication, the cursor scan and the final
role store. -/
def logs (L : Layout) (a b l width : ℕ) (m : Memory w) : List (Report w) :=
  headLogs L a m ++ cursorLogs L w a b l width ++ [BlockRoleZero.report w L]

/-- External memory after all four level-zero source visits. -/
def post (L : Layout) (a b l width : ℕ) (m : Memory w) :=
  after m (eventLog (logs L a b l width m))

/-- A fixed native clock bound for every source call in this prefix. -/
def clock (L : Layout) (a : ℕ) :=
  (Scalars.initialRow (.terminal a)).recipe.code.length + (DescriptorHeads.publisher L.shape).recipe.code.length +
    CursorRAM.visit.length + 8

/-- A source visit runs on the supplied operands and branch tapes within the initial packet
clock, producing the given reports. -/
def Source (L : Layout) (a : ℕ) (pub : Fin 5 → Word w) (s : Word w) (v : BlockPlanner.Visit)
    (m : Memory w) (rs : List (Report w)) : Prop :=
  ∃ fuel bits, fuel ≤ clock L a ∧ HeaderPacket.Run L pub s v m rs fuel bits

private theorem head_after (L : Layout) (a : ℕ) (m : Memory w) :
    after m (eventLog (headLogs L a m)) = initialFinal a L m := by
  simp only [headLogs,eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil,after,List.foldl_append]
  rfl

private theorem role_run (L : Layout) (pub : Fin 5 → Word w) (m : Memory w) (fit : levelStart L 0+27 < 2^w) :
    HeaderPacket.Run L pub (header w L 0) BlockRoleZero.visit m [BlockRoleZero.report w L] 7 [[]] := by
  obtain ⟨start,stop,native,_,_,_,reads⟩ := BlockRoleZero.run L pub m
  change BlockRoleZero.visit.initial.eval pub (header w L 0) m = 0 at start
  change BlockRoleZero.visit.stop.eval pub (header w L 0) m = 1 at stop
  apply HeaderPacket.singleton (by decide) (by
    unfold rawCall
    dsimp only
    rw [start]; exact native)
  · rw [start,stop]
    change 0 % 2^w < 1 % 2^w
    rw [Nat.zero_mod,Nat.mod_eq_of_lt (by omega : 1 < 2^w)]; decide
  · rw [stop]; rfl
  · intro x v h
    exact (reads x v h).elim
  · intro x v h
    have hrole : x = BlockRoleZero.role w L ∧ v = 0 := by simpa [BlockRoleZero.report] using h
    rw [hrole.1]
    change levelStart L 0 ≤ (levelStart L 0+27)%2^w
    rw [Nat.mod_eq_of_lt fit]
    omega

open private fit_fields from OAI.Computability.VPVNP.CompressorBlockHeaderRun

open Compression in
theorem initial {a b l pad : ℕ} {T : Type} [Fintype T] (L : Layout) (n : ℕ) (base : Word w)
    (m : Memory w) (hD : 1 < b+l) (hd : 2+pad = 2^a) (bits : T → ℕ)
    (ready : BlockHeaderStartup.Ready L a b l (∑ t, bits t) n base m)
    (fields : 30 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (room : incidenceStart L 0+6*CursorRAM.rowCount b l a ≤ 2^w) (width : (∑ t, bits t) < 2^w) :
    let W := ∑ t, bits t
    let pub := (Workspace.ports L.shape.arity base).data
    let s := header w L 0
    let X := cursorState (cursorCoordinateLabels b l) hD hd bits
    let out := post L a b l W m
    SourceWalk (Source L a pub s) (order L a) m (logs L a b l W m) ∧
      (packedIncidence L w 0 (CursorRAM.rowCount b l a)).Represents X out ∧
      out (levelStart L 0+27) = 0 ∧
      (∀ x, x < incidenceStart L 0 → x ≠ levelStart L 0+27 → out x = initialFinal a L m x) ∧
      (out (levelStart L 0+14)).val = endAddress L ∧
      (out (levelStart L 0+28)).val = L.levels ∧ (out (levelStart L 0+29)).val = n := by
  intro W pub s X out
  let mid := initialMemory a L m
  let afterHeads := initialFinal a L m
  let cs := cursorLogs L w a b l W
  let afterCursor := after afterHeads (eventLog cs)
  let role := BlockRoleZero.report w L
  let z : Fin L.levels := ⟨0,ready.nonempty⟩
  have fieldsFit := fit_fields L z fit
  change levelStart L 0+L.shape.scalarFields < 2^w at fieldsFit
  have roleFit : levelStart L 0+27 < 2^w := by omega
  have before : levelStart L 0+27 < incidenceStart L 0 := by unfold incidenceStart levelHeaderWords; omega
  obtain ⟨first,second⟩ := HeaderPacket.initial ready.initial (by omega) fit pub s (ready.first s) ready.count_before
  obtain ⟨cursor,rep,kept,_,_⟩ := BlockCursorPacket.run L n base m s hD hd bits ready room width
  have roleRun := role_run L pub afterCursor roleFit
  let firstLog := scalarReport (Scalars.initialRow (.terminal a)) (s+6) s m
  let headLog := headReport L 0 mid
  have headWalk : SourceWalk (Source L a pub s) [BlockHeaderPlan.initialScalars a,
      BlockHeaderPlan.heads L.shape BlockHeaderPlan.firstHeader] m (headLogs L a m) := by
    apply SourceWalk.next (rs := [firstLog]) (ts := [headLog]) ⟨_,_,by unfold clock; omega,first⟩
    simp only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    exact SourceWalk.singleton ⟨_,_,by unfold clock; omega,second⟩
  have tailWalk : SourceWalk (Source L a pub s) [BlockPlanner.cursor BlockHeaderPlan.persistentFrame,BlockRoleZero.visit]
      afterHeads (cs++[role]) := by
    apply SourceWalk.next (rs := cs) (ts := [role]) ⟨_,_,by unfold clock; omega,cursor⟩
    exact SourceWalk.singleton ⟨_,_,by unfold clock; omega,roleRun⟩
  have eqn : out = writeMemory afterCursor (BlockRoleZero.role w L) 0 := by
    change after m (eventLog ((headLogs L a m++cs)++[role])) = _
    rw [SourceWalk.after_append,SourceWalk.after_append,head_after]
    simp only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rfl
  have val : (BlockRoleZero.role w L).val = levelStart L 0+27 := Nat.mod_eq_of_lt roleFit
  have keep (x : ℕ) (below : x < incidenceStart L 0) (other : x ≠ levelStart L 0+27) : out x = afterHeads x := by
    rw [eqn,writeMemory,val,ite_eq_right other]
    exact kept x (.inl below)
  have slots : IncidenceDirectory.slotCount X = CursorRAM.rowCount b l a := by
    change Fintype.card (Fin (b+l) × Compression.BitWord b)*2^l*2^a = ((b+l)*2^b*2^l)*2^a
    rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_congr (Compression.bitWordFinEquiv b),Fintype.card_fin]
  have rep' : (packedIncidence L w 0 (CursorRAM.rowCount b l a)).Represents X afterCursor := rep
  refine ⟨?_,?_,?_,keep,?_,?_,?_⟩
  · change SourceWalk _ ([_,_]++[_,_]) m (headLogs L a m++cs++[role])
    rw [List.append_assoc]
    apply headWalk.append
    rwa [head_after]
  · rw [eqn]
    exact BlockRoleZero.preserve L X _ afterCursor rep' slots.le room before
  · rw [eqn,writeMemory,val,ite_eq_left rfl]
  · rw [keep _ (by omega) (by omega)]; exact ready.arena
  · rw [keep _ (by unfold incidenceStart levelHeaderWords; omega) (by omega)]; exact ready.levels
  · rw [keep _ (by unfold incidenceStart levelHeaderWords; omega) (by omega)]; exact ready.length

/-- Every data call in the initial segment consumes the empty choice string. -/
theorem quiet (L : Layout) (a b l width : ℕ) (m : Memory w) :
    ∀ r ∈ logs L a b l width m, choiceBits r.events = [] := by
  intro r hr
  rcases List.mem_append.mp hr with h|h
  · rcases List.mem_append.mp h with h|h
    · rcases List.mem_cons.mp h with rfl|h
      · exact (RowRecipe.report_cost ..).2.2
      · obtain rfl := List.mem_singleton.mp h
        exact (RowRecipe.report_cost ..).2.2
    · let p := CursorRAM.publicWords w b l a width (incidenceStart L 0)
      let N := CursorRAM.rowCount b l a
      have paths := ((runSegment_iff ..).mp (CursorRAM.scan_native p 0 N m)).2.2
      have each : choiceBits r.events ∈ branchPaths (CursorRAM.scanReports p 0 N) := List.mem_map.mpr ⟨r,h,rfl⟩
      rw [paths] at each
      exact (List.mem_replicate.mp each).2
  · obtain rfl := List.mem_singleton.mp h
    rfl

end CompressorRecords.BlockInitialPackets

end VPVNP
end Computability
end OAI
