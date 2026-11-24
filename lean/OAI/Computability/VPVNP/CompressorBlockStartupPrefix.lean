import OAI.Computability.VPVNP.CompressorBlockInitialPackets

/-!
# The level-zero source prefix from physical startup data

At each sufficiently large length the saved cursor operands come from the
eight linked startup stages. The four initial descriptor workers produce
the typed cursor graph, preserve all eight operands, and publish the
terminal six scalars used by the first selected substep.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockStartupPrefix

open BurstRAM BlockPlanner CursorBounds DescriptorSpace CursorNetwork BlockHeaderRun
open scoped Fin.CommRing
open private address_val fit_fields from OAI.Computability.VPVNP.CompressorBlockHeaderRun

variable {w : ℕ}

open Compression in
/-- The level-zero startup reports execute and leave the packed cursor graph and its persistent
metadata in memory. -/
structure Resident (L : Layout) (a b l width n : ℕ) (base : Word w) (m : Memory w) (X : State a l) : Prop where
  walk : SourceWalk (BlockInitialPackets.Source L a (Workspace.ports L.shape.arity base).data (header w L 0))
    (BlockInitialPackets.order L a) m (BlockInitialPackets.logs L a b l width m)
  rows : IncidenceDirectory.slotCount X = CursorRAM.rowCount b l a
  room : incidenceStart L 0 + 6*CursorRAM.rowCount b l a ≤ 2^w
  incidenceHeads : ∀ c : Fin 6, BlockInitialPackets.post L a b l width m (incidenceHead L 0 c) =
    (incidenceBase L 0 (CursorRAM.rowCount b l a) c : Word w)
  tableHeads : ∀ j : Fin L.shape.tables, BlockInitialPackets.post L a b l width m (tableHead L 0 j) =
    (tableBase L 0 j : Word w)
  incidence : (packedIncidence L w 0 (CursorRAM.rowCount b l a)).Represents X (BlockInitialPackets.post L a b l width m)
  scalars : Scalars.Present (.terminal a) ((b+l)*2^b) l (header w L 0) (BlockInitialPackets.post L a b l width m)
  frame : Frame.data (header w L 0+6) (BlockInitialPackets.post L a b l width m) =
    CursorRAM.ScheduleInit.inputs (CursorRAM.encode w (directoryBase L)) (CursorRAM.encode w 1) b l a width
      (incidenceStart L 0)
  role : BlockInitialPackets.post L a b l width m (levelStart L 0+27) = 0
  arena : (BlockInitialPackets.post L a b l width m (levelStart L 0+14)).val = endAddress L
  levels : (BlockInitialPackets.post L a b l width m (levelStart L 0+28)).val = L.levels
  length : (BlockInitialPackets.post L a b l width m (levelStart L 0+29)).val = n
  positions : ((b+l)*2^b)*2^l = L.positions

/-- All fields consumed by the following pass are recovered on a live
memory agreeing with the raw output above the first level header. This
includes the incoming and outgoing columns at their computed indices. -/
theorem Resident.live {L : Layout} {a b l width n : ℕ} {base : Word w} {m : Memory w}
    {X : Compression.State a l} (resident : Resident L a b l width n base m X) (live : Memory w)
    (agree : SourceTransport.Agree (levelStart L 0 ≤ ·) (BlockInitialPackets.post L a b l width m) live)
    (nonempty : 0 < L.levels) (fields : 14 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w) :
    let N := CursorRAM.rowCount b l a
    (packedIncidence L w 0 N).Represents X live ∧
      Scalars.Present (.terminal a) ((b+l)*2^b) l (header w L 0) live ∧
      Frame.data (header w L 0+6) live =
        CursorRAM.ScheduleInit.inputs (CursorRAM.encode w (directoryBase L)) (CursorRAM.encode w 1) b l a width
          (incidenceStart L 0) ∧
      (∀ c : Fin 6, live (incidenceHead L 0 c) = (incidenceBase L 0 N c : Word w)) ∧
      (∀ j : Fin L.shape.tables, live (tableHead L 0 j) = (tableBase L 0 j : Word w)) ∧
      live (levelStart L 0+27) = 0 ∧ (live (levelStart L 0+14)).val = endAddress L ∧
      (live (levelStart L 0+28)).val = L.levels ∧ (live (levelStart L 0+29)).val = n := by
  intro N
  let raw := BlockInitialPackets.post L a b l width m
  let T := packedIncidence L w 0 N
  have col (c : Fin 6) (j : Word w) (hj : j.val < N) : live (T.column c+j).val = raw (T.column c+j).val := by
    apply (agree _ _).symm
    have right := Nat.mul_le_mul_right N c.isLt
    rw [Nat.succ_mul] at right
    have room := resident.room
    change incidenceStart L 0 + 6*N ≤ 2^w at room
    have top : incidenceBase L 0 N c+j.val < 2^w := by unfold incidenceBase; omega
    rw [show T.column c = CursorRAM.encode w (incidenceBase L 0 N c) from packed_column ..,
      Fin.val_add,show (CursorRAM.encode w (incidenceBase L 0 N c)).val = incidenceBase L 0 N c
        from Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt top]
    unfold incidenceBase incidenceStart
    omega
  have baseRead (c : Fin 6) (e : X.Base × Fin (2^a)) := col c (IncidenceDirectory.basePort X e)
    ((IncidenceDirectory.basePort_lt X e).trans_le resident.rows.le)
  have actualRead (c : Fin 6) (e : (X.Base × Compression.BitWord l) × Fin (2^a)) := col c
    (IncidenceDirectory.actualPort X e) ((IncidenceDirectory.actualPort_lt X e).trans_le resident.rows.le)
  have inc := resident.incidence
  have rep : T.Represents X live :=
    ⟨fun e ↦ (baseRead 0 e).trans (inc.baseOut e),fun e ↦ (baseRead 1 e).trans (inc.baseIn e),
     fun e ↦ (baseRead 2 e).trans (inc.shift e),fun e ↦ (actualRead 3 e).trans (inc.actualOut e),
     fun e ↦ (actualRead 4 e).trans (inc.actualIn e),fun e ↦ (actualRead 5 e).trans (inc.width e)⟩
  have room := fit_fields L ⟨0,nonempty⟩ fit
  change levelStart L 0+L.shape.scalarFields < 2^w at room
  have field (j : ℕ) (hj : j < 14) :
      live (header w L 0+(j : Word w)).val = raw (header w L 0+(j : Word w)).val := by
    rw [address_val L 0 j (by omega)]
    exact (agree _ (Nat.le_add_right ..)).symm
  refine ⟨rep,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    exact (congrArg Fin.val (field j.val (j.isLt.trans (by decide)))).trans (resident.scalars j)
  · refine Eq.trans ?_ resident.frame
    funext j
    change live (header w L 0+6+(j.val : Word w)).val = raw (header w L 0+6+(j.val : Word w)).val
    rw [show header w L 0+6+(j.val : Word w) = header w L 0+((6+j.val : ℕ) : Word w) by simp [add_assoc]]
    exact field _ (by have := j.isLt; omega)
  · intro c
    exact (agree _ (by unfold incidenceHead; omega)).symm.trans (resident.incidenceHeads c)
  · intro j
    exact (agree _ (by unfold tableHead; omega)).symm.trans (resident.tableHeads j)
  · exact (agree _ (Nat.le_add_right ..)).symm.trans resident.role
  · exact (congrArg Fin.val (agree _ (Nat.le_add_right ..)).symm).trans resident.arena
  · exact (congrArg Fin.val (agree _ (Nat.le_add_right ..)).symm).trans resident.levels
  · exact (congrArg Fin.val (agree _ (Nat.le_add_right ..)).symm).trans resident.length

theorem resident {a b l pad : ℕ} {T : Type} [Fintype T] (L : Layout) (n : ℕ) (base : Word w)
    (m : Memory w) (hD : 1 < b+l) (hd : 2+pad = 2^a) (bits : T → ℕ)
    (ready : BlockHeaderStartup.Ready L a b l (∑ t, bits t) n base m) (fields : 30 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (room : incidenceStart L 0+6*CursorRAM.rowCount b l a ≤ 2^w)
    (width : (∑ t, bits t) < 2^w) :
    Resident L a b l (∑ t, bits t) n base m (cursorState (cursorCoordinateLabels b l) hD hd bits) := by
  obtain ⟨walk,inc,role,keep,arena,levels,len⟩ := BlockInitialPackets.initial L n base m hD hd bits
    ready fields fit room width
  have hfield := fit_fields L ⟨0,ready.nonempty⟩ fit
  change levelStart L 0 + L.shape.scalarFields < 2^w at hfield
  have low (i : ℕ) (hi : i < 14) :
      BlockInitialPackets.post L a b l (∑ t, bits t) m (header w L 0+(i : Word w)).val =
        initialFinal a L m (header w L 0+(i : Word w)).val := by
    rw [address_val L 0 i (by omega)]
    exact keep _ (by unfold incidenceStart levelHeaderWords; omega) (by omega)
  have cards : IncidenceDirectory.slotCount (cursorState (cursorCoordinateLabels b l) hD hd bits) = CursorRAM.rowCount b l a := by
    change Fintype.card (Fin (b+l) × Compression.BitWord b)*2^l*2^a = ((b+l)*2^b*2^l)*2^a
    rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_congr (Compression.bitWordFinEquiv b),Fintype.card_fin]
  refine ⟨walk,cards,room,?_,?_,inc,?_,?_,role,arena,levels,len,ready.positions⟩
  · intro c
    rw [keep _ (by unfold incidenceHead incidenceStart levelHeaderWords; have := c.isLt; omega)
      (by unfold incidenceHead; omega)]
    exact ready.initial.heads.incidence c
  · intro j
    rw [keep _ (by unfold tableHead incidenceStart levelHeaderWords; have := j.isLt; omega)
      (by unfold tableHead; omega)]
    exact ready.initial.heads.tables j
  · intro j
    exact (congrArg Fin.val (low j.val (j.isLt.trans (by decide)))).trans (ready.initial.terminal j)
  · refine Eq.trans ?_ (ready.initial.cursorFrame.trans ready.frame)
    funext i
    change BlockInitialPackets.post L a b l (∑ t, bits t) m (header w L 0+6+(i.val : Word w)).val = _
    have addr : header w L 0+6+(i.val : Word w) = header w L 0+((6+i.val : ℕ) : Word w) := by simp [add_assoc]
    change BlockInitialPackets.post L a b l (∑ t, bits t) m (header w L 0+6+(i.val : Word w)).val =
      initialFinal a L m (header w L 0+6+(i.val : Word w)).val
    rw [addr]
    exact low _ (by have := i.isLt; omega)

open CursorRouting Compression in
/-- One length threshold covers both the true pair startup and all four
initial descriptor visits, uniformly in the incoming contents of RAM. -/
theorem eventually_resident (D : CalendarRows.Spec) (d : ℕ) (F : Shape) (B a pad lanes steps : ℕ)
    (hd : 2+pad = 2^a) (hB : 1 ≤ B) (hq : 0 < D.q) (hph : 0 < D.phaseRows)
    (hθ : (D.p : ℝ)/D.q ≤ 1) (hlanes : lanes ≤ B)
    (arity : 7 ≤ F.arity) (fields : 30 ≤ F.scalarFields) {base : ℕ → ℕ} (hb : PolynomiallyBounded base) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (pub : Fin 11 → Word (wordBits B n)) (tag : Word (wordBits B n)),
      (pub 2).val = base n → (pub 6).val = n → (pub 7).val = addressBits B n → tag.val < base n →
      ∀ m, let L := LevelFields.tightDirectory (cursorLayout F B steps ((D.p : ℝ)/D.q) (base n) n) (CalendarRows.rows D n)
           let l := roundedDown D.p D.q n*lanes
           let b := virtualBits B n-l
           let widths : RAMSystem (virtualBits B n) → ℕ := ramFieldBits (virtualBucket n) (wordBits B n)
           ∃ hD : 1 < b+l, Resident L a b l (initialWidth B n) n (pub 2)
             (BlockHeaderStartup.post D d L B n a lanes steps pub tag m)
             (cursorState (cursorCoordinateLabels b l) hD hd widths) := by
  filter_upwards [BlockHeaderStartup.eventually_ready D d F B a lanes steps hB hq hph hθ hlanes arity fields hb,
    DescriptorParameters.eventually_tight_capacity D F B a lanes hB hθ hlanes hb,
    DescriptorParameters.eventually_tight_end D F B steps hB hb] with n ready cap fit
  intro pub tag workspace length address lower m
  let P := cursorLayout F B steps ((D.p : ℝ)/D.q) (base n) n
  let L := LevelFields.tightDirectory P (CalendarRows.rows D n)
  let l := roundedDown D.p D.q n*lanes
  let b := virtualBits B n-l
  let bits : RAMSystem (virtualBits B n) → ℕ := ramFieldBits (virtualBucket n) (wordBits B n)
  have hc := (cap P.positions P.levels).2
  have large : 1 < b+l := hc.split ▸ hc.cursors
  refine ⟨large,resident L n (pub 2) _ large hd bits (ready pub tag workspace length address lower m)
    fields fit hc.arrays_end.le hc.width_lt⟩

end CompressorRecords.BlockStartupPrefix

end VPVNP
end Computability
end OAI
