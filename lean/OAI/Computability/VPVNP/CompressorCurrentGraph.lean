import OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders
import OAI.Computability.VPVNP.CompressorRecordsShrinkFrame

/-! # The current graph at a selected compression boundary

A boundary carries the actual terminal scalars and the packed incidence
columns of its current state. The initial position count is retained at
level zero. Publishing the next header preserves the current graph's old
incidence columns, even at the first shrinking substep.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CurrentGraph

open BurstRAM Compression DescriptorSpace BlockHeaderRun PortRefresh.TraversalHeaders SourceTransport
open scoped Fin.CommRing

variable {w a g : ℕ}

/-- The part of the initial physical header used at subsequent levels. -/
structure Startup (L : Layout) (n : ℕ) (m : Memory w) : Prop where
  counts : ∃ V D lanes, DescriptorHeads.CountsAt (header w L 0) m V D lanes ∧ V*lanes=L.positions
  arena : (m (levelStart L 0+14)).val=endAddress L
  levels : (m (levelStart L 0+28)).val=L.levels
  length : (m (levelStart L 0+29)).val=n

/-- The current level's terminal scalars, pointer bank and packed incidence represent its
state, with the startup data still present at level zero. -/
structure Current (L : Layout) (i : ℕ) (X : State a g) (n : ℕ) (m : Memory w) : Prop where
  terminal : Scalars.Present (.terminal a) (Fintype.card X.Base) g (header w L i) m
  heads : HeadBank L i (IncidenceDirectory.slotCount X) m
  incidence : (packedIncidence L w i (IncidenceDirectory.slotCount X)).Represents X m
  startup : Startup L n m

open private keep_counts keep_present address_val from OAI.Computability.VPVNP.CompressorBlockHeaderRun
open private incidence_end_le from OAI.Computability.VPVNP.CompressorDescriptorSpace

/-- Every occupied column word lies between the end of this level's header
and the beginning of its scratch arrays. -/
theorem column_range (L : Layout) (i : Fin L.levels) (rows : ℕ) (size : rows ≤ slotCapacity L)
    (fit : endAddress L < 2^w) (c : Fin 6) (j : Word w) (hj : j.val < rows) :
    let x := ((packedIncidence L w i rows).column c+j).val
    incidenceStart L i ≤ x ∧ x < arrayBase L i := by
  have room := packed_incidence_room L fit i size
  have mul := Nat.mul_le_mul_right rows c.isLt
  rw [Nat.succ_mul] at mul
  have pos : incidenceBase L i rows c+j.val < incidenceStart L i+6*rows := by
    dsimp only [incidenceBase]; omega
  rw [packed_column,Fin.val_add,show (CursorRAM.encode w (incidenceBase L i rows c)).val=incidenceBase L i rows c
    from Nat.mod_eq_of_lt ((Nat.le_add_right ..).trans_lt (pos.trans room)),Nat.mod_eq_of_lt (pos.trans room)]
  exact ⟨(Nat.le_add_right ..).trans (Nat.le_add_right ..),pos.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_left 6 size) _)⟩

theorem incidence_keep (L : Layout) (i : Fin L.levels) (X : State a g) {m out : Memory w}
    (fit : endAddress L < 2^w) (size : IncidenceDirectory.slotCount X ≤ slotCapacity L)
    (rep : (packedIncidence L w i (IncidenceDirectory.slotCount X)).Represents X m)
    (keep : ∀ x, incidenceStart L i ≤ x → x < arrayBase L i → out x = m x) :
    (packedIncidence L w i (IncidenceDirectory.slotCount X)).Represents X out := by
  let T := packedIncidence L w i (IncidenceDirectory.slotCount X)
  have atCell (c : Fin 6) (j : Word w) (hj : j.val < IncidenceDirectory.slotCount X) :
      out (T.column c+j).val=m (T.column c+j).val := by
    have h := column_range L i _ size fit c j hj
    exact keep _ h.1 h.2
  have hb (c : Fin 6) (e : X.Base × Fin (2^a)) := atCell c _ (IncidenceDirectory.basePort_lt X e)
  have ha (c : Fin 6) (e : (X.Base × BitWord g) × Fin (2^a)) := atCell c _ (IncidenceDirectory.actualPort_lt X e)
  exact ⟨fun e => (hb 0 e).trans (rep.baseOut e),fun e => (hb 1 e).trans (rep.baseIn e),
    fun e => (hb 2 e).trans (rep.shift e),fun e => (ha 3 e).trans (rep.actualOut e),
    fun e => (ha 4 e).trans (rep.actualIn e),fun e => (ha 5 e).trans (rep.width e)⟩

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
  {f : B.Entry → R} {hf : B.IsSolution f}

/-- The stored current state supplies the source data of all three physical
header bursts. The old graph and the new head bank coexist in their output. -/
theorem Current.publish {L : Layout} {n : ℕ} (v : SelectedLevel B f hf) (old new : Fin L.levels)
    {m : Memory w} (cur : Current L old v.input n m) (next : old.val+1=new.val)
    (six : 6 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (size : IncidenceDirectory.slotCount v.input ≤ slotCapacity L)
    (sites : v.input.positions < 2^w) (degree : slotDegree S < 2^w) :
    let out := finalMemory v L old new m
    Substep v L old new six m ∧
      (packedIncidence L w old (IncidenceDirectory.slotCount v.input)).Represents v.input out ∧
      HeadBank L old (IncidenceDirectory.slotCount v.input) out ∧ HeadBank L new v.outputSlots out := by
  obtain ⟨V,D,lanes,cnt,hpos⟩ := cur.startup.counts
  have run := substep_run v L old new next six fit m cur.terminal cnt hpos sites degree
  have banks := headBanks_of_substep run (by omega) cur.heads
  refine ⟨run,incidence_keep L old v.input fit size cur.incidence ?_,banks⟩
  intro x low high
  have nextAddr := incidence_end_le L old
  rw [next] at nextAddr
  have lower : levelStart L old+6 ≤ incidenceStart L old := by unfold incidenceStart levelHeaderWords; omega
  exact run.outside x (.inr (lower.trans low)) (.inl (high.trans_le nextAddr))
    (.inl ((high.trans_le nextAddr).trans_le (Nat.le_add_right ..)))


/-- All first-level cells needed from startup, including the saved length and
the immutable descriptor arena end. -/
def startupCell (L : Layout) (x : ℕ) := ∃ offset ∈ ([0,1,2,14,28,29] : List ℕ), x=levelStart L 0+offset

/-- The six scalar words and the two families of pointers that describe a
current graph. The remaining header words hold local traversal metadata. -/
def graphCell (L : Layout) (i x : ℕ) :=
  (levelStart L i ≤ x ∧ x < levelStart L i+6) ∨
  (levelStart L i+L.shape.scalarFields ≤ x ∧ x < incidenceStart L i)

private theorem cell_val (L : Layout) {i j : ℕ} (h : levelStart L i+j < 2^w) :
    (header w L i + (j : Word w)).val=levelStart L i+j := by
  change (((levelStart L i : ℕ) : Word w)+(j : Word w)).val = _
  rw [← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt h]

theorem Startup.keep {L : Layout} {n : ℕ} {m out : Memory w} (s : Startup L n m)
    (room : levelStart L 0+2 < 2^w)
    (keep : ∀ x, startupCell L x → out x=m x) : Startup L n out := by
  obtain ⟨V,D,lanes,old,number⟩ := s.counts
  refine ⟨⟨V,D,lanes,keep_counts old ?_,number⟩,
    (congrArg Fin.val (keep _ ⟨14,by decide,rfl⟩)).trans s.arena,(congrArg Fin.val (keep _ ⟨28,by decide,rfl⟩)).trans s.levels,
    (congrArg Fin.val (keep _ ⟨29,by decide,rfl⟩)).trans s.length⟩
  intro j
  rw [cell_val L (by have := j.isLt; omega)]
  apply keep _ ⟨j.val,?_,rfl⟩
  fin_cases j <;> decide

private theorem graph_keep {L : Layout} (i : Fin L.levels) {X : State a g} {m out : Memory w}
    (scalars : Scalars.Present (.terminal a) (Fintype.card X.Base) g (header w L i) m)
    (heads : HeadBank L i (IncidenceDirectory.slotCount X) m)
    (six : 6 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (keep : ∀ x, graphCell L i x → out x=m x) :
    Scalars.Present (.terminal a) (Fintype.card X.Base) g (header w L i) out ∧
      HeadBank L i (IncidenceDirectory.slotCount X) out := by
  have room := level_room L fit i
  have span : levelStart L i+6 ≤ levelStart L (i.val+1) := by
    simp only [levelStart,Nat.succ_mul,levelWords,levelHeaderWords]; omega
  refine ⟨keep_present scalars (fun j => ?_),⟨fun c => ?_,fun c => ?_⟩⟩
  · rw [cell_val L (by have := j.isLt; omega)]
    exact keep _ (.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left j.isLt _⟩)
  · apply (keep _ (.inr ⟨Nat.le_add_right ..,?_⟩)).trans (heads.incidence c)
    unfold incidenceStart levelHeaderWords
    have := c.isLt; omega
  · apply (keep _ (.inr ⟨?_,?_⟩)).trans (heads.tables c)
    · unfold tableHead; omega
    · unfold tableHead incidenceStart levelHeaderWords
      have := c.isLt; omega

theorem Current.transfer {L : Layout} {i : Fin L.levels} {X : State a g} {n : ℕ} {m out : Memory w}
    (cur : Current L i X n m) (fit : endAddress L < 2^w) (six : 6 ≤ L.shape.scalarFields)
    (size : IncidenceDirectory.slotCount X ≤ slotCapacity L) (agree : Agree (levelStart L 0 ≤ ·) m out) :
    Current L i X n out := by
  have lower := levelStart_mono L (Nat.zero_le i.val)
  have room := level_room L fit i
  have span : levelStart L i+6 ≤ levelStart L (i.val+1) := by
    simp only [levelStart,Nat.succ_mul,levelWords,levelHeaderWords]; omega
  obtain ⟨term,heads⟩ := graph_keep i cur.terminal cur.heads six fit (fun x hx => by
    rcases hx with hx|hx <;> exact (agree _ (by omega)).symm)
  refine ⟨term,heads,incidence_keep L i X fit size cur.incidence (fun x lo _ => ?_),cur.startup.keep (by omega) ?_⟩
  · exact (agree x (lower.trans ((Nat.le_add_right ..).trans lo))).symm
  · rintro x ⟨j,_,rfl⟩; exact (agree _ (Nat.le_add_right ..)).symm

/-- Replaying the post-header kernels may install the next graph's incidence
columns and traversal metadata. Only its scalar words, pointers and six
startup words are needed to reconstruct the full current boundary. -/
theorem Current.successor {L : Layout} {n : ℕ} (v : SelectedLevel B f hf) (old new : Fin L.levels)
    {m out : Memory w} (cur : Current L old v.input n m) (next : old.val+1=new.val)
    (fields : 30 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (sub : Substep v L old new (by omega) m)
    (rep : (packedIncidence L w new (IncidenceDirectory.slotCount (v.pass.next v.term))).Represents (v.pass.next v.term) out)
    (frame : ∀ x, graphCell L new x ∨ startupCell L x → out x=finalMemory v L old new m x) :
    Current L new (v.pass.next v.term) n out := by
  have bank := (headBanks_of_substep sub (by omega) cur.heads).2
  have slots : v.outputSlots=IncidenceDirectory.slotCount (v.pass.next v.term) := by
    rw [SelectedLevel.outputSlots,SelectedLevel.outputSites,State.positions,Fintype.card_prod,
      Fintype.card_congr (bitWordFinEquiv _),Fintype.card_fin]
  obtain ⟨term,heads⟩ := graph_keep new sub.output (slots ▸ bank) (by omega) fit (fun x h => frame x (.inl h))
  obtain ⟨V,D,lanes,cnt,hpos⟩ := cur.startup.counts
  have afterStartup : Startup L n (finalMemory v L old new m) :=
    ⟨⟨V,D,lanes,keep_counts cnt sub.firstCounts,hpos⟩,
      (congrArg Fin.val (sub.firstScalarTail v next 14 (by decide) (by omega))).trans cur.startup.arena,
      (congrArg Fin.val (sub.firstScalarTail v next 28 (by decide) (by omega))).trans cur.startup.levels,
      (congrArg Fin.val (sub.firstScalarTail v next 29 (by decide) (by omega))).trans cur.startup.length⟩
  have hspan : levelStart L 0+2 ≤ levelStart L 1 := by
    simp only [levelStart,Nat.zero_mul,Nat.add_zero,Nat.one_mul,levelWords,levelHeaderWords]; omega
  have hi : 1 ≤ L.levels := by have := old.isLt; omega
  exact ⟨term,heads,rep,afterStartup.keep (hspan.trans_lt ((levelStart_mono L hi).trans_lt fit)) (fun x h => frame x (.inr h))⟩

end CompressorRecords.CurrentGraph

end VPVNP
end Computability
end OAI
