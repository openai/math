import OAI.Computability.MultitapeWeakETH.HistoryLayout

/-! # Reading recursive child ordinals and role words directly from a terminal log -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords BurstRAM DyadicBudget
open PairSimulation LocalHistory TraversalRows TraversalRoles DescriptorSpace
open private address address_poly address_eq from OAI.Computability.MultitapeWeakETH.TerminalColumns
open scoped Fin.CommRing
noncomputable section

abbrev HistoryPoint := LogQuery × Tally
abbrev HistorySite := HistoryPoint × Tally

variable {k R : Type} [Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)

private theorem room_at {L : Layout} {w i : ℕ} (fit : endAddress L < 2^w)
    (live : i<L.levels) (wide : 28≤levelWords L) : levelStart L i+27 < 2^w := by
  have below := levelStart_mono L (show i+1 ≤ L.levels by omega)
  change levelStart L i+27 < 2^w
  apply lt_of_le_of_lt _ fit
  apply le_trans _ below
  simp only [levelStart,Nat.succ_mul]
  omega

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory

set_option maxHeartbeats 1400000 in
/-- On each completed native history, read the actual role of every layer and the
canonical ordered children of every non-leaf. The programs use just the sparse volume,
the write log, the chronological level, and the requested site's enumeration ordinal. -/
theorem history_program (f : B.Entry → R) (hf : B.IsSolution f) :
    ∃ (role : HistoryPoint → Tally) (children : HistorySite → List Tally), Poly role ∧ Poly children ∧
    ∀ volume : Tally,
      let s := index (4*stepSize B) volume.length
      let n := scale B s
      let w := CursorBounds.wordBits 1 n
      let u := stepSize B*s
      let X := source B s
      let initial : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
      let L := gridLayout B volume
      let base := entryMemory B (3*u) u n s w
      let E := B.execute f hf s (lanes_fit B s) X
      ∀ (z : E.Choices) (log : CallProgram.Stores w),
        let past := executeLevels B f hf s (lanes_fit B s) X z
        let tags := SelectedDirectoryHistory.layers B f hf initial past
        let m := memory base log
        CompiledResident.resident B f hf 0 X.positions s n initial
          (Frame.data (k:=8) (BlockHeaderRun.header w L 0+6) base) past (E.finalState z) m →
        (∀ j : Fin tags.length, role ((volume,writes log),tally j.val) = tally tags[j].role.code) ∧
        ∀ (i : Fin past.length) (j : Fin (levelLayer B f hf (past[i.val]'i.isLt)).count),
          children (((volume,writes log),tally i.val),tally j.val) = ((levelLayer B f hf (past[i.val]'i.isLt)).ids j).map tally := by
  obtain ⟨read,hr,spec⟩ := descriptor_memory_program B
  let rd (q : LogQuery × Bits.Word) := read ((q.1.1,q.2),q.1.2)
  have cost : Poly rd := (((Easy.fst.compose Easy.fst).pair Easy.snd).pair (Easy.fst.compose Easy.snd)).poly.compose hr
  let role (q : HistoryPoint) :=
    let (ctx,head) := (historyQuery B (q,[])).1.1
    TerminalWords.capped (rd (ctx,address (head,tally 27)),tally 2)
  have rp : Poly role := by
    have ctx := ((Poly.identity.pair (Code.Poly.const ([] : Tally))).compose (historyQuery_poly B)).fstCompose.fstCompose
    have cell := (ctx.fstCompose.pair ((ctx.sndCompose.pair (Code.Poly.const (tally 27))).compose address_poly)).compose cost
    exact (cell.pair (Code.Poly.const (tally 2))).compose TerminalWords.capped_poly
  refine ⟨role,fun q => ChildScan.children rd (historyQuery B q),rp,(historyQuery_poly B).compose (ChildScan.children_poly rd cost),?_⟩
  intro volume s n w u X initial L base E z log past tags m stored
  have saved : Nonempty (SelectedDirectoryHistory.Past B f hf initial L (endAddress L) past m) := stored.1.1.1
  obtain ⟨D⟩ := saved
  have fit : endAddress L < 2^w := stored.1.2.1.startup.arena ▸ (m (levelStart L 0+14)).isLt
  have len : past.length=s*(S.steps+1) := VertexLevel.selected_pass_count B f hf s (lanes_fit B s) X z
  have levels : L.levels=1+(S.steps+1)*s := by unfold L gridLayout BlockProgram.layout; rfl
  have wide : 28≤levelWords L := by
    have head : levelHeaderWords L=66 := by unfold L gridLayout BlockProgram.layout; rfl
    unfold levelWords; omega
  let ctx : LogQuery := (tally s,writes log)
  have exactRead (a : Word w) : rd (ctx,wordBits a)=wordBits (m a.val) := spec s log a
  constructor
  · intro j
    have live : j.val<L.levels := by
      have h := j.isLt
      change j.val < (SelectedDirectoryHistory.layers B f hf initial past).length at h
      simp only [SelectedDirectoryHistory.layers,List.length_cons,List.length_map,len] at h
      rw [levels,Nat.mul_comm]; omega
    have room := room_at fit live wide
    have off : (((levelStart L j.val : Word w)+((27:ℕ):Word w))).val = levelStart L j.val+27 := by
      rw [← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt room]
    change TerminalWords.capped (rd (ctx,address (historyHeader B (volume,tally j.val),tally 27)),tally 2) = _
    simp only [historyHeader,tally_length,address_eq,exactRead,TerminalWords.capped,value_native]
    change tally (min (m (((levelStart L j.val : Word w)+((27:ℕ):Word w))).val).val 2) = _
    have tagWord : m (levelStart L j.val+27) = (tags[j].role.code : Word w) := D.role j
    have tagLe := tags[j].role.code_le_two
    have small : tags[j].role.code < 2^w := by omega
    rw [off,tagWord,Fin.val_natCast,Nat.mod_eq_of_lt small,Nat.min_eq_left tagLe]
  · intro i j
    have live : i.val<L.levels := by have h := i.isLt; rw [levels,Nat.mul_comm]; omega
    have room := room_at fit live wide
    change ChildScan.children rd (((ctx,historyHeader B (volume,tally i.val)),tally (endAddress L)),tally j.val) = _
    have head : historyHeader B (volume,tally i.val) = wordBits ((levelStart L i.val : ℕ) : Word w) := by
      unfold historyHeader
      rw [tally_length]
    rw [head]
    have cell : levelStart L i.val+26 < 2^w := by omega
    have result := ChildScan.selected_children (w:=w) (m:=m) (R:=R) (k:=k) (S:=S) (A:=LogQuery) B f hf rd ctx exactRead
      (initial:=initial) (L:=L) (past:=past) D i j cell
    exact result

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
