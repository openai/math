import OAI.Computability.BorderVNP.RoutingISAScheduleClockMergeRanges
import OAI.Computability.BorderVNP.CellPacketGeometryBoundaries
import OAI.Computability.BorderVNP.CellTeamReportCharge

/-! # Public and original chunk intervals in the supplemental allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source CellPacket.Supplement
open DiagonalTallyCellReports CellPacketGeometry

private theorem chunk_intervals {Site : Type} (slot : Site → ℕ) (width : ℕ) (fs : Site → List Factor)
    (parts : List (Source.Part Site)) (base lo hi stop : ℕ)
    (publicEnd : base+(parts.flatMap Part.publicBuffer).length ≤ lo)
    (original : ∀ j, Part.original j ∈ parts → hi ≤ slot j ∧ slot j+width+(boxBody (fs j)).length ≤ stop) :
    ∀ c ∈ chunks slot width fs base parts, c.endSource ≤ lo ∨ hi ≤ c.base ∧ c.endSource ≤ stop := by
  induction parts generalizing base with
  | nil => simp [chunks]
  | cons h ps ih =>
    cases h with
    | publicWords xs =>
      simp only [List.flatMap_cons,Part.publicBuffer,List.length_append] at publicEnd
      intro c member
      obtain rfl | rest := List.mem_cons.mp member
      · exact .inl (by change base+xs.length ≤ lo; omega)
      · exact ih (base+xs.length) (by omega) (fun j h => original j (List.mem_cons_of_mem _ h)) c rest
    | original j =>
      simp only [List.flatMap_cons,Part.publicBuffer,List.nil_append] at publicEnd
      intro c member
      obtain rfl | rest := List.mem_cons.mp member
      · exact .inr (original j List.mem_cons_self)
      · exact ih base publicEnd (fun j h => original j (List.mem_cons_of_mem _ h)) c rest

/-- The actual fixed-width public section, private site slots, and reserved
supplemental stride determine every chunk interval needed by the merge. -/
theorem MergeSections.of_public_private {Site : Type} (l : CellControlRows.Layout) (p : ℕ → Placed Site)
    (geom : ℕ → ℕ) (extra : ℕ → List Record) (description : ℕ)
    (publicEnd : ∀ c < l.cells, (p c).publicBase+((p c).parts.flatMap Part.publicBuffer).length ≤ l.sorted)
    (geometryBase : ∀ c < l.cells, geom c=(p c).publicBase+((prefixParts (p c)).flatMap Part.publicBuffer).length)
    (slots : ∀ c < l.cells, ∀ j, Sum.inr j ∈ (p c).boxes → l.sorted+l.padded ≤ (p c).slot j ∧
      (p c).slot j+description ≤ l.supplemental ∧ (p c).headerWidth+(boxBody ((p c).factors j)).length ≤ description)
    (supplement : ∀ c < l.cells, ((extra c).flatMap record).length ≤ l.stride) :
    MergeSections l p geom extra := by
  have whole (c : ℕ) : (p c).parts=prefixParts (p c)++[.publicWords (fieldList record (p c).rows++fieldList vector (p c).reports)] := rfl
  have endAt (c : ℕ) (hc : c<l.cells) := publicEnd c hc
  simp only [whole,List.flatMap_append,List.flatMap_singleton,Part.publicBuffer,List.length_append,fieldList,List.length_cons] at endAt
  constructor
  · intro c hc
    apply chunk_intervals _ _ _ _ _ _ _ _ (by have h := endAt c hc; omega)
    intro j member
    have site : Sum.inr j ∈ (p c).boxes := by
      obtain h | h := List.mem_cons.mp member
      · contradiction
      · obtain ⟨b,hb,eq⟩ := List.mem_map.mp h
        cases b with
        | inl fs => contradiction
        | inr k => cases eq; exact hb
    obtain ⟨lo,hi,fit⟩ := slots c hc j site
    exact ⟨lo,by omega⟩
  · intro c hc
    rw [geometryBase c hc]
    simp only [fieldList,List.length_cons]
    have h := endAt c hc
    omega
  · exact supplement

/-- The actual public inverse ranks put the complete ordinary words of
every cell before the descriptor bank, including its report-address suffix. -/
theorem publicSection_end {C p d H dest : ℕ} {S Orig E : Type} {D : SiteWords.Directory S Orig C}
    {pin : Orig → E} {arg : E → ℕ} {mem : ℕ → ℕ} {fit : C+D.words.length+C ≤ 2^p}
    {space : C+(Schema.coords (D.referenceRows pin).length).length+C ≤ 2^d} {π : Equiv.Perm (Fin (2^p))}
    (buf : Schema.Buffers D fit space dest H (fun i => ((D.referenceRows pin).get i).2)
      (fun i => ((D.referenceRows pin).get i).1) arg mem π) (c : Fin C) :
    let r := sectionRange mem dest (Markers.start fit c) (Markers.stop fit c)
    r.1+((plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c) (D.reports c)).flatMap Part.publicBuffer).length ≤
      descriptorBank dest p := by
  intro r
  rw [←(buf.publicWords c).1]
  change dest+mem (dest+(2^p+(Markers.start fit c).val))+1+
    (mem (dest+(2^p+(Markers.stop fit c).val))-mem (dest+(2^p+(Markers.start fit c).val))-1) ≤ dest+(2^p+2^p)
  rw [buf.positions,buf.positions]
  have a := (π.symm (Markers.start fit c)).isLt
  have b := (π.symm (Markers.stop fit c)).isLt
  omega

/-- Obtain the public and opaque source intervals directly from the reconstructed
cell buffers, the actual received site slots, and the report stride. -/
theorem MergeSections.of_buffers {C bits d H dest description : ℕ} {S Orig E : Type}
    {D : SiteWords.Directory S Orig C} {pin : Orig → E} {arg : E → ℕ} {mem : ℕ → ℕ}
    {fit : C+D.words.length+C ≤ 2^bits} {space : C+(Schema.coords (D.referenceRows pin).length).length+C ≤ 2^d}
    {π : Equiv.Perm (Fin (2^bits))}
    (buf : Schema.Buffers D fit space dest H (fun i => ((D.referenceRows pin).get i).2)
      (fun i => ((D.referenceRows pin).get i).1) arg mem π)
    (l : CellControlRows.Layout) (p : ℕ → Placed Orig) (geom : ℕ → ℕ) (extra : ℕ → List Record)
    (cells : l.cells=C) (sorted : l.sorted=descriptorBank dest bits)
    (bases : ∀ c : Fin C, (p c.val).publicBase=(sectionRange mem dest (Markers.start fit c) (Markers.stop fit c)).1)
    (parts : ∀ c : Fin C, (p c.val).parts=plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c) (D.reports c))
    (geometry : ∀ c < l.cells, geom c=(p c).publicBase+((prefixParts (p c)).flatMap Part.publicBuffer).length)
    (slots : ∀ c < l.cells, ∀ j, Sum.inr j ∈ (p c).boxes → l.sorted+l.padded ≤ (p c).slot j ∧
      (p c).slot j+description ≤ l.supplemental ∧ (p c).headerWidth+(boxBody ((p c).factors j)).length ≤ description)
    (supplement : ∀ c < l.cells, ((extra c).flatMap record).length ≤ l.stride) : MergeSections l p geom extra := by
  apply MergeSections.of_public_private l p geom extra description _ geometry slots supplement
  intro c hc
  let i : Fin C := ⟨c,hc.trans_eq cells⟩
  rw [bases i,parts i,sorted]
  exact publicSection_end buf i

/-- The signed arena locates the typed task table above the report partition,
and the actual descriptor bank ends before the receiving cube cells. -/
theorem MergeArena.of_signed_layout (l : CellControlRows.Layout) (a : SignedTaskArena.Layout) (team frame offsets ctl : ℕ)
    (tasks : l.toLayout=a.tasks team frame offsets ctl) (cells : l.cells≤a.before.bound.cells)
    (sort : l.sorted+l.padded ≤ a.cube.cellBank) (supplement : l.supplemental=a.before.supplement)
    (stride : l.stride=a.before.bound.supplementStride) (counters : l.counters=a.before.counters)
    (merged : l.merged=a.before.merged) (four : l.four=a.before.four) : MergeArena l := by
  apply MergeArena.of_before l a.before cells supplement stride counters merged four
  · apply sort.trans
    apply (show a.cube.cellBank ≤ a.cube.stop from Nat.le_add_right ..).trans
    apply le_trans _ a.constants_le_before
    simp only [CubeConstants.arenaEnd,CubeConstants.idBase]
    omega
  · rw [tasks]
    exact Nat.le_add_right ..

/-- The allocation for this emitted report bounds the actual supplemental
records in its cell's reservation for every choice of the local cursor. -/
theorem allocated_binding_stride {pre : DiagonalTallyAllocation.BeforeTasks} {post : DiagonalTallyAllocation.AfterTasks}
    {banks : CellBanks.Layout} {rl : ReportLayout} {cs : List (ReportCell rl)} {q : ReportCursor}
    (allocation : ReportAllocation pre post banks rl cs q) (c : ReportCell rl) (hc : c∈cs) (cursor : LocalReportCursor) :
    ((bindingRows c.bundles cursor).flatMap record).length ≤ pre.bound.supplementStride := by
  rw [binding_words]
  exact allocation.supplements c hc

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
