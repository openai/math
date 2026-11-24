import OAI.Computability.VPVNP.CompressorBlockHeadWindows
import OAI.Computability.VPVNP.CompressorPublishedScoreRoom

/-! # Chronological DFS head publications on the allocated graph levels

The second publication starts from the first group's actual output. The
joined source group records every global ordinal and every emitted report.
For shrinking levels the original graph header and table capacity locate
the selected-layout bit beyond the published scalar fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.PublishedHeads

open BurstRAM DescriptorSpace BlockPlanner PhaseRecipe Schedule Compression
open scoped Fin.CommRing

variable {w : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (base : Word w) (positions blocks t step cap : ℕ) (m : Memory w)
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog prog)) base
local notation "pub" => Schedule.Ports.data pt
local notation "first" => Script.levelsPerBlock prog * t
local notation "st" => (levelStart L (first) : Word w)
local notation "here" => levelStart L (first+step)

variable {N : ℕ} (terms : Fin 4 → Expr) (heads : Fin N → Expr)
    (W : Window (BlockProgram.script B) (fieldVisits step 36 terms))
    (V : Window (BlockProgram.script B) (fieldVisits step 40 heads))
local notation "mid" => image pub st m (here+36) terms

/-- The two physical publication groups, with the second attached to the
first's exact final memory and immediately succeeding ordinal. -/
structure Pair : Prop where
  termGroup : Installed (N:=4) B base positions blocks t step 36 terms W cap m
  dataGroup : Installed (N:=N) B base positions blocks t step 40 heads V cap mid
  consecutive : V.before.length = W.before.length+4

variable {B base positions blocks t step cap m terms heads W V}

theorem Pair.online (pair : Pair B base positions blocks t step cap m terms heads W V) :
    ∃ ps : List (SourceOnline.Packet prog w),
      SourceOnline.Group prog L base cap ((prog).initial.length+t*(prog).block.length+W.before.length)
        (directoryRows L) m ps ∧
      ps.map (fun p ↦ p.stage.phase) = W.indices++V.indices ∧
      ps.flatMap SourceWalk.Packet.reports = fieldReports (here+36) pub st m terms ++ fieldReports (here+40) pub st mid heads ∧
      ps.flatMap (fun p ↦ p.stage.choices) = List.replicate (4+N) [] := by
  obtain ⟨ps,p,pp,pr,pb⟩ := pair.termGroup.online
  obtain ⟨qs,q,qp,qr,qb⟩ := pair.dataGroup.online
  have len : ps.length = 4 := by
    simpa only [Window.indices,List.length_map,List.length_ofFn,fieldVisits] using congrArg List.length pp
  have same : SourceOnline.post m ps = mid := by rw [SourceOnline.post,pr]; rfl
  have next : (prog).initial.length+t*(prog).block.length+W.before.length+ps.length =
      (prog).initial.length+t*(prog).block.length+V.before.length := by rw [pair.consecutive,len,Nat.add_assoc]
  refine ⟨ps++qs,p.append (by rw [same,next]; exact q),?_,?_,?_⟩
  · simp only [List.map_append,pp,qp]
  · simp only [List.flatMap_append,pr,qr]
  · simp only [List.flatMap_append,pb,qb,List.replicate_add]

theorem Pair.frame (pair : Pair B base positions blocks t step cap m terms heads W V) (x : ℕ)
    (out : x < here+36 ∨ here+40+N ≤ x) :
    image pub st mid (here+40) heads x = m x := by
  have d := pair.dataGroup.source.outside x (by unfold Outside; omega)
  exact d.trans (pair.termGroup.source.outside x (by unfold Outside; omega))

theorem pair_charge (ports : Fin 5 → Word w) (state : Word w) (m : Memory w) (start : ℕ)
    (terms : Fin 4 → Expr) (heads : Fin N → Expr) :
    let nextMem := image ports state m (start+36) terms
    RAMBuckets.cost Report.probes (fieldReports (start+36) ports state m terms ++ fieldReports (start+40) ports state nextMem heads) =
      2*(4+N) := by
  intro nextMem
  have charge {n : ℕ} (head : ℕ) (input : Memory w) (rhs : Fin n → Expr) :
      RAMBuckets.cost Report.probes (fieldReports head ports state input rhs) = 2*n := packet_cost ports state input head rhs
  rw [RAMBuckets.cost_append,charge,charge,Nat.mul_add]

private theorem offset_length {α : Type*} (ls : List (List α)) (j : ℕ) (hj : j < ls.length) :
    (ls.take (j+1)).flatten.length = (ls.take j).flatten.length + ls[j].length := by
  rw [List.take_succ_eq_append_getElem hj,List.flatten_append,List.length_append,List.flatten_cons,
    List.flatten_nil,List.append_nil]

variable (B) (i : Fin S.steps)

/-- All eighteen shrinking publications on the live table-zero allocation. -/
theorem shrink_pair (h : Ready B base positions blocks t cap m) {g : ℕ}
    (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g)) (T : IncidenceDirectory w)
    (header : ShrinkHeaderReads.Header i X T (tableBase L (first+i.val) (0 : Fin 6)) L (first) m)
    (sites : X.positions ≤ positions) :
    Pair B base positions blocks t i.val cap m (BlockHeadStability.shrinkTerms B i) (dataValues B i)
      (BlockGroups.shrink B i 10) (BlockGroups.shrink B i 11) := by
  have level : first+i.val < (L).levels := by
    have hb := Nat.mul_le_mul_left (S.steps+1) h.block
    change (S.steps+1)*t+i.val < 1+(S.steps+1)*blocks
    rw [Nat.mul_succ] at hb
    have := i.isLt
    omega
  have score := PublishedScoreRoom.allocated B i X T base.val positions blocks header
    (show LevelFields.Entry L (first) pub st m from ⟨rfl,h.pitch⟩) level sites h.room
  have term := shrink_terms_window B i h score
  refine ⟨term,shrink_data_window B i (h.after_publication term),?_⟩
  rw [BlockGroups.shrink_offset,BlockGroups.shrink_offset]
  have lens := offset_length (BlockGroups.parts B i) 10 (by rw [BlockGroups.parts_length]; decide)
  have four : ((BlockGroups.parts B i)[10]'(by rw [BlockGroups.parts_length]; decide)).length = 4 :=
    BlockProgram.termPointers_length ..
  change _+((BlockGroups.parts B i).take 11).flatten.length = _+((BlockGroups.parts B i).take 10).flatten.length+4
  rw [lens,four,Nat.add_assoc]

/-- The four refresh term pointers are followed by its next-level address. -/
theorem refresh_pair (h : Ready B base positions blocks t cap m) :
    Pair B base positions blocks t S.steps cap m (BlockHeadStability.refreshTerms B)
      (fun _ : Fin 1 ↦ LevelFields.atLevel (S.steps+1)) (BlockGroups.refresh B 5) (BlockGroups.refresh B 6) := by
  have term := refresh_terms_window B h
  refine ⟨term,refresh_next_window B (h.after_publication term),?_⟩
  rw [BlockGroups.refresh_offset,BlockGroups.refresh_offset]
  have lens := offset_length (BlockGroups.refreshParts B) 5 (by rw [BlockGroups.refreshParts_length]; decide)
  have four : ((BlockGroups.refreshParts B)[5]'(by rw [BlockGroups.refreshParts_length]; decide)).length = 4 :=
    BlockProgram.termPointers_length ..
  change _+((BlockGroups.refreshParts B).take 6).flatten.length = _+((BlockGroups.refreshParts B).take 5).flatten.length+4
  rw [lens,four,Nat.add_assoc]

end CompressorRecords.PublishedHeads

end

end VPVNP
end Computability
end OAI
