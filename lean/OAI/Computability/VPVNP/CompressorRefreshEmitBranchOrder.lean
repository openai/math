import OAI.Computability.VPVNP.CompressorRefreshBeforeMatch
import OAI.Computability.VPVNP.CompressorRefreshGroupSplit
import OAI.Computability.VPVNP.CompressorPassTimeline
import OAI.Computability.VPVNP.CompressorBlockHeadSequence

/-! # Ordinal boundaries of an actual selected refresh

The common header and demand packets reach the same selector ordinal as the
selected native core. Its remaining workers end where the six incidence copies
begin. The nine traversal publications following those copies end the refresh.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.RefreshEmit

open BurstRAM Compression BlockPlanner PassTimeline PortRefresh SourceOnline
open scoped Fin.CommRing
open private offset_length from OAI.Computability.VPVNP.CompressorBlockHeadSequence

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
variable {f : B.Entry → R} {hf : B.IsSolution f} {g w : ℕ} {base : Word w}
variable {positions blocks t cap termCap : ℕ} {X : State S.portExponent (S.portExponent+g)}
variable {c : Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh}
local notation "scr" => BlockProgram.script B
local notation "sh" => RefreshBlockPlan.shape B
local notation "d" => LevelRecipe.Shape.ports sh
local notation "h" => LevelRecipe.Shape.dH sh
local notation "ties" => LevelRecipe.Shape.ties sh
local notation "deg" => LevelRecipe.Shape.degree sh
local notation "loc" => Located.mk t (Pass.refresh (steps := S.steps))
local notation "start" => Located.first loc B
local notation "ord" => List.length (Script.initial scr)+t*List.length (Script.block scr)
local notation "coreStart" => ord+List.length (Window.before (BlockGroups.refresh B 1))
local notation "copyStart" => ord+List.length (Window.before (BlockGroups.refresh B 2))
local notation "Pkt" => Packet scr w

private theorem header_end : start+3 = coreStart := by
  change ord+((List.finRange S.steps).flatMap (BlockProgram.shrink B)).length+3 = _
  rw [BlockGroups.refresh_offset,Nat.add_assoc]
  rfl

private theorem core_end : coreStart+(6+ties+d*h+deg) = copyStart := by
  have parts := BlockGroups.refreshParts_length B
  have next := offset_length (BlockGroups.refreshParts B) 1 (by rw [parts]; decide)
  have size : ((BlockGroups.refreshParts B)[1]'(by rw [parts]; decide)).length = 6+ties+d*h+deg := by
    change ((LevelRecipe.order sh).map _).length = _
    rw [List.length_map,RefreshCore.stage_split]
    simp only [RefreshPrepare.stages,RefreshCore.afterTerm,List.length_append,List.length_cons,
      List.length_nil,List.length_finRange,List.length_map]
    omega
  rw [size] at next
  rw [BlockGroups.refresh_offset,BlockGroups.refresh_offset]
  change ord+(_+((BlockGroups.refreshParts B).take 1).flatten.length)+_ =
    ord+(_+((BlockGroups.refreshParts B).take 2).flatten.length)
  rw [next]; omega

variable {m m' : Memory w} {hs ds pre rest : List (Packet (BlockProgram.script B) w)}
  {packet : Packet (BlockProgram.script B) w}
variable (before : RefreshBefore.Before B f hf base positions blocks t X cap m hs ds)
variable (split : RefreshCore.SelectedSplit B f hf base positions blocks t X c termCap cap m' pre packet rest)

include before split

/-- Both physical prefixes launch their selector at the same global row. -/
theorem selector_ordinal : start+(hs++ds).length = coreStart+pre.length := by
  have header := header_end (B := B) (t := t)
  rw [before.length,split.preCount]
  omega

/-- The absolute selector, first copy, and one-past-end row of a selected
refresh, with the actual fifteen post-core packets in their original order. -/
theorem branch_ordinals (extra : List Pkt) (count : extra.length = 15) :
    start+(hs++ds).length = coreStart+pre.length ∧
      coreStart+pre.length+1+rest.length = copyStart ∧
      start+(hs++ds).length+1+(rest++extra).length = (loc).finish B := by
  have nr : rest.length = 2+d*h+deg := by
    have num := congrArg List.length split.tailPhases
    simp only [List.length_map,Window.indices,List.length_ofFn] at num
    change rest.length = (RefreshCore.afterTerm B).length at num
    simp only [RefreshCore.afterTerm,List.length_map,List.length_finRange,List.length_append,
      List.length_cons,List.length_nil] at num
    omega
  refine ⟨selector_ordinal before split,?_,?_⟩
  · have endOf := core_end (B := B) (t := t)
    rw [split.preCount,nr]; omega
  · change _ = start+(BlockProgram.refresh B).length
    rw [before.length,List.length_append,count,nr,BlockProgram.refresh_length]
    omega

end CompressorRecords.RefreshEmit

end

end VPVNP
end Computability
end OAI
