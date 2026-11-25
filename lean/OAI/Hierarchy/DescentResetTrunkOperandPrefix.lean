import OAI.Hierarchy.DescentResetWindowTicketCount
import OAI.Hierarchy.DescentResetWindowStemOrder
import OAI.Hierarchy.DescentClosedLocalRoster

namespace OAI
/-! # The measured source rank of an incoming stem is its retained trunk offset -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open DescentSharedCableNames DescentOrderedWords DescentNamedContact DescentCableUnbundling
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "siteNames" => installedNames old (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "oldEdges" => (old).graph.Edge
local notation "loc" => fun j : oldEdges=>(T).home ((old).graph.dst j)

theorem stem_nodes (s : Bool) (j : oldEdges) :
    siteNames ((coarse).graph.src (stemParent B (s,j)))=.inl (s,(T).home (ends (old).graph s j)) ∧
    siteNames ((coarse).graph.dst (stemParent B (s,j)))=.inr ((Z).bank.attach (s,(placement).input s j)) ∧
    (coarse).graph.width (stemParent B (s,j))=(Z).unit := by
  let e:=stemParent B (s,j)
  have read:=sourceFields_read old (T).home (placement).input (T).hub same (Z).bank (Z).tables e
  change physicalFields _ _ _ _ _ _ _ e=sourceFields _ _ _ _ _ ((wires) ((wires).symm (.inl (s,j)))) at read
  rw [Equiv.apply_symm_apply] at read
  exact ⟨congrArg RawFields.src read,congrArg RawFields.dst read,(congrArg RawFields.width read).trans ((Z).allWidths j)⟩

private theorem at_head (x j : oldEdges) (s : Bool) :
    (Stage.home B.raw ((coarse).graph.src (stemParent B (s,x)))=
      Stage.home B.raw ((coarse).graph.src (stemParent B (true,j))) ∨
      Stage.home B.raw ((coarse).graph.dst (stemParent B (s,x)))=
      Stage.home B.raw ((coarse).graph.src (stemParent B (true,j)))) ↔ s=true ∧ loc x=loc j := by
  have sx:=stem_nodes B s x
  have sj:=stem_nodes B true j
  have equivalent (a b : (coarse).graph.Site) :
      Stage.home B.raw a=Stage.home B.raw b ↔ siteNames a=siteNames b :=
    (B.valid.coordinates.eq_iff).trans ((siteNames).injective.eq_iff.symm)
  rw [equivalent,equivalent,sx.1,sx.2.1,sj.1]
  cases s <;> simp [ends]

private theorem later_parent (j : oldEdges) (x : (Z).Fallback ⊕ ((placement).Contact ⊕ PrivateOccurrence B)) :
    ¬ (tape).rank ((motherNames B).symm (.inr x))<(tape).rank (stemParent B (true,j)) := by
  change ¬((Z).installedResetOrdinal T vertexCode birth ((wires).symm (.inr x))).val<
    ((Z).installedResetOrdinal T vertexCode birth ((wires).symm (.inl (true,j)))).val
  have upper {U V : Type} {m n : ℕ} (a : U↪Fin m) (b : V↪Fin n) (l : U) (r : V) :
      ¬(DescentResetCableSlots.sum a b (.inr r)).val<(DescentResetCableSlots.sum a b (.inl l)).val := by
    change ¬ (m+(b r).val<(a l).val)
    have small:=(a l).isLt
    omega
  change ¬(DescentResetCableSlots.sum _ _ ((wires) ((wires).symm (.inr x)))).val <
    (DescentResetCableSlots.sum _ _ ((wires) ((wires).symm (.inl (true,j))))).val
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact upper _ _ _ _

private theorem siblings (j x : oldEdges) :
    (tape).rank (stemParent B (true,x))<(tape).rank (stemParent B (true,j)) ↔ birth x<birth j := by
  change ((Z).installedResetOrdinal T vertexCode birth (stemParent B (true,x))).val<
      ((Z).installedResetOrdinal T vertexCode birth (stemParent B (true,j))).val ↔ _
  have x₀:=congrArg Prod.fst ((Z).stemArchive T vertexCode birth true x)
  have j₀:=congrArg Prod.fst ((Z).stemArchive T vertexCode birth true j)
  change ((Z).installedResetOrdinal T vertexCode birth (stemParent B (true,x))).val=
    (birth x).val+_*_ at x₀
  change ((Z).installedResetOrdinal T vertexCode birth (stemParent B (true,j))).val=
    (birth j).val+_*_ at j₀
  rw [x₀,j₀,Nat.add_lt_add_iff_right]
  rfl

def earlierIncoming (j : oldEdges) :=(Finset.univ.filter (fun x : oldEdges=>loc x=loc j ∧ birth x<birth j)).card

/-- The signed panel's field 6 is measured on the actual chronological reset
tape. Only the earlier true stems at this same terminal contribute. -/
theorem incoming_sourceTicket (j : oldEdges) (live : 0<weight B (stemParent B (true,j))) :
    (sourceTicket B (stemParent B (true,j)) live).val=earlierIncoming B j := by
  classical
  have un : 0<(Z).unit:=by rw [B.unit,←B.next.grain];exact Nat.mul_pos B.next.placement.unitPos G.base_pos
  rw [sourceTicket_count]
  let read (e : (coarse).graph.Edge) := if
    (Stage.home B.raw ((coarse).graph.src e)=Stage.home B.raw ((coarse).graph.src (stemParent B (true,j))) ∨
     Stage.home B.raw ((coarse).graph.dst e)=Stage.home B.raw ((coarse).graph.src (stemParent B (true,j)))) ∧
      (tape).rank e<(tape).rank (stemParent B (true,j)) then (coarse).graph.width e/(Z).unit else 0
  change ∑e, read e=_
  rw [←(motherNames B).symm.sum_comp read,Fintype.sum_sum_type]
  have after (x : (Z).Fallback ⊕ ((placement).Contact ⊕ PrivateOccurrence B)) : read ((motherNames B).symm (.inr x))=0 := by
    simp only [read,later_parent B j x,and_false,ite_false]
  simp only [after,Finset.sum_const_zero,Nat.add_zero]
  rw [Fintype.sum_prod_type,Fintype.sum_bool]
  have left (x : oldEdges) : read ((motherNames B).symm (.inl (false,x)))=0 := by
    change read (stemParent B (false,x))=0
    simp [read,at_head B x j false]
  have right (x : oldEdges) : read ((motherNames B).symm (.inl (true,x)))=
      if loc x=loc j ∧ birth x<birth j then 1 else 0 := by
    change read (stemParent B (true,x))=_
    simp [read,at_head B x j true,siblings B j x,(stem_nodes B true x).2.2,Nat.div_self un]
  simp only [left,right,Finset.sum_const_zero,Nat.add_zero]
  simp only [earlierIncoming, Finset.card_filter]

/-- The same native integer is the dyadic word count used by oldField at
the target end of the original compressed cable. -/
theorem incoming_offset (j : oldEdges) (live : 0<weight B (stemParent B (true,j))) :
    DescentOrderedWords.offset (DescentOrderedReset.fibreKey birth loc (loc j))
      (fun e=> (old).graph.width e.val) ⟨j,rfl⟩ =
      (sourceTicket B (stemParent B (true,j)) live).val*(Z).unit := by
  rw [incoming_sourceTicket]
  have widths : (fun e : Fibre loc (loc j) => (old).graph.width e.val) = fun _ => (Z).unit :=
    funext (fun e => (Z).allWidths e.val)
  trans DescentOrderedWords.offset (DescentOrderedReset.fibreKey birth loc (loc j))
    (fun _ => (Z).unit) ⟨j, rfl⟩
  · exact congrArg (fun masses => DescentOrderedWords.offset
      (DescentOrderedReset.fibreKey birth loc (loc j)) masses ⟨j, rfl⟩) widths
  unfold DescentOrderedWords.offset DescentOrderedWords.before
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  change (Finset.univ.filter fun e : Fibre loc (loc j)=>birth e.val<birth j).card=
    (Finset.univ.filter fun e : oldEdges=>loc e=loc j ∧ birth e<birth j).card
  apply Finset.card_bij (fun e _=>e.val)
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.property,(Finset.mem_filter.mp he).2⟩
  · intro e _ f _ eqn;exact Subtype.ext eqn
  · intro e he
    obtain ⟨_,atEnd,first⟩:=Finset.mem_filter.mp he
    exact ⟨⟨e,atEnd⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,first⟩,rfl⟩

theorem incoming_chunks (j : oldEdges) (live : 0<weight B (stemParent B (true,j))) (p pieces : ℕ)
    (positive : 0<p) (scale : (Z).unit=pieces*p) :
    DescentOrderedWords.offset (DescentOrderedReset.fibreKey birth loc (loc j))
      (fun e=> (old).graph.width e.val) ⟨j,rfl⟩/p=(sourceTicket B (stemParent B (true,j)) live).val*pieces := by
  rw [incoming_offset B j live,scale,←Nat.mul_assoc,Nat.mul_div_cancel _ positive]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
