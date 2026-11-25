import OAI.Hierarchy.DescentResetStemObservedWord
import OAI.Hierarchy.DescentResetStemPosition
import OAI.Hierarchy.DescentResetCandidateMeta
import OAI.Hierarchy.DescentResetStemDecoder

namespace OAI
/-! # Native reset stem flags and endpoint classes on the actual receiver -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical
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
local notation "Host" => DescentSharedCableNames.Stage.Host (Fin groups) B.next.V k
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
local notation "widthsAgree" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub widthsAgree (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)


local notation "Slot" => Fin (2^(m-c))×Fin (2*(A).cap)

open DescentResetFieldAssembler DescentResetWindowResidentSources
local notation "R" => blocks B
local notation "rank" => (Z).rawHostRank T vertexCode
local notation "shapeId" => (Z).codeHost T vertexCode
local notation "lab" => DescentRelativeContacts.shortName c
local notation "End" => (old).graph.Edge

/-- The observed post-reset neighbour directory can be reused at every
group and low block of the same receiver. Duplicate neighbour edges give
one directory entry even if they arise from different device families. -/
def stemNeighbors (u : Host) : Finset ℕ :=
  (B.next.placement.near u.1.2).map rawRank

theorem stem_ordinal_read (u t : Host) (member : t∈sources B.next.placement u) :
    stemOrdinal (rank u.1.2).val (stemNeighbors B u) (rank t.1.2).val=localClass B u t := by
  rw [class_host B u t member]
  unfold stemOrdinal stemNeighbors
  have countMap {V : Type} [DecidableEq V] (name : V ↪ ℕ) (N : Finset V) (a b : V) :
      ((insert (name a) (N.map name)).filter (fun n => n < name b)).card =
        ((insert a N).filter (fun u => name u < name b)).card := by
    rw [← Finset.map_insert, Finset.filter_map, Finset.card_map]
    rfl
  exact countMap rawRank (B.next.placement.near u.1.2) u.1.2 t.1.2

theorem stem_absent_read (u : Host) :
    (rank u.1.2).val∉stemNeighbors B u ↔ u∉Stage.near B.next.placement u := by
  rw [self_missing B u]
  exact not_congr (Finset.mem_map' (f:=rawRank) (a:=u.1.2))

private theorem receiver_eq (u v : Host) (hi : (receiverRoot B u).2=(receiverRoot B v).2) :
    (rank u.1.2).val=(rank v.1.2).val ↔ u=v := by
  constructor
  · intro yes
    have host : u.1.2=v.1.2:=(rank).injective (Fin.ext yes)
    have pos : (u.1.1,u.2)=(v.1.1,v.2):=(digits).symm.injective hi
    have gr : u.1.1 = v.1.1 := congrArg (fun p : Fin groups × Block k => p.1) pos
    have bl : u.2 = v.2 := congrArg (fun p : Fin groups × Block k => p.2) pos
    exact Prod.ext (Prod.ext gr host) bl
  · rintro rfl
    rfl

theorem stem_fields_read (s : Bool) (j : End) :
    let e:=stemParent B (s,j)
    let t:=(T).home (ends (old).graph s j)
    let x:=DescentCommonHost.Node.trunk s (lab ((T).code t))
    let y:=DescentCommonHost.publicNode placement (Z).graph c (T).code s ((placement).input s j)
    (rank ((R).src e).1.2).val=shapeId x ∧ (rank ((R).dst e).1.2).val=shapeId y ∧
      (R).count e=1 ∧ decide (e∈(coarse).core)=
        (s || !((A).hub (B.frame.host.symm ((T).code t).1))) := by
  intro e t x y
  have shape:=(Z).stemFields T s j
  have start:=congrArg DescentResetTrunks.RawFields.src shape
  have stop:=congrArg DescentResetTrunks.RawFields.dst shape
  have width:=congrArg DescentResetTrunks.RawFields.width shape
  have core:=congrArg DescentResetTrunks.RawFields.core shape
  have code (v : (coarse).graph.Site) :
      (rank (Stage.home B.next.placement (hop v)).1.2).val=shapeId ((Z).commonName T v) := by
    rw [named_home B v]
    exact ((Z).codeHost_at T vertexCode v).symm
  have coreAt : (s || !((T).hub ((T).home ((old).graph.src j)))) =
      (s || !((A).hub (B.frame.host.symm ((T).code t).1))) := by
    cases s
    · simp only [t, ends, Bool.false_or,(T).tag,B.frame.originalHub,B.frame.homeHost,Equiv.symm_apply_apply]
    · rfl
  refine ⟨(code _).trans (congrArg (shapeId) start),
    (code _).trans (congrArg (shapeId) stop),?_,core.trans coreAt⟩
  change weight B e=1
  rw [weight_quotient,show (coarse).graph.width e=(Z).unit from width]
  apply Nat.div_self
  rw [B.unit, ←B.next.grain]
  exact Nat.mul_pos B.next.placement.unitPos G.base_pos

/-- Both endpoints share the same predecessor cell, so their complete
coordinates can be tested by comparing just the observed native host name. -/
theorem stem_word_at (u : Host) (s : Bool) (j : End)
    (aligned : (receiverRoot B ((R).src (stemParent B (s,j)))).2=(receiverRoot B u).2) :
    let e:=stemParent B (s,j)
    let src:=(rank ((R).src e).1.2).val
    let dst:=(rank ((R).dst e).1.2).val
    let hub:=(A).hub (B.frame.host.symm (receiverRoot B u).1)
    (receiverRoot B ((R).src e)).1=(receiverRoot B u).1 →
      stemWord (rank u.1.2).val (stemNeighbors B u) s hub (some (src,dst)) =
        if live : active (R) u e then «meta» B u (some ⟨e,live⟩) else .blank := by
  intro e src dst hub same
  have roots:=stem_receiver_root B s j
  have together : receiverRoot B ((R).dst e)=receiverRoot B ((R).src e):=roots.2.trans roots.1.symm
  have srcAt : src=(rank u.1.2).val ↔ (R).src e=u:=receiver_eq B _ u aligned
  have dstAt : dst=(rank u.1.2).val ↔ (R).dst e=u:=
    receiver_eq B _ u ((congrArg Prod.snd together).trans aligned)
  obtain ⟨_,_,weight,core⟩:=stem_fields_read B s j
  have hubAt : (receiverRoot B u).1=((T).code ((T).home (ends (old).graph s j))).1 :=
    same.symm.trans (congrArg Prod.fst roots.1)
  by_cases live : active (R) u e
  · have present : src=(rank u.1.2).val ∨ dst=(rank u.1.2).val:=live.2.imp srcAt.mpr dstAt.mpr
    simp only [stemWord,present,live,ite_true,dite_true]
    let x : Local (R) u:=⟨e,live⟩
    have self : u∈sources B.next.placement u:=Finset.mem_insert_self ..
    have smem : (R).src e ∈ sources B.next.placement u := source_mem _ _ _ u x
    have dmem : (R).dst e ∈ sources B.next.placement u := destination_mem B u x
    have cnt : (R).count e = 1 := weight
    have flag : decide (e ∈ (coarse).core) =
        (s || !((A).hub (B.frame.host.symm ((T).code ((T).home (ends (old).graph s j))).1))) := core
    simp only [«meta»,src,dst,stem_ordinal_read B u ((R).src e) smem,
      stem_ordinal_read B u ((R).dst e) dmem,stem_ordinal_read B u u self,
      stem_absent_read,cnt,flag,hub,hubAt]
  · have dead : ¬(src=(rank u.1.2).val ∨ dst=(rank u.1.2).val) :=
      fun yes=>live ⟨(show 0 < (R).count (stemParent B (s,j)) by rw [weight]; decide),yes.imp srcAt.mp dstAt.mp⟩
    simp only [stemWord,dead,live,ite_false,dite_false]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
