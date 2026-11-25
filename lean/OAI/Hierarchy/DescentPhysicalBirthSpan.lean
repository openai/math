import OAI.Hierarchy.DescentResetSelectedNewbornRange
import OAI.Hierarchy.DescentRotorPhysicalRangePrefix
import OAI.Hierarchy.DescentInstalledLaneRange
import OAI.Hierarchy.DescentRotorPublicSelectorNone

namespace OAI
/-! # Argument counts in the physical fresh-operation range register -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentBundleHistory DescentKernelHistory
noncomputable section

private theorem part_length {α β : Type*} (f : α→List β) (xs : List α) (x : α) (used : x∈xs) :
    (f x).length≤(xs.flatMap f).length:=by
  induction xs with
  | nil=>simp at used
  | cons y ys ih=>
    rw [List.flatMap_cons,List.length_append]
    rcases List.mem_cons.mp used with same|rest
    · subst y
      omega
    · have enough:=ih rest
      omega

/-- The count carried by any occurrence fits within the flattened argument
list of that node, even when the queried ordinal is in padding. -/
theorem count_le_arity {p : ℕ} {U V : Type} {w : V→ℕ} {r : BitRecipe U V w}
    (s : Shape p r) (hp : 0<p) (u : r.Node) (j : ℕ) :
    DescentResetMetadataInputs.argumentSpan s u j≤(s.recipe hp).arity u:=by
  rw [←atSlot_count,←length s u hp]
  by_cases hj : j<(occurrences s u).length
  · let c:=(occurrences s u)[j]
    have mem : c∈occurrences s u:=List.getElem_mem hj
    obtain ⟨row,inRows,inRow⟩:=List.mem_flatMap.mp mem
    obtain ⟨item,inside,here⟩:=List.mem_flatMap.mp inRow
    obtain ⟨_,same⟩:=List.mem_replicate.mp here
    have inner:=part_length (fun q=>List.replicate q.count q.code) row item inside
    have outer:=part_length (List.flatMap (fun q=>List.replicate q.count q.code)) (s.rows u) row inRows
    simp only [atSlot,List.getElem?_eq_getElem hj,Option.elim_some,value]
    change c.count≤(occurrences s u).length
    rw [same]
    exact (show item.code.count≤_ from by simpa only [List.length_replicate,Slice.code] using inner).trans outer
  · simp [atSlot,List.getElem?_eq_none (Nat.le_of_not_gt hj)]
end
end Hierarchy.DescentRetainedRangeDigits

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentRetainedRangeDigits DescentBundleHistory DescentResetPublicOperandBook
open DescentKernelHistory DescentResetOperandSetup DescentRotor DescentRouterSlots DescentBatchedNodeOrder
open DescentDenseHostOrder LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 350000
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "cfg" => publicOperands z roots menu.payload
local notation "C" => a.successor.setup
local notation "R" => (cfg).rotor
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)
    (Y : Fin (a.successor.setup.retained.outputs*a.successor.setup.placement.shapes)→Fin a.successor.setup.placement.oldHosts→
      Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.retained.bits)
    (j : Fin a.successor.setup.retained.outputs) (blk : Fin a.successor.setup.placement.blocks)
    (h : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
    (x : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits) (arg : Fin (publicOperands z roots menu.payload).args) (node : Fin (publicOperands z roots menu.payload).nodes)
    (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val=0 → ((publicOperands z roots menu.payload).reg x 1).val=0)
    (physical : ∀hv : h.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0 →
      ((publicOperands z roots menu.payload).reg x 3).val=(a.successor.setup.placement.shape (name ⟨h.val,hv⟩)).val)
    (fresh : ∀hv : h.val<U,menu.keep (a.successor.setup.placement.shape (name ⟨h.val,hv⟩))=false)
local notation "mouth" => finProdFinEquiv (arg,node)
local notation "word" f:arg => menu.spanValue name Y j blk h g x mouth (page f) blank physical
local notation "prv" f:arg => (R).flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split node.val arg.val
   (page f).succ ((cfg).reg x)
local notation "surface" f:arg => ((cfg).column z.board (C).fieldBits (some (page f)) mouth x).val

include fresh in
/-- All three public tree fields pass through the actual selected operand
adder. This equality covers the original tree's empty rows as well. -/
theorem physical_fallback_span (shape : ↥(roster z.board (R).residual (R).depth))
    (seen : ((cfg).reg x 3).val=(localRank z.board (R).residual (R).depth shape).val)
    (side peer path) (atTree : shape.val=.fall side peer path)
    (f : Fin 3) : (word f).val=surface f:=by
  apply menu.selected_surface_word name Y j blk h g x arg node blank physical fresh
  exact (R).flat_fallback z.board ((cfg).reg x) shape seen side peer path atTree _ _ _ _ _ _

include fresh in
/-- On an exceptional actor the other physical source is zero for every
ordinal. The measured exceptional mouth is therefore the complete f6 word. -/
theorem fallback_count {p : ℕ} {T A : Type} {width : A→ℕ} {r : BitRecipe T A width}
    (sh : Shape p r) (u : r.Node) (shape : ↥(roster z.board (R).residual (R).depth))
    (seen : ((cfg).reg x 3).val=(localRank z.board (R).residual (R).depth shape).val)
    (side peer path) (atTree : shape.val=.fall side peer path)
    (issued : surface (2:Fin 3)=atSlot sh u arg.val 2) :
    (word (2:Fin 3)).val=DescentResetMetadataInputs.argumentSpan sh u arg.val:=by
  rw [←atSlot_count,←issued]
  apply menu.selected_surface_word name Y j blk h g x arg node blank physical fresh
  exact (R).flat_fallback z.board ((cfg).reg x) shape seen side peer path atTree _ _ _ _ _ _

variable {I K Q B H : Type} [Fintype I] [Fintype Q] [Fintype B] [Fintype H] [Field K]
variable (d : ℕ) (hp : 0<(publicOperands z roots menu.payload).grain) (contact : I→Q) (input : Bool→I→B)
    (site : Bool→B→H) (owner : Bool→Q→H) (align : ∀s i,site s (input s i)=owner s (contact i))
    (side : Bool) (host : H) {nKey : ℕ} {hw : 0<(publicOperands z roots menu.payload).rotor.packet} {pay : ℝ}
    (first : InputId site side host↪Fin (2^a.successor.middle.rotorBits))
    (last : LinkId owner side host↪Fin (2^a.successor.middle.rotorBits))
local notation "mu" => (R).batches*(cfg).grain
local notation "src" => fun i=>first (root contact input site owner side host align i)
local notation "dst" => fun i=>last (link contact owner side host i)
variable (P : BaseCircuit K z.board (publicOperands z roots menu.payload).multiplicity (publicOperands z roots menu.payload).rotor.packet ((publicOperands z roots menu.payload).rotor.batches*(publicOperands z roots menu.payload).grain) hw
  (fun i : Item contact owner side host => first (root contact input site owner side host align i))
  (fun i : Item contact owner side host => last (link contact owner side host i)) pay) (key : I↪Fin nKey)
local notation "dev" => DescentGoodRouter.device d mu contact input site owner align side host z.board first last P
local notation "ops" => DescentBatchedRotor.program d (R).batches (cfg).grain hp contact input site owner align
  side host z.board first last P key
local notation "id₀" => deviceOrder z.board hw (R).batches (cfg).grain hp contact input site owner align key d (.good first last pay P)
variable (actor : (DescentGoodRouter.device d
     ((publicOperands z roots menu.payload).rotor.batches*(publicOperands z roots menu.payload).grain) contact input site owner align side host z.board first last P).Site)
variable (z₀ : (DescentBatchedRotor.program d
     (publicOperands z roots menu.payload).rotor.batches (publicOperands z roots menu.payload).grain hp contact input site owner align side host z.board first last P key actor).Node)
local notation "w₀" => DescentKernelHistory.boundaryWidth dev actor
variable (multiple : ∀i,
    (DescentKernelHistory.boundaryWidth (DescentGoodRouter.device d ((publicOperands z roots menu.payload).rotor.batches*(publicOperands z roots menu.payload).grain) contact input site owner align side host z.board first last P) actor i)=
    (DescentKernelHistory.boundaryWidth (DescentGoodRouter.device d ((publicOperands z roots menu.payload).rotor.batches*(publicOperands z roots menu.payload).grain) contact input site owner align side host z.board first last P) actor i)/(publicOperands z roots menu.payload).grain*(publicOperands z roots menu.payload).grain)
local notation "sh" => ofProgram (fun i=>w₀ i/(cfg).grain) multiple hp (ops actor)
local notation "physicalActor" => (DescentCommonPalette.rotorSiteEquiv z.board d P.layers (cfg).multiplicity (R).packet mu).symm actor
local notation "flat" => (R).flattened z.board (cfg).multiplicity P.layers (cfg).grain (id₀ actor z₀).val physicalActor

include fresh in
omit [Fintype B] in
/-- A real entry in the physical rotor's private lane prefix contributes its
true slice count. Being in that prefix proves that the public mouth is empty. -/
theorem rotor_private_fields
    (numbered : node.val=(id₀ actor z₀).val)
    (active : ((cfg).reg x 1).val>0 ∧ ((cfg).reg x 2).val%2=0 ∧
      ((cfg).reg x 3).val<(roster z.board (R).residual (R).depth).card)
    (label : Unit×ℕ) (shape : ((DescentResetTrunkPalette.order z.board (R).residual (R).depth).symm
      ⟨((cfg).reg x 3).val,active.2.2⟩).val=.good side label physicalActor)
    (located : (((cfg).reg x 1).val-1,label.2)∈DescentHostDirectory.codes (R).residual)
    (measured : DescentRecordedRotorLayers.layers a.successor.middle.rotorBits (R).packet (R).gain ((cfg).reg x 0).val=P.layers)
    (seats : P.layers*(R).batches≤(R).addresses) (l : DescentRotorOperandQueryROM.Shape.PrivateLane z.board) (within : ℕ)
    (hit : flat[arg.val]?=some (l,within)) (axis : Fin 3) (fitField : atSlot sh z₀ arg.val axis<2^(C).fieldBits) :
    (word axis).val=atSlot sh z₀ arg.val axis:=by
  have rd (f₀ : Fin 3) : prv f₀=atSlot sh z₀ arg.val f₀:=by
    rw [numbered]
    exact (R).issued_private_range z.board d (cfg).grain hp contact input site owner align side host first last P key
      actor z₀ multiple arg.val (cfg).split ((cfg).reg x) active label shape located measured seats l within hit f₀
  have real : arg.val<((sh).recipe hp).arity z₀:=by
    by_contra! late
    have none_ := (R).padded_private_row z.board d (cfg).grain hp contact input site owner align side host first last P key
      actor z₀ multiple arg.val late
    rw [hit] at none_
    contradiction
  have positive:=atSlot_count_pos (r:=(ops actor).recipe) sh z₀ ⟨arg.val,by rwa [length (r:=(ops actor).recipe) sh z₀ hp]⟩
  have got:=menu.selected_private_range name Y j blk h g x arg node blank physical fresh
    (show 0<prv (2:Fin 3) from (rd 2).symm ▸ positive) axis
  rw [rd] at got
  simpa only [Fin.val_natCast,Nat.mod_eq_of_lt fitField] using congrArg Fin.val got


include fresh in
omit [Fintype B] in
theorem rotor_private_count
    (numbered : node.val=(id₀ actor z₀).val)
    (active : ((cfg).reg x 1).val>0 ∧ ((cfg).reg x 2).val%2=0 ∧
      ((cfg).reg x 3).val<(roster z.board (R).residual (R).depth).card)
    (label : Unit×ℕ) (shape : ((DescentResetTrunkPalette.order z.board (R).residual (R).depth).symm
      ⟨((cfg).reg x 3).val,active.2.2⟩).val=.good side label physicalActor)
    (located : (((cfg).reg x 1).val-1,label.2)∈DescentHostDirectory.codes (R).residual)
    (measured : DescentRecordedRotorLayers.layers a.successor.middle.rotorBits (R).packet (R).gain ((cfg).reg x 0).val=P.layers)
    (seats : P.layers*(R).batches≤(R).addresses) (l : DescentRotorOperandQueryROM.Shape.PrivateLane z.board) (within : ℕ)
    (hit : flat[arg.val]?=some (l,within)) (space : ((sh).recipe hp).arity z₀<2^(C).fieldBits) :
    (word (2:Fin 3)).val=DescentResetMetadataInputs.argumentSpan sh z₀ arg.val:=by
  have countEq := atSlot_count (r:=(ops actor).recipe) sh z₀ arg.val
  apply Eq.trans _ countEq
  exact menu.rotor_private_fields name Y j blk h g x arg node blank physical fresh d hp contact input site owner align side host first last P key actor z₀ multiple numbered active label shape located measured seats l within hit 2 (countEq.trans_lt ((count_le_arity (r:=(ops actor).recipe) sh hp z₀ arg.val).trans_lt space))

include fresh in
omit [Fintype B] in
/-- The flattened private prefix and the public suffix partition every original
rotor operand, including arbitrary padding beyond the program. -/
theorem rotor_fields
    (numbered : node.val=(id₀ actor z₀).val)
    (active : ((cfg).reg x 1).val>0 ∧ ((cfg).reg x 2).val%2=0 ∧
      ((cfg).reg x 3).val<(roster z.board (R).residual (R).depth).card)
    (label : Unit×ℕ) (shape : ((DescentResetTrunkPalette.order z.board (R).residual (R).depth).symm
      ⟨((cfg).reg x 3).val,active.2.2⟩).val=.good side label physicalActor)
    (located : (((cfg).reg x 1).val-1,label.2)∈DescentHostDirectory.codes (R).residual)
    (measured : DescentRecordedRotorLayers.layers a.successor.middle.rotorBits (R).packet (R).gain ((cfg).reg x 0).val=P.layers)
    (seats : P.layers*(R).batches≤(R).addresses)
    (axis : Fin 3) (fitField : atSlot sh z₀ arg.val axis<2^(C).fieldBits)
    (surfaceRead : flat[arg.val]?=none → surface axis=atSlot sh z₀ arg.val axis) :
    (word axis).val=atSlot sh z₀ arg.val axis:=by
  cases atInput : flat[arg.val]? with
  | some pair =>
    rcases pair with ⟨l,within⟩
    exact menu.rotor_private_fields name Y j blk h g x arg node blank physical fresh d hp contact input site owner
      align side host first last P key actor z₀ multiple numbered active label shape located measured seats l within
      atInput axis fitField
  | none =>
    rw [←surfaceRead atInput]
    apply menu.selected_surface_word name Y j blk h g x arg node blank physical fresh
    apply (R).flat_table_outside z.board _ _ _ _ _ _ active side label physicalActor shape
    simpa only [measured,numbered] using atInput


include fresh in
omit [Fintype B] in
theorem rotor_count
    (numbered : node.val=(id₀ actor z₀).val)
    (active : ((cfg).reg x 1).val>0 ∧ ((cfg).reg x 2).val%2=0 ∧
      ((cfg).reg x 3).val<(roster z.board (R).residual (R).depth).card)
    (label : Unit×ℕ) (shape : ((DescentResetTrunkPalette.order z.board (R).residual (R).depth).symm
      ⟨((cfg).reg x 3).val,active.2.2⟩).val=.good side label physicalActor)
    (located : (((cfg).reg x 1).val-1,label.2)∈DescentHostDirectory.codes (R).residual)
    (measured : DescentRecordedRotorLayers.layers a.successor.middle.rotorBits (R).packet (R).gain ((cfg).reg x 0).val=P.layers)
    (seats : P.layers*(R).batches≤(R).addresses)
    (space : ((sh).recipe hp).arity z₀<2^(C).fieldBits)
    (surfaceRead : flat[arg.val]?=none → surface (2:Fin 3)=atSlot sh z₀ arg.val 2) :
    (word (2:Fin 3)).val=DescentResetMetadataInputs.argumentSpan sh z₀ arg.val:=by
  have countEq := atSlot_count (r:=(ops actor).recipe) sh z₀ arg.val
  apply Eq.trans _ countEq
  exact menu.rotor_fields name Y j blk h g x arg node blank physical fresh d hp contact input site owner align side host first last P key actor z₀ multiple numbered active label shape located measured seats 2 (countEq.trans_lt ((count_le_arity (r:=(ops actor).recipe) sh hp z₀ arg.val).trans_lt space)) surfaceRead

include fresh in
omit [Fintype B] in
/-- Root gates and spine comparisons use exclusively physical private rotor
cables. Beyond their complete prefix both the range and the public lookup are
zero on the real good actor. -/
theorem rotor_private_slots
    (numbered : node.val=(id₀ actor z₀).val)
    (actorShape : ↥(roster z.board (R).residual (R).depth))
    (key₀ : DescentResetHostSize.Code (R).residual)
    (depth : ((cfg).reg x 1).val=key₀.val.1+1) (safe : ((cfg).reg x 2).val%2=0)
    (seen : ((cfg).reg x 3).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (headSeen : ((cfg).oldConfig.header ((cfg).basic x) 2).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (good : actorShape.val=.good side ((),key₀.val.2) physicalActor)
    (measured : DescentRecordedRotorLayers.layers a.successor.middle.rotorBits (R).packet (R).gain ((cfg).reg x 0).val=P.layers)
    (seats : P.layers*(R).batches≤(R).addresses) (axis : Fin 3) (fitField : atSlot sh z₀ arg.val axis<2^(C).fieldBits)
    (allPrivate : (DescentRetainedRangeDigits.operandCodes (fun i=>w₀ i/(cfg).grain) ((ops actor).op z₀)).flatten=
      ((R).privateRows z.board (cfg).multiplicity P.layers (cfg).grain (id₀ actor z₀).val physicalActor).map
        (DescentRotorOperandQueryROM.Shape.PrivateLane.code z.board (R) (cfg).multiplicity P.layers (cfg).grain))
    (noPort : (R).publicTap z.board (cfg).multiplicity P.layers (cfg).grain (id₀ actor z₀).val arg.val physicalActor=none) :
    (word axis).val=atSlot sh z₀ arg.val axis :=by
  have fit : ((cfg).reg x 3).val<(roster z.board (R).residual (R).depth).card:=
    seen ▸ (localRank _ _ _ actorShape).isLt
  have ix : (⟨_,fit⟩:Fin (roster z.board (R).residual (R).depth).card)=
    DescentResetTrunkPalette.order z.board (R).residual (R).depth actorShape:=Fin.ext seen
  have active : ((cfg).reg x 1).val>0 ∧ ((cfg).reg x 2).val%2=0 ∧
      ((cfg).reg x 3).val<(roster z.board (R).residual (R).depth).card:=⟨by omega,safe,fit⟩
  apply menu.rotor_fields name Y j blk h g x arg node blank physical fresh d hp contact input site owner align side host
    first last P key actor z₀ multiple numbered active ((),key₀.val.2) (by simpa only [ix,Equiv.symm_apply_apply] using good)
    (by simpa only [depth,Nat.add_sub_cancel] using key₀.property) measured seats axis fitField
  intro empty_
  have noRoot:=(R).public_selector_none z.board (cfg).multiplicity (cfg).grain node.val arg.val ((cfg).reg x)
    side key₀ physicalActor actorShape depth safe seen good (by simpa only [measured,numbered] using noPort)
  have headRoom : ((cfg).oldConfig.header ((cfg).basic x) 2).val<(roster z.board (R).residual (R).depth).card:=
    headSeen ▸ (localRank _ _ _ actorShape).isLt
  have header : (⟨_,headRoom⟩:Fin (roster z.board (R).residual (R).depth).card)=
    DescentResetTrunkPalette.order z.board (R).residual (R).depth actorShape:=Fin.ext headSeen
  have visible : ((cfg).oldConfig.header ((cfg).basic x) 2).val <
      (roster z.board (cfg).oldConfig.residual (cfg).oldConfig.maxDepth).card := headRoom
  have decoded : ((DescentResetTrunkPalette.order z.board (cfg).oldConfig.residual (cfg).oldConfig.maxDepth).symm
      ⟨((cfg).oldConfig.header ((cfg).basic x) 2).val,visible⟩).val = .good side ((),key₀.val.2) physicalActor :=
    (congrArg (fun t => ((DescentResetTrunkPalette.order z.board (R).residual (R).depth).symm t).val) header).trans
      ((congrArg Subtype.val ((DescentResetTrunkPalette.order z.board (R).residual (R).depth).symm_apply_apply actorShape)).trans good)
  have dead : (cfg).mixed z.board node.val arg.val x=none:=by
    by_cases vacant : ((cfg).oldConfig.header ((cfg).basic x) 0).val=0
    · simp only [Config.mixed,vacant,ite_true]
    · simp only [Config.mixed,vacant,ite_false,noRoot,DescentFallbackOperandBranch.Config.mixed,dite_eq_left visible,decoded]
  have keys:=(R).private_prefix z.board (fun i=>w₀ i/(cfg).grain) multiple hp (ops actor) z₀
    (cfg).multiplicity P.layers (id₀ actor z₀).val physicalActor [] (allPrivate.trans (List.append_nil _).symm)
  simp only [atSlot,keys,DescentTerminalSliceRuns.repeatFields,List.flatMap_nil,List.append_nil,List.getElem?_map,
    empty_,Option.map_none,Option.elim_none,Config.column,Equiv.symm_apply_apply,dead,Fin.val_zero]

include fresh in
omit [Fintype B] in
theorem rotor_private_only
    (numbered : node.val=(id₀ actor z₀).val)
    (actorShape : ↥(roster z.board (R).residual (R).depth))
    (key₀ : DescentResetHostSize.Code (R).residual)
    (depth : ((cfg).reg x 1).val=key₀.val.1+1) (safe : ((cfg).reg x 2).val%2=0)
    (seen : ((cfg).reg x 3).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (headSeen : ((cfg).oldConfig.header ((cfg).basic x) 2).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (good : actorShape.val=.good side ((),key₀.val.2) physicalActor)
    (measured : DescentRecordedRotorLayers.layers a.successor.middle.rotorBits (R).packet (R).gain ((cfg).reg x 0).val=P.layers)
    (seats : P.layers*(R).batches≤(R).addresses) (space : ((sh).recipe hp).arity z₀<2^(C).fieldBits)
    (allPrivate : (DescentRetainedRangeDigits.operandCodes (fun i=>w₀ i/(cfg).grain) ((ops actor).op z₀)).flatten=
      ((R).privateRows z.board (cfg).multiplicity P.layers (cfg).grain (id₀ actor z₀).val physicalActor).map
        (DescentRotorOperandQueryROM.Shape.PrivateLane.code z.board (R) (cfg).multiplicity P.layers (cfg).grain))
    (noPort : (R).publicTap z.board (cfg).multiplicity P.layers (cfg).grain (id₀ actor z₀).val arg.val physicalActor=none) :
    (word (2:Fin 3)).val=DescentResetMetadataInputs.argumentSpan sh z₀ arg.val :=by
  have countEq := atSlot_count (r:=(ops actor).recipe) sh z₀ arg.val
  apply Eq.trans _ countEq
  exact menu.rotor_private_slots name Y j blk h g x arg node blank physical fresh d hp contact input site owner align side host first last P key actor z₀ multiple numbered actorShape key₀ depth safe seen headSeen good measured seats 2 (countEq.trans_lt ((count_le_arity (r:=(ops actor).recipe) sh hp z₀ arg.val).trans_lt space)) allPrivate noPort

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
