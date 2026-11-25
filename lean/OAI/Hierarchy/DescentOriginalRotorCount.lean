import OAI.Hierarchy.DescentPhysicalBirthSpan
import OAI.Hierarchy.DescentRotorMouthSpan

namespace OAI
/-! # Argument-span census for the entire installed good bank -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentPhysicalSplit DescentResetGates DescentLaneGates DescentFallbackItemSelect
open DescentSIMDLookup DescentRetainedRangeDigits DescentBundleHistory DescentResetPublicOperandBook
open DescentResetOperandSetup DescentRotor DescentRouterSlots DescentBatchedNodeOrder
open DescentDenseHostOrder LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander
open scoped Classical Fin.CommRing
noncomputable section
open DescentKernelHistory
set_option quotPrecheck false
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
variable (actor : (DescentGoodRouter.device d ((publicOperands z roots menu.payload).rotor.batches*(publicOperands z roots menu.payload).grain) contact input site owner align side host z.board first last P).Site) (z₀ : (DescentBatchedRotor.program d (publicOperands z roots menu.payload).rotor.batches (publicOperands z roots menu.payload).grain hp contact input site owner align side host z.board first last P key actor).Node)
local notation "w₀" => DescentKernelHistory.boundaryWidth dev actor
variable (multiple : ∀i,(DescentKernelHistory.boundaryWidth (DescentGoodRouter.device d ((publicOperands z roots menu.payload).rotor.batches*(publicOperands z roots menu.payload).grain) contact input site owner align side host z.board first last P) actor i)=(DescentKernelHistory.boundaryWidth (DescentGoodRouter.device d ((publicOperands z roots menu.payload).rotor.batches*(publicOperands z roots menu.payload).grain) contact input site owner align side host z.board first last P) actor i)/(publicOperands z roots menu.payload).grain*(publicOperands z roots menu.payload).grain)
local notation "sh" => ofProgram (fun i=>w₀ i/(cfg).grain) multiple hp (ops actor)
local notation "physicalActor" => (DescentCommonPalette.rotorSiteEquiv z.board d P.layers (cfg).multiplicity (R).packet mu).symm actor
local notation "flat" => (R).flattened z.board (cfg).multiplicity P.layers (cfg).grain (id₀ actor z₀).val physicalActor

open DescentRotorOperandQueryROM.Shape DescentBatchedRotor
local notation "liveHost" => Physical.host z.board.arcs d P.layers (cfg).multiplicity (R).packet mu
local notation "archSlot" => bareSlot z.board (R) d P.layers (cfg).multiplicity mu
local notation "archRow" => bareSpineRow z.board (R) d P
local notation "nativeBits" => tapBits d mu z.board P
local notation "E" => Item contact owner side host
local notation "chron" => (Function.Embedding.subtype (fun i=>owner side (contact i)=host)).trans key
local notation "H₀" => Physical.host z.board.arcs 0 0 0 0 0
local notation "backAt" v:arg i:arg t:arg => DescentBatchedRotor.tapLane d (R).batches (cfg).grain hp contact input site owner align side host
  z.board first last P v i true ⟨i,t⟩

set_option maxHeartbeats 1000000 in
include fresh in
omit [Fintype B] in
/-- Every physical operation in the good bank is either a private root/spine
instruction, a selected supply arc, or a selected old public mouth. Each case
computes its count on the exact ordered program, including argument padding. -/
theorem physical_rotor_span (numbered : node.val=(id₀ actor z₀).val)
    (actorShape : ↥(roster z.board (R).residual (R).depth)) (key₀ : DescentResetHostSize.Code (R).residual)
    (depth : ((cfg).reg x 1).val=key₀.val.1+1) (safe : ((cfg).reg x 2).val%2=0)
    (seen : ((cfg).reg x 3).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (headSeen : ((cfg).oldConfig.header ((cfg).basic x) 2).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (good : actorShape.val=.good side ((),key₀.val.2) physicalActor)
    (measured : DescentRecordedRotorLayers.layers a.successor.middle.rotorBits (R).packet (R).gain ((cfg).reg x 0).val=P.layers)
    (seats : P.layers*(R).batches≤(R).addresses) (axis : Fin 3) (fitField : atSlot sh z₀ arg.val axis<2^(C).fieldBits)
    (slots : E↪Fin (cfg).oldConfig.count)
    (present : ∀e,(cfg).endpoints side key₀ x (slots e)=some (src e,dst e))
    (missing : ∀j,(¬∃e,slots e=j)→(cfg).endpoints side key₀ x j=none)
    (sorted : ∀e₁ e₂ : E,before ((cfg).oldItem x side) (slots e₁) (slots e₂) ↔ chron e₁<chron e₂)
    (traffic : (cfg).traffic x side key₀=DescentBaseProfile.matrixOfBundles src dst)
    (room : 2<2^(C).fieldBits) :
    (word axis).val=atSlot sh z₀ arg.val axis:=by
  classical
  have privateOnly:=menu.rotor_private_slots name Y j blk h g x arg node blank physical fresh d hp contact input site
    owner align side host first last P key actor z₀ multiple numbered actorShape key₀ depth safe seen headSeen good measured seats axis fitField
  have fit : ((cfg).reg x 3).val<(roster z.board (R).residual (R).depth).card:=seen ▸ (localRank _ _ _ actorShape).isLt
  have ix : (⟨_,fit⟩:Fin (roster z.board (R).residual (R).depth).card)=
      DescentResetTrunkPalette.order z.board (R).residual (R).depth actorShape:=Fin.ext seen
  have active : ((cfg).reg x 1).val>0 ∧ ((cfg).reg x 2).val%2=0 ∧
      ((cfg).reg x 3).val<(roster z.board (R).residual (R).depth).card:=⟨by omega,safe,fit⟩
  have prefixOrSurface:=menu.rotor_fields name Y j blk h g x arg node blank physical fresh d hp contact input site
    owner align side host first last P key actor z₀ multiple numbered active ((),key₀.val.2)
    (by simpa only [ix,Equiv.symm_apply_apply] using good)
    (by simpa only [depth,Nat.add_sub_cancel] using key₀.property) measured seats axis fitField
  rcases actor with ⟨v,(_|_)|i⟩
  · rcases z₀ with ⟨r,b⟩
    apply privateOnly
    · exact (R).root_formals z.board d (cfg).grain hp contact input site owner align side host first last P key v r b
    · rfl
  · exact z₀.elim
  · rcases z₀ with a|t
    · have ordinal : (id₀ ⟨v,.inr i⟩ (.inl a)).val =
          (tapOrder P.layers (R).batches ((R).subrow z.board (cfg).multiplicity v)
            (archSlot v i) (.inl (archRow v a))).val :=
        tapOrder_spine_cast (DescentCommonPalette.rotor_count_eq z.board d P.layers (cfg).multiplicity (R).packet mu v).symm
          P.layers (R).batches (nativeBits v) ((R).subrow z.board (cfg).multiplicity v)
          (tapBits_bare z.board (R) d P v) i a
      apply privateOnly
      · rw [ordinal]
        exact (R).spine_formals z.board d (cfg).grain hp contact input site owner align side host first last P key v i a
      · rw [ordinal]
        exact (R).public_spine_none z.board _ _ _ _ v (archSlot v i) (archRow v a)
    · have ordinal : (id₀ ⟨v,.inr i⟩ (.inr t)).val =
          (tapOrder P.layers (R).batches ((R).subrow z.board (cfg).multiplicity v)
            (archSlot v i) (.inr (archRow v ⟨i,t⟩).2)).val :=
        tapOrder_selected_cast (DescentCommonPalette.rotor_count_eq z.board d P.layers (cfg).multiplicity (R).packet mu v).symm
          P.layers (R).batches (nativeBits v) ((R).subrow z.board (cfg).multiplicity v)
          (tapBits_bare z.board (R) d P v) i t
      have socketBare : DescentPhysicalSplit.name liveHost v i =
          DescentPhysicalSplit.name H₀ v (archSlot v i) :=
        DescentCommonPalette.rotor_name_cast z.board d P.layers (cfg).multiplicity (R).packet mu v (archSlot v i)
      rcases socket:DescentPhysicalSplit.name liveHost v i with ⟨vertex,pin⟩|⟨edge,dir⟩
      · apply prefixOrSurface
        intro noPrivate
        let signed := (R).spineReference z.board (cfg).multiplicity P.layers (cfg).grain
          v (archSlot v i) true (archRow v ⟨i,t⟩)
        have size := (R).spine_lane_count z.board d (cfg).grain hp contact input site owner align side host
          first last P v i ⟨i,t⟩
        have socket₀ := socketBare.symm.trans socket
        have passed : signed.count z.board (R) (cfg).multiplicity P.layers (cfg).grain ≤ arg.val := by
          by_contra! inside
          have declared : (R).privateRows z.board (cfg).multiplicity P.layers (cfg).grain
              (tapOrder P.layers (R).batches ((R).subrow z.board (cfg).multiplicity v)
                (archSlot v i) (.inr (archRow v ⟨i,t⟩).2)).val
              ⟨v,.inr (archSlot v i)⟩ = [] ++ signed :: [] := by
            apply ((R).selected_rows z.board (cfg).multiplicity P.layers (cfg).grain v
              (archSlot v i) (archRow v ⟨i,t⟩).2).trans
            rw [socket₀]
            rfl
          have contains := (R).flatten_member z.board (cfg).multiplicity P.layers (cfg).grain _
            ⟨v,.inr (archSlot v i)⟩ signed [] [] declared ⟨arg.val,inside⟩
          simp only [List.flatMap_nil,List.length_nil,Nat.zero_add] at contains
          rw [ordinal] at noPrivate
          have impossible := noPrivate.symm.trans contains
          cases impossible
        have head : ((cfg).oldConfig.header ((cfg).basic x) 0).val≠0 := fun miss => by
          have dead := blank miss
          omega
        refine (cfg).installed_public_range d contact input site owner align side host z.board first last key hp P
          x key₀ slots present missing sorted traffic measured v i t vertex pin socket
          (arg.val-signed.count z.board (R) (cfg).multiplicity P.layers (cfg).grain) arg ?_
          node (numbered.trans ordinal) multiple actorShape depth safe seen good head (C).fieldBits room axis
        erw [size]
        exact (Nat.add_sub_of_le passed).symm
      · apply privateOnly
        · rw [ordinal]
          exact (R).supply_formals z.board d (cfg).grain hp contact input site owner align side host first last P key v i t edge dir socket
        · rw [ordinal]
          exact (R).public_private_none z.board _ _ _ _ v (archSlot v i) (archRow v ⟨i,t⟩).2
            (edge,dir) (socketBare.symm.trans socket)

include fresh in
omit [Fintype B] in
theorem physical_rotor_count (numbered : node.val=(id₀ actor z₀).val)
    (actorShape : ↥(roster z.board (R).residual (R).depth)) (key₀ : DescentResetHostSize.Code (R).residual)
    (depth : ((cfg).reg x 1).val=key₀.val.1+1) (safe : ((cfg).reg x 2).val%2=0)
    (seen : ((cfg).reg x 3).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (headSeen : ((cfg).oldConfig.header ((cfg).basic x) 2).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (good : actorShape.val=.good side ((),key₀.val.2) physicalActor)
    (measured : DescentRecordedRotorLayers.layers a.successor.middle.rotorBits (R).packet (R).gain ((cfg).reg x 0).val=P.layers)
    (seats : P.layers*(R).batches≤(R).addresses) (space : ((sh).recipe hp).arity z₀<2^(C).fieldBits)
    (slots : E↪Fin (cfg).oldConfig.count)
    (present : ∀e,(cfg).endpoints side key₀ x (slots e)=some (src e,dst e))
    (missing : ∀j,(¬∃e,slots e=j)→(cfg).endpoints side key₀ x j=none)
    (sorted : ∀e₁ e₂ : E,before ((cfg).oldItem x side) (slots e₁) (slots e₂) ↔ chron e₁<chron e₂)
    (traffic : (cfg).traffic x side key₀=DescentBaseProfile.matrixOfBundles src dst)
    (room : 2<2^(C).fieldBits) :
    (word (2:Fin 3)).val=DescentResetMetadataInputs.argumentSpan sh z₀ arg.val:=by
  have countEq := atSlot_count (r:=(ops actor).recipe) sh z₀ arg.val
  apply Eq.trans _ countEq
  exact menu.physical_rotor_span name Y j blk h g x arg node blank physical fresh d hp contact input site owner align side host first last P key actor z₀ multiple numbered actorShape key₀ depth safe seen headSeen good measured seats 2 (countEq.trans_lt ((count_le_arity (r:=(ops actor).recipe) sh hp z₀ arg.val).trans_lt space)) slots present missing sorted traffic room

private theorem tap_card_cast {q q₀ : ℕ} (eqSlots : q=q₀) (layers batches : ℕ)
    (width : Fin q→ℕ) (width₀ : Fin q₀→ℕ) (eqWidth : ∀j,width j=width₀ (j.cast eqSlots)) (i : Fin q) :
    Fintype.card (SpineRow (r:=layers) (m:=batches) width ⊕ Block layers batches (width i)) =
      Fintype.card (SpineRow (r:=layers) (m:=batches) width₀ ⊕ Block layers batches (width₀ (i.cast eqSlots))) := by
  subst q₀
  have same : width=width₀ := funext eqWidth
  cases same
  rfl

include fresh in
omit [Fintype B] in
/-- The end of the real instruction list is also the end of both native
operand directories. This applies to a blank head, to a missing root layer,
and to an ordinal beyond the combined choice and spine rows. -/
theorem physical_rotor_absent (absent : Fintype.card (ops actor).Node≤node.val)
    (actorShape : ↥(roster z.board (R).residual (R).depth)) (key₀ : DescentResetHostSize.Code (R).residual)
    (depth : ((cfg).reg x 1).val=key₀.val.1+1) (safe : ((cfg).reg x 2).val%2=0)
    (seen : ((cfg).reg x 3).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (headSeen : ((cfg).oldConfig.header ((cfg).basic x) 2).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (good : actorShape.val=.good side ((),key₀.val.2) physicalActor)
    (measured : DescentRecordedRotorLayers.layers a.successor.middle.rotorBits (R).packet (R).gain ((cfg).reg x 0).val=P.layers)
    (axis : Fin 3) : (word axis).val=0:=by
  let lanes:=(R).privateRows z.board (cfg).multiplicity P.layers (cfg).grain node.val physicalActor
  have empty_ : lanes=[] ∧ (R).publicTap z.board (cfg).multiplicity P.layers (cfg).grain node.val arg.val physicalActor=none:=by
    rcases actor with ⟨v,(_|_)|i⟩
    · have size := Fintype.card_congr (@finProdFinEquiv P.layers (R).batches)
      have count : P.layers*(R).batches≤node.val := ((size.trans (Fintype.card_fin _)).symm.le).trans absent
      change (R).privateRows z.board (cfg).multiplicity P.layers (cfg).grain node.val ⟨v,.inl false⟩=[] ∧ _
      exact ⟨by simp only [DescentRotorOperandQueryROM.Shape.privateRows,dite_eq_right (Nat.not_lt.mpr count)],rfl⟩
    · exact ⟨rfl,rfl⟩
    · let castSlot := (DescentCommonPalette.rotor_count_eq z.board d P.layers (cfg).multiplicity (R).packet mu v).symm
      let k := i.cast castSlot
      have size := tap_card_cast castSlot P.layers (R).batches (DescentResetGates.tapBits d mu z.board P v)
        ((R).subrow z.board (cfg).multiplicity v) ((R).tapBits_bare z.board d P v) i
      have count : ¬node.val<Fintype.card (SpineRow (r:=P.layers) (m:=(R).batches) ((R).subrow z.board (cfg).multiplicity v) ⊕
        Block P.layers (R).batches ((R).subrow z.board (cfg).multiplicity v k)):= Nat.not_lt.mpr (size.symm.le.trans absent)
      change (R).privateRows z.board (cfg).multiplicity P.layers (cfg).grain node.val ⟨v,.inr k⟩=[] ∧
        (R).publicTap z.board (cfg).multiplicity P.layers (cfg).grain node.val arg.val ⟨v,.inr k⟩=none
      exact ⟨by simp only [DescentRotorOperandQueryROM.Shape.privateRows,dite_eq_right count],
        by simp only [DescentRotorOperandQueryROM.Shape.publicTap,dite_eq_right count]⟩
  have fit : ((cfg).reg x 3).val<(roster z.board (R).residual (R).depth).card:=seen ▸ (localRank _ _ _ actorShape).isLt
  have ix : (⟨_,fit⟩:Fin (roster z.board (R).residual (R).depth).card)=
      DescentResetTrunkPalette.order z.board (R).residual (R).depth actorShape:=Fin.ext seen
  have active : ((cfg).reg x 1).val>0 ∧ ((cfg).reg x 2).val%2=0 ∧
      ((cfg).reg x 3).val<(roster z.board (R).residual (R).depth).card:=⟨by omega,safe,fit⟩
  have noRoot:=(R).public_selector_none z.board (cfg).multiplicity (cfg).grain node.val arg.val ((cfg).reg x)
    side key₀ physicalActor actorShape depth safe seen good (by simpa only [measured] using empty_.2)
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
  have noPrivate : prv axis=0:=by
    apply (R).flat_table_outside z.board _ _ _ _ _ _ active side ((),key₀.val.2) physicalActor
      (by simpa only [ix,Equiv.symm_apply_apply] using good)
    rw [measured]
    change (lanes.flatMap _)[arg.val]?=none
    rw [empty_.1]
    simp
  exact congrArg Fin.val (menu.selected_missing_range name Y j blk h g x arg node blank physical fresh dead axis noPrivate)


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
