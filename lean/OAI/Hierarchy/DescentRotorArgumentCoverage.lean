import OAI.Hierarchy.DescentRotorPhysicalRangePrefix
import OAI.Hierarchy.DescentRotorPublicOperand
import OAI.Hierarchy.DescentProgramArgumentKeys

namespace OAI
/-! # Every active rotor operand has a private cable or a selected public socket -/
namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentSIMDLookup DescentPhysicalSplit DescentBatchedNodeOrder DescentRotor DescentLaneGates DescentCommonHost
open DescentBatchedRotor DescentResetGates DescentRouterSlots DescentKernelHistory DescentBundleHistory
open DescentRetainedRangeDigits DescentTerminalSliceRuns DescentDenseHostOrder DescentHostDirectory
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1100000
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h) (C : Shape)
local notation "Q" => DescentCommonPalette.rotor G
local notation "H₀" => Physical.host G.arcs 0 0 0 0 0

open DescentRetainedRangeDigits DescentTerminalSliceRuns
private theorem terminal_prefix_length (mult layers p : ℕ) (v : Fin (2^n))
    (i : Fin (DescentPhysicalSplit.count H₀ v)) (t : Block layers C.batches (C.subrow G mult v i))
    (leg : Fin (2^n) × Bool) (socket : name H₀ v i=.inl leg) :
    (C.flattened G mult layers p (tapOrder layers C.batches (C.subrow G mult v) i (.inr t)).val
      ⟨v,.inr i⟩).length =
      (C.spineReference G mult layers p v i true ⟨i,t⟩).count G C mult layers p := by
  unfold flattened
  rw [C.selected_rows G mult layers p v i t]
  simp [socket,PrivateLane.names]

section Physical
variable {I U R W K : Type} [Fintype I] [Fintype U] [Fintype R] [Fintype W] [Field K]
variable (D p : ℕ) (hp : 0<p) (contact : I→U) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→U→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {mult num : ℕ}
variable {hw : 0<C.packet} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "u" => C.batches*p
variable (P : BaseCircuit K G mult C.packet (C.batches*p) hw
  (fun e : Item contact owner s w => first (root contact input site owner s w align e))
  (fun e : Item contact owner s w => last (link contact owner s w e)) pay) (key : I↪Fin num)
local notation "H" => Physical.host G.arcs D P.layers mult C.packet u
local notation "prg" => DescentBatchedRotor.program D C.batches p hp contact input site owner align s w G first last P key
local notation "tap" => tapLane D C.batches p hp contact input site owner align s w G first last P


local notation "A" => DescentGoodRouter.device D u contact input site owner align s w G first last P
local notation "μ" v => fun a=>boundaryWidth A v a / p
local notation "mode" => tapLegLane D u contact input site owner align s w G first last P key (m:=C.batches) (p:=p) rfl hp
local notation "get" => legLane D u contact input site owner align s w G first last P key (m:=C.batches) (p:=p) rfl hp
local notation "qty" => C.privateRows G mult P.layers p
local notation "code" => PrivateLane.code G C mult P.layers p


local notation "physical" => deviceOrder G hw C.batches p hp contact input site owner align key D (.good first last pay P)
local notation "number" a:max z:max => (physical a z).val
local notation "bareActor" => (DescentCommonPalette.rotorSiteEquiv G D P.layers mult C.packet u).symm
local notation "slot₀" => bareSlot G C D P.layers mult u
local notation "row₀" => bareSpineRow G C D P
local notation "cfgBits" => tapBits D u G P
local notation "flat" a:max z:max => C.flattened G mult P.layers p (number a z) (bareActor a)
local notation "tapSite" v:max i:max => (⟨v,.inr i⟩ : (A).Site)
local notation "back" v:max i:max t:max => tap v i true ⟨i,t⟩
local notation "mouths" => C.publicTap G mult P.layers p

/-- The public alternative retains the same concrete site and node, the
original leg/socket, and a bounded p-word of its actually connected lane. -/
def PublicArgument (actor : (A).Site) (z : (prg actor).Node) (arg : ℕ) : Prop :=
  ∃(v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H v))
    (t : Block P.layers C.batches (cfgBits v i)) (vertex : Fin (2^n)) (pin : Bool)
    (lane : Lane p (boundaryWidth A (tapSite v i))) (within : Fin (lane.count (μ (tapSite v i)))),
    (⟨actor,z⟩ : Σa,(prg a).Node)=⟨tapSite v i,.inr t⟩ ∧
    name H v i=.inl (vertex,pin) ∧ mode v i t.1 t.2.1 t.2.2=.wire lane ∧
    arg=(back v i t).count (μ (tapSite v i))+within.val ∧
    mouths (number actor z) arg (bareActor actor)=some ⟨pin,vertex,t.1.val,t.2.1.val,t.2.2.val,within.val⟩

local notation "external" => C.PublicArgument G D p hp contact input site owner align s w first last P key

omit [Fintype R] in
private theorem private_complete (actor : (A).Site) (z : (prg actor).Node)
    (blocks : ∀a,boundaryWidth A actor a=(μ actor) a*p) (arg : ℕ)
    (live : arg<((ofProgram (μ actor) blocks hp (prg actor)).keys z).length)
    (formals : (operandCodes (μ actor) ((prg actor).op z)).flatten=
      (qty (number actor z) (bareActor actor)).map code) :
    ∃q k,(flat actor z)[arg]?=some (q,k) :=by
  have all:=C.private_prefix (Y:=2^n) (width:=boundaryWidth A actor) (p:=p) G (μ actor) blocks hp (prg actor) z mult P.layers
    (number actor z) (bareActor actor) [] (formals.trans (List.append_nil _).symm)
  have size:=DescentRetainedRangeDigits.length (ofProgram (μ actor) blocks hp (prg actor)) z hp
  rw [all] at size
  have bound : arg<(flat actor z).length:=by
    change arg<((ofProgram (μ actor) blocks hp (prg actor)).recipe hp).arity z at live
    rw [←size] at live
    simpa [repeatFields] using live
  exact ⟨((flat actor z)[arg]).1,((flat actor z)[arg]).2,by simp [List.getElem?_eq_getElem bound]⟩

private def tailWords {V : Type} {width : V→ℕ} {grain : ℕ} (units : V→ℕ) :
    LaneSource grain width → ℕ
  | .fixed _=>0
  | .wire lane=>lane.count units

private theorem eq_arg_count {V : Type} {width : V→ℕ} (units : V→ℕ)
    (blocks : ∀a,width a=units a*p) (program : Program (2^n) p width)
    (headLane : Lane p width) (extra : LaneSource p width) :
    ((List.ofFn (equalOp (Y:=2^n) (.wire headLane) extra).arg).flatMap
      (laneProgramNames units blocks hp program)).length =
      headLane.count units + tailWords units extra := by
  cases extra <;> simp [tailWords,DescentLaneGates.equalOp,DescentLaneGates.expectOp,List.ofFn_succ,laneProgramNames]

private theorem offset_lt {arg head width : ℕ} (start : head≤arg) (live : arg<head+width) :
    arg-head<width := by omega

omit [Fintype R] in
private theorem terminal_coverage (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count H v))
    (t : Block P.layers C.batches (cfgBits v i)) (vertex : Fin (2^n)) (pin : Bool)
    (socket : name H v i=.inl (vertex,pin)) (blocks : ∀a,boundaryWidth A (tapSite v i) a=(μ (tapSite v i)) a*p)
    (arg : ℕ) (live : arg<((ofProgram (μ (tapSite v i)) blocks hp (prg (tapSite v i))).keys (.inr t)).length)
    (ordinal : number (tapSite v i) (.inr t) =
      (tapOrder P.layers C.batches (C.subrow G mult v) (slot₀ v i) (.inr (row₀ v ⟨i,t⟩).2)).val)
    (leftCount : (back v i t).count (μ (tapSite v i)) =
      (C.spineReference G mult P.layers p v (slot₀ v i) true (row₀ v ⟨i,t⟩)).count G C mult P.layers p) :
    (∃q k,(flat (tapSite v i) (.inr t))[arg]?=some (q,k)) ∨ external (tapSite v i) (.inr t) arg := by
  have same : name H v i=name H₀ v (slot₀ v i) :=
    DescentCommonPalette.rotor_name_cast G D P.layers mult C.packet u v (slot₀ v i)
  have socket₀ := same.symm.trans socket
  let gate : (prg (tapSite v i)).Node:=.inr t
  let headLane:=back v i t
  let units:=μ (tapSite v i)
  have prefixSize : (flat (tapSite v i) gate).length=headLane.count units :=by
    exact (congrArg (fun k => (C.flattened G mult P.layers p k ⟨v,.inr (slot₀ v i)⟩).length) ordinal).trans
      ((terminal_prefix_length G C mult P.layers p v (slot₀ v i) (row₀ v ⟨i,t⟩).2 (vertex,pin) socket₀).trans
        leftCount.symm)
  by_cases inPrefix : arg<(flat (tapSite v i) gate).length
  · exact Or.inl ⟨((flat (tapSite v i) gate)[arg]).1,((flat (tapSite v i) gate)[arg]).2,
        List.getElem?_eq_getElem inPrefix⟩
  have tailStart : headLane.count units≤arg:=by omega
  have total : ((ofProgram units blocks hp (prg (tapSite v i))).keys gate).length=
      headLane.count units+tailWords units (mode v i t.1 t.2.1 t.2.2) :=by
    apply (congrArg List.length (program_keys units blocks hp (prg (tapSite v i)) gate)).trans
    have dispatched : (prg (tapSite v i)).op gate =
        DescentLaneGates.equalOp (Y:=2^n) (.wire headLane) (mode v i t.1 t.2.1 t.2.2) := rfl
    exact (congrArg (fun op : Op (2^n) p (boundaryWidth A (tapSite v i)) =>
      ((List.ofFn op.arg).flatMap (laneProgramNames units blocks hp (prg (tapSite v i)))).length) dispatched).trans
      (eq_arg_count (n:=n) p hp units blocks (prg (tapSite v i)) headLane (mode v i t.1 t.2.1 t.2.2))
  change arg<((ofProgram units blocks hp (prg (tapSite v i))).keys gate).length at live
  rw [total] at live
  cases trace:mode v i t.1 t.2.1 t.2.2 with
  | fixed b =>
    simp [trace,tailWords] at live
    omega
  | wire lane =>
    have countEq : tailWords units (mode v i t.1 t.2.1 t.2.2) = lane.count units :=
      congrArg (tailWords units) trace
    have inside : arg < headLane.count units + lane.count units :=
      live.trans_le (congrArg (headLane.count units + ·) countEq).le
    let within : Fin (lane.count units):=⟨arg-headLane.count units,offset_lt tailStart inside⟩
    have pos : arg=headLane.count units+within.val:=by dsimp [within];omega
    refine Or.inr ⟨v,i,t,vertex,pin,lane,within,rfl,socket,trace,pos,?_⟩
    rw [pos]
    change mouths (number (tapSite v i) (.inr t))
      ((back v i t).count (μ (tapSite v i))+within.val) ⟨v,.inr (slot₀ v i)⟩=_
    rw [ordinal,leftCount]
    exact C.public_tap_at G mult P.layers p v (slot₀ v i) (row₀ v ⟨i,t⟩).2 vertex pin socket₀ within.val

omit [Fintype R] in
theorem rotor_argument_coverage (actor : (A).Site) (z : (prg actor).Node)
    (blocks : ∀a,boundaryWidth A actor a=(μ actor) a*p) (arg : ℕ)
    (live : arg<((ofProgram (μ actor) blocks hp (prg actor)).keys z).length) :
    (∃q k,(flat actor z)[arg]?=some (q,k)) ∨ external actor z arg := by
  rcases actor with ⟨v,(_|_)|i⟩
  · rcases z with ⟨r,b⟩
    apply Or.inl
    apply private_complete G C D p hp contact input site owner align s w first last P key _ _ blocks arg live
    exact C.root_formals G D p hp contact input site owner align s w first last P key v r b
  · exact z.elim
  · rcases z with spine|t
    · have ordinal : number (tapSite v i) (.inl spine) =
          (tapOrder P.layers C.batches (C.subrow G mult v) (slot₀ v i) (.inl (row₀ v spine))).val :=
        tapOrder_spine_cast (DescentCommonPalette.rotor_count_eq G D P.layers mult C.packet u v).symm
          P.layers C.batches (cfgBits v) (C.subrow G mult v) (tapBits_bare G C D P v) i spine
      apply Or.inl
      apply private_complete G C D p hp contact input site owner align s w first last P key _ _ blocks arg live
      rw [ordinal]
      exact C.spine_formals G D p hp contact input site owner align s w first last P key v i spine
    · have ordinal : number (tapSite v i) (.inr t) =
          (tapOrder P.layers C.batches (C.subrow G mult v) (slot₀ v i) (.inr (row₀ v ⟨i,t⟩).2)).val :=
        tapOrder_selected_cast (DescentCommonPalette.rotor_count_eq G D P.layers mult C.packet u v).symm
          P.layers C.batches (cfgBits v) (C.subrow G mult v) (tapBits_bare G C D P v) i t
      cases socket:name H v i with
      | inr supply =>
        obtain ⟨e,dir⟩:=supply
        apply Or.inl
        apply private_complete G C D p hp contact input site owner align s w first last P key _ _ blocks arg live
        rw [ordinal]
        exact C.supply_formals G D p hp contact input site owner align s w first last P key v i t e dir socket
      | inl terminal =>
        obtain ⟨vertex,pin⟩:=terminal
        exact terminal_coverage G C D p hp contact input site owner align s w first last P key v i t
          vertex pin socket blocks arg live ordinal
          (C.spine_lane_count G D p hp contact input site owner align s w first last P v i ⟨i,t⟩)

end Physical
end
end Hierarchy.DescentRotorOperandQueryROM.Shape

end OAI
