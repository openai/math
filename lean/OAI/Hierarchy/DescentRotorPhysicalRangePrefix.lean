import OAI.Hierarchy.DescentRotorPrivateRangeRows

namespace OAI
/-! # Physical argument order for every good-rotor operation -/
namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentSIMDLookup DescentPhysicalSplit DescentBatchedNodeOrder DescentRotor DescentLaneGates DescentCommonHost
open DescentBatchedRotor DescentResetGates DescentRouterSlots DescentKernelHistory DescentBundleHistory
open DescentRetainedRangeDigits DescentTerminalSliceRuns DescentDenseHostOrder DescentHostDirectory
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h) (C : Shape)
local notation "Q" => DescentCommonPalette.rotor G
local notation "H₀" => Physical.host G.arcs 0 0 0 0 0

open DescentRetainedRangeDigits DescentTerminalSliceRuns
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
local notation "configuredEdge" => DescentCommonPalette.rotorEdge G D P.layers mult C.packet u
local notation "bareActor" => (DescentCommonPalette.rotorSiteEquiv G D P.layers mult C.packet u).symm
local notation "qty" => C.privateRows G mult P.layers p
local notation "code" => PrivateLane.code G C mult P.layers p

include hp in
omit [Fintype R] in
private theorem genuine {v : (A).Site} (l : Lane p (boundaryWidth A v)) (q : PrivateLane G)
    (read : (Sum.map Subtype.val Subtype.val l.port,l.start,l.stride)=(Sum.inl ((configuredEdge) q.edge),q.start,q.stride)) :
    laneCode (μ v) l=code q:=by
  have port:=congrArg Prod.fst read
  have start:=congrArg (fun a=>a.2.1) read
  have stride:=congrArg (fun a=>a.2.2) read
  change l.start=q.start at start
  change l.stride=q.stride at stride
  have cost:(μ v) l.port=q.units G C mult P.layers:=by
    rcases eqp:l.port with ⟨e,he⟩|⟨i,hi⟩
    · rw [eqp] at port
      have same:e=(configuredEdge) q.edge:=Sum.inl.inj port
      subst e
      exact C.privateUnits_width G D P.layers mult p hp q
    · rw [eqp] at port;contradiction
  change SliceCode.mk (l.start%p) l.stride (min (l.stride+1) ((μ v) l.port-l.start/p))=_
  simp only [start,stride,cost,PrivateLane.code,PrivateLane.count]

private theorem formal_list {V : Type} {grain : ℕ} {ww : V→ℕ} (units : V→ℕ) {outputs : ℕ} (o : Op outputs grain ww) :
    (operandCodes units o).flatten=List.ofFn (fun j=>laneCode units (o.arg j)):=by
  rw [show operandCodes units o=(List.ofFn fun j=>laneCode units (o.arg j)).map (fun c=>[c]) by
    simp [operandCodes,List.map_ofFn,Function.comp_def]]
  generalize List.ofFn (fun j => laneCode units (o.arg j)) = xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,List.flatten_cons,List.cons_append,List.nil_append,ih]

private def sourceCodes {V : Type} {grain : ℕ} {ww : V→ℕ} (units : V→ℕ) : LaneSource grain ww→List SliceCode
  | .wire l=>[laneCode units l]
  | .fixed _=>[]

private theorem formal_eq {V : Type} {grain : ℕ} {ww : V→ℕ} {outputs : ℕ} (units : V→ℕ) (l : Lane grain ww) (r : LaneSource grain ww) :
    (operandCodes units (equalOp (Y:=outputs) (.wire l) r)).flatten=laneCode units l::sourceCodes units r:=by
  cases r <;> simp [operandCodes,DescentLaneGates.equalOp,DescentLaneGates.expectOp,sourceCodes,List.ofFn_succ]

theorem tapOrder_spine_cast {q₁ q₀ : ℕ} (e : q₁=q₀) (r m : ℕ)
    (w₁ : Fin q₁→ℕ) (w₀ : Fin q₀→ℕ) (same : ∀i,w₁ i=w₀ (Fin.cast e i))
    (i : Fin q₁) (t : SpineRow (r:=r) (m:=m) w₁) :
    (tapOrder r m w₁ i (.inl t)).val=
      (tapOrder r m w₀ (Fin.cast e i) (.inl ⟨Fin.cast e t.1,t.2.1,t.2.2.1,
        Fin.cast (same t.1) t.2.2.2⟩)).val := by
  subst q₀
  have ew : w₁=w₀ := funext same
  cases ew
  rcases t with ⟨j,a,b,c⟩
  rfl

theorem tapOrder_selected_cast {q₁ q₀ : ℕ} (e : q₁=q₀) (r m : ℕ)
    (w₁ : Fin q₁→ℕ) (w₀ : Fin q₀→ℕ) (same : ∀i,w₁ i=w₀ (Fin.cast e i))
    (i : Fin q₁) (t : Block r m (w₁ i)) :
    (tapOrder r m w₁ i (.inr t)).val=
      (tapOrder r m w₀ (Fin.cast e i) (.inr (t.1,t.2.1,Fin.cast (same i) t.2.2))).val := by
  subst q₀
  have ew : w₁=w₀ := funext same
  cases ew
  rcases t with ⟨a,b,c⟩
  rfl

omit [Fintype R] in
theorem root_formals (v : Fin (2^n)) (r : Fin P.layers) (b : Fin C.batches) :
    (operandCodes (μ ⟨v,.inl false⟩) ((prg ⟨v,.inl false⟩).op (r,b))).flatten=
      ((qty (finProdFinEquiv (r,b)).val ⟨v,.inl false⟩).map code):=by
  rw [C.root_rows G,List.map_ofFn]
  refine (formal_list (μ ⟨v,.inl false⟩) ((prg ⟨v,.inl false⟩).op (r,b))).trans ?_
  apply congrArg List.ofFn
  funext j
  obtain ⟨t,rfl⟩:=(rowSerial G.arcs mult C.packet v).surjective j
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  exact genuine G C D p hp contact input site owner align s w first last P _ _ <|
    C.root_reference_read G D p hp contact input site owner align s w first last P key v r b t

local notation "slot₀" => bareSlot G C D P.layers mult u
local notation "row₀" => bareSpineRow G C D P
local notation "cfgBits" => tapBits D u G P

omit [Fintype U] [Fintype R] [Fintype W] in
private theorem tap_name_bare (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v)) :
    name H v i = name H₀ v (slot₀ v i) :=
  DescentCommonPalette.rotor_name_cast G D P.layers mult C.packet u v (slot₀ v i)

omit [Fintype R] in
theorem spine_formals (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v))
    (t : SpineRow (r:=P.layers) (m:=C.batches) (cfgBits v)) :
    (operandCodes (μ ⟨v,.inr i⟩) ((prg ⟨v,.inr i⟩).op (.inl t))).flatten =
      (qty (tapOrder P.layers C.batches (C.subrow G mult v) (slot₀ v i) (.inl (row₀ v t))).val
        ⟨v,.inr (slot₀ v i)⟩).map code := by
  rw [C.spine_rows G]
  change (operandCodes _ (equalOp (Y:=2^n) (.wire (tap v i true t)) (.wire (tap v i false t)))).flatten=_
  refine (formal_eq (outputs:=2^n) (μ ⟨v,.inr i⟩) (tap v i true t) (.wire (tap v i false t))).trans ?_
  change [laneCode _ (tap v i true t),laneCode _ (tap v i false t)]=[_,_]
  have side (dir : Bool) := genuine G C D p hp contact input site owner align s w first last P
    (tap v i dir t) (C.spineReference G mult P.layers p v (slot₀ v i) dir (row₀ v t))
    (C.spine_reference_read G D p hp contact input site owner align s w first last P v i dir t)
  exact congrArg₂ List.cons (side true) (congrArg List.singleton (side false))

omit [Fintype R] in
private theorem picked_codes (e : (H).Edge) (dir : Bool) (r : Fin P.layers) (b : Fin C.batches)
    (j : Fin (mult*C.packet)) :
    sourceCodes (μ (DescentPhysicalSplit.tap H (.inr (e,dir)))) (get (.inr (e,dir)) r b j) =
      [code (C.supplyReference G mult P.layers p e dir r b j.val)] := by
  have hit := C.supply_reference_read G D p hp contact input site owner align s w first last P key e dir r b j
  cases eqn : get (.inr (e,dir)) r b j with
  | fixed bit => simp [eqn] at hit
  | wire l =>
    simp only [eqn,Option.some.injEq] at hit
    exact congrArg (fun a=>[a]) (genuine G C D p hp contact input site owner align s w first last P l _ hit)

omit [Fintype R] in
private theorem leg_codes_transport (v₀ v₁ : (A).Site) (eqn : v₀=v₁)
    (l : LaneSource p (boundaryWidth A v₀)) :
    sourceCodes (μ v₁) (eqn ▸ l : LaneSource p (boundaryWidth A v₁)) = sourceCodes (μ v₀) l := by
  cases eqn
  rfl

omit [Fintype R] in
theorem selected_formals (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v))
    (t : Block P.layers C.batches (cfgBits v i)) :
    ∃ tail : List SliceCode,(operandCodes (μ ⟨v,.inr i⟩) ((prg ⟨v,.inr i⟩).op (.inr t))).flatten =
      (qty (tapOrder P.layers C.batches (C.subrow G mult v) (slot₀ v i) (.inr (row₀ v ⟨i,t⟩).2)).val
        ⟨v,.inr (slot₀ v i)⟩).map code ++ tail := by
  let backReq := C.spineReference G mult P.layers p v (slot₀ v i) true (row₀ v ⟨i,t⟩)
  have back := genuine G C D p hp contact input site owner align s w first last P _ _
    (C.spine_reference_read G D p hp contact input site owner align s w first last P v i true ⟨i,t⟩)
  have suffix (e : Leg H) (j : Fin (legBits D u G P e)) :
      ∃ tail : List SliceCode,code backReq :: sourceCodes (μ (DescentPhysicalSplit.tap H e)) (get e t.1 t.2.1 j) =
        ((match e with
          | .inl _ => [backReq]
          | .inr (edge,dir) => [backReq,C.supplyReference G mult P.layers p edge dir t.1 t.2.1 j.val]).map code) ++ tail := by
    rcases e with ⟨a,b⟩ | ⟨edge,dir⟩
    · exact ⟨_,rfl⟩
    · refine ⟨[],?_⟩
      exact congrArg (List.cons (code backReq)) (picked_codes G C D p hp contact input site owner align s w first last P key edge dir t.1 t.2.1 j)
  rw [C.selected_rows G mult P.layers p v (slot₀ v i) (row₀ v ⟨i,t⟩).2]
  change ∃ _,(operandCodes _ (equalOp (Y:=2^n) (.wire (tap v i true ⟨i,t⟩)) (mode v i t.1 t.2.1 t.2.2))).flatten=_
  obtain ⟨tail, endEq⟩ := suffix (name H v i) t.2.2
  refine ⟨tail, (formal_eq (outputs:=2^n) (μ ⟨v,.inr i⟩) (tap v i true ⟨i,t⟩) (mode v i t.1 t.2.1 t.2.2)).trans ?_⟩
  apply (congrArg₂ List.cons back (leg_codes_transport G C D p contact input site owner align s w first last P _ _ (tap_named H v i) (get (name H v i) t.1 t.2.1 t.2.2))).trans
  rw [←tap_name_bare G C D p contact input site owner align s w first last P v i]
  apply endEq.trans
  let bareRow := row₀ v ⟨i,t⟩
  have sameMatch (leg : Leg H) :
      (match leg with
        | .inl _ => [backReq]
        | .inr (e,dir) => [backReq,C.supplyReference G mult P.layers p e dir t.1 t.2.1 t.2.2.val]) =
      (let back := C.spineReference G mult P.layers p v (slot₀ v i) true ⟨slot₀ v i,bareRow.2⟩
       match (show Leg H₀ from leg) with
       | .inl _ => [back]
       | .inr (e,dir) => [back,C.supplyReference G mult P.layers p e dir bareRow.2.1 bareRow.2.2.1 bareRow.2.2.2.val]) := by
    rcases leg with x | ⟨e,dir⟩ <;> rfl
  exact congrArg (fun xs => xs.map code ++ tail) (sameMatch (name H v i))

omit [Fintype R] in
theorem spine_lane_count (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v))
    (row : SpineRow (r:=P.layers) (m:=C.batches) (cfgBits v)) :
    (tap v i true row).count (μ ⟨v,.inr i⟩) =
      (C.spineReference G mult P.layers p v (slot₀ v i) true (row₀ v row)).count G C mult P.layers p := by
  exact congrArg SliceCode.count (genuine G C D p hp contact input site owner align s w first last P _ _
    (C.spine_reference_read G D p hp contact input site owner align s w first last P v i true row))

omit [Fintype R] in
/-- The private supply socket contributes both physical operands in their circuit order. -/
theorem supply_formals (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v))
    (t : Block P.layers C.batches (cfgBits v i)) (e : (H).Edge) (dir : Bool)
    (socket : name H v i=.inr (e,dir)) :
    (operandCodes (μ ⟨v,.inr i⟩) ((prg ⟨v,.inr i⟩).op (.inr t))).flatten =
      (qty (tapOrder P.layers C.batches (C.subrow G mult v) (slot₀ v i) (.inr (row₀ v ⟨i,t⟩).2)).val
        ⟨v,.inr (slot₀ v i)⟩).map code := by
  have back := genuine G C D p hp contact input site owner align s w first last P _ _
    (C.spine_reference_read G D p hp contact input site owner align s w first last P v i true ⟨i,t⟩)
  have chosen (l : Leg H) (j : Fin (legBits D u G P l)) (received : l=.inr (e,dir)) :
      sourceCodes (μ (DescentPhysicalSplit.tap H l)) (get l t.1 t.2.1 j) =
        [code (C.supplyReference G mult P.layers p e dir t.1 t.2.1 j.val)] := by
    subst l
    exact picked_codes G C D p hp contact input site owner align s w first last P key e dir t.1 t.2.1 j
  have socket₀ := (tap_name_bare G C D p contact input site owner align s w first last P v i).symm.trans socket
  rw [C.selected_rows G mult P.layers p v (slot₀ v i) (row₀ v ⟨i,t⟩).2]
  change (operandCodes _ (equalOp (Y:=2^n) (.wire (tap v i true ⟨i,t⟩)) (mode v i t.1 t.2.1 t.2.2))).flatten=_
  apply (formal_eq (outputs:=2^n) (μ ⟨v,.inr i⟩) (tap v i true ⟨i,t⟩) (mode v i t.1 t.2.1 t.2.2)).trans
  apply (congrArg₂ List.cons back (leg_codes_transport G C D p contact input site owner align s w first last P _ _ (tap_named H v i) (get (name H v i) t.1 t.2.1 t.2.2))).trans
  apply (congrArg (List.cons _) (chosen (name H v i) t.2.2 socket)).trans
  dsimp only
  rw [socket₀]
  rfl


local notation "physical" => deviceOrder G hw C.batches p hp contact input site owner align key D (.good first last pay P)

omit [Fintype R] in
theorem rotor_formals (actor : (A).Site) (z : (prg actor).Node) :
    ∃tail : List SliceCode,(operandCodes (μ actor) ((prg actor).op z)).flatten=
      (qty (physical actor z).val (bareActor actor)).map code++tail:=by
  rcases actor with ⟨v,(_|_)|i⟩
  · rcases z with ⟨r,b⟩
    exact ⟨[],by rw [List.append_nil];exact C.root_formals G D p hp contact input site owner align s w first last P key v r b⟩
  · exact z.elim
  · rcases z with a|b
    · have ordinal : (physical ⟨v,.inr i⟩ (.inl a)).val =
          (tapOrder P.layers C.batches (C.subrow G mult v) (slot₀ v i) (.inl (row₀ v a))).val :=
        tapOrder_spine_cast (DescentCommonPalette.rotor_count_eq G D P.layers mult C.packet u v).symm
          P.layers C.batches (cfgBits v) (C.subrow G mult v) (tapBits_bare G C D P v) i a
      refine ⟨[],?_⟩
      rw [List.append_nil,ordinal]
      exact C.spine_formals G D p hp contact input site owner align s w first last P key v i a
    · have ordinal : (physical ⟨v,.inr i⟩ (.inr b)).val =
          (tapOrder P.layers C.batches (C.subrow G mult v) (slot₀ v i) (.inr (row₀ v ⟨i,b⟩).2)).val :=
        tapOrder_selected_cast (DescentCommonPalette.rotor_count_eq G D P.layers mult C.packet u v).symm
          P.layers C.batches (cfgBits v) (C.subrow G mult v) (tapBits_bare G C D P v) i b
      rw [ordinal]
      exact C.selected_formals G D p hp contact input site owner align s w first last P key v i b

omit [Fintype R] in
theorem private_span_fields (actor : (A).Site) (z : (prg actor).Node) (block : ∀a,boundaryWidth A actor a=(μ actor) a*p)
    (arg split within : ℕ) (l : PrivateLane G)
    (hit : (C.flattened G mult P.layers p (physical actor z).val (bareActor actor))[arg]?=some (l,within)) (f : Fin 3) :
    l.kept G C mult P.layers p split within (page f)=atSlot (ofProgram (μ actor) block hp (prg actor)) z arg f:=by
  obtain ⟨tail,formal⟩:=C.rotor_formals G D p hp contact input site owner align s w first last P key actor z
  exact C.private_at_slot G (μ actor) block hp (prg actor) z mult P.layers (physical actor z).val (bareActor actor) tail formal
    arg within split l hit f

omit [Fintype R] in
theorem padded_private_row (actor : (A).Site) (z : (prg actor).Node) (block : ∀a,boundaryWidth A actor a=(μ actor) a*p)
    (arg : ℕ) (outside : ((ofProgram (μ actor) block hp (prg actor)).recipe hp).arity z≤arg) :
    (C.flattened G mult P.layers p (physical actor z).val (bareActor actor))[arg]?=none:=by
  obtain ⟨tail,formal⟩:=C.rotor_formals G D p hp contact input site owner align s w first last P key actor z
  exact C.private_outside G (μ actor) block hp (prg actor) z mult P.layers (physical actor z).val (bareActor actor) tail formal arg outside

omit [Fintype R] in
theorem issued_private_range (actor : (A).Site) (z : (prg actor).Node)
    (block : ∀a,boundaryWidth A actor a=(μ actor) a*p) (arg split : ℕ) (x : Fin 4→Cell C.fieldBits)
    (active : (x 1).val>0 ∧ (x 2).val%2=0 ∧ (x 3).val<(DescentDenseHostOrder.roster G C.residual C.depth).card)
    (label : Unit×ℕ) (shape : ((DescentResetTrunkPalette.order G C.residual C.depth).symm
      ⟨(x 3).val,active.2.2⟩).val = .good s label (bareActor actor))
    (root : ((x 1).val-1,label.2)∈DescentHostDirectory.codes C.residual)
    (measured : DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val=P.layers)
    (enough : P.layers*C.batches≤C.addresses) (l : PrivateLane G) (within : ℕ)
    (hit : (C.flattened G mult P.layers p (physical actor z).val (bareActor actor))[arg]?=some (l,within)) (f : Fin 3) :
    C.flatReg G mult p split (physical actor z).val arg (page f).succ x=
      atSlot (ofProgram (μ actor) block hp (prg actor)) z arg f:=by
  rw [C.flat_table_present G mult p split _ arg x active s label (bareActor actor) shape root P.layers measured enough l within hit f,
    ←PrivateLane.range_field G C mult P.layers p split within l f]
  exact C.private_span_fields G D p hp contact input site owner align s w first last P key actor z block arg split within l hit f

omit [Fintype R] in
theorem issued_private_padding (actor : (A).Site) (z : (prg actor).Node)
    (block : ∀a,boundaryWidth A actor a=(μ actor) a*p) (arg split : ℕ) (x : Fin 4→Cell C.fieldBits)
    (active : (x 1).val>0 ∧ (x 2).val%2=0 ∧ (x 3).val<(DescentDenseHostOrder.roster G C.residual C.depth).card)
    (label : Unit×ℕ) (shape : ((DescentResetTrunkPalette.order G C.residual C.depth).symm
      ⟨(x 3).val,active.2.2⟩).val = .good s label (bareActor actor))
    (measured : DescentRecordedRotorLayers.layers n C.packet C.gain (x 0).val=P.layers)
    (outside : ((ofProgram (μ actor) block hp (prg actor)).recipe hp).arity z≤arg) (f : Fin 8) :
    C.flatReg G mult p split (physical actor z).val arg f x=0:=by
  apply C.flat_table_outside G mult p split _ arg x active s label (bareActor actor) shape _ f
  rw [measured]
  exact C.padded_private_row G D p hp contact input site owner align s w first last P key actor z block arg outside

end Physical
end
end Hierarchy.DescentRotorOperandQueryROM.Shape

end OAI
