import OAI.Hierarchy.DescentRotorPhysicalRangePrefix
import OAI.Hierarchy.DescentCableBlockNumber

namespace OAI
/-! # Physical edge and block of each flattened private rotor argument -/
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

/-- Physical cable, first block and number of blocks in a formal lane. -/
abbrev LaneAddress (E : Type) := Option E × ℕ × ℕ

private def laneAddress {E A : Type} {p : ℕ} {w : A→ℕ} (units : A→ℕ) (face : A→Option E)
    (l : Lane p w) : LaneAddress E := (face l.port,l.start/p,l.count units)

private def argumentAddresses {E A : Type} {p Y : ℕ} {w : A→ℕ} (units : A→ℕ) (face : A→Option E)
    (o : Op Y p w) : List (LaneAddress E):=List.ofFn fun j=>laneAddress units face (o.arg j)

private def sourceAddresses {E A : Type} {p : ℕ} {w : A→ℕ} (units : A→ℕ) (face : A→Option E) :
    LaneSource p w→List (LaneAddress E)
  | .wire l=>[laneAddress units face l]
  | .fixed _=>[]

private theorem equal_addresses {E A : Type} {p Y : ℕ} {w : A→ℕ} (units : A→ℕ) (face : A→Option E)
    (l : Lane p w) (r : LaneSource p w) :
    argumentAddresses units face (DescentLaneGates.equalOp (Y:=Y) (.wire l) r)=laneAddress units face l::sourceAddresses units face r:=by
  cases r <;> simp [argumentAddresses,laneAddress,DescentLaneGates.equalOp,DescentLaneGates.expectOp,sourceAddresses,List.ofFn_succ]

private def cableFace {d : ℕ} {P : Type} {bits : P→ℕ} (N : Computability.BorderVNP.Crossing.Network d P bits)
    (v : N.Site) (a : Boundary N v) : Option N.Edge :=
  a.elim (fun e=>some e.val) (fun _=>none)

private def storedAddress (mult levels p : ℕ) (l : PrivateLane G) : LaneAddress (Q).Edge :=
  (some l.edge,l.start/p,l.count G C mult levels p)
private def expandAddress {E : Type} (a : LaneAddress E) : List (Option (E×ℕ)) :=
  List.ofFn (fun i : Fin a.2.2=>a.1.map (fun e=>(e,a.2.1+i.val)))

private def keyAddress {E V H : Type} {p : ℕ} {w : V→ℕ} {hw : H→ℕ} (face : V→Option E) :
    BlockRef p w⊕BlockRef p hw→Option (E×ℕ)
  | .inl b=>(face b.port).map (fun e=>(e,b.block))
  | .inr _=>none

private theorem lane_words {E V H : Type} {hw : H→ℕ} {p : ℕ} {w : V→ℕ} (units : V→ℕ)
    (multiple : ∀v,w v=units v*p) (hp : 0<p) (face : V→Option E) (l : Lane p w) :
    (laneSlice (hw:=hw) units multiple hp l).names.map (keyAddress face)=
       expandAddress (laneAddress units face l):=by
  rw [Slice.names,List.map_ofFn]
  rfl

private theorem program_words {E V : Type} {Y p : ℕ} {w : V→ℕ} (units : V→ℕ)
    (multiple : ∀v,w v=units v*p) (hp : 0<p) (face : V→Option E) (P : Program Y p w) (z : P.Node) :
    ((ofProgram units multiple hp P).keys z).map (keyAddress face)=
      (argumentAddresses units face (P.op z)).flatMap expandAddress:=by
  let lanes:=List.ofFn (P.op z).arg
  let slice:=laneSlice (hw:=P.recipe.hiddenWidth) units multiple hp
  have rows : (ofProgram units multiple hp P).rows z=lanes.map (fun l=>[slice l]):=by
    dsimp only [lanes]
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    change List.ofFn (fun _ : Fin 1=>_)=[_]
    simp [List.ofFn_succ]; rfl
  have laneRows : argumentAddresses units face (P.op z)=lanes.map (laneAddress units face):=by
    simp [argumentAddresses,lanes,List.map_ofFn,Function.comp_def]
  simp only [DescentBundleHistory.Shape.keys,rows,laneRows]
  simp [List.flatMap_map,List.map_flatMap,slice,lane_words]

private def location (p : ℕ) (v : PrivateLane G×ℕ) : Option ((Q).Edge×ℕ) :=
  some (v.1.edge,v.1.start/p+v.2)

private theorem private_words (mult levels p : ℕ) (q : PrivateLane G) :
    expandAddress (storedAddress G C mult levels p q)=(q.names G C mult levels p).map (location G p):=by
  simp only [PrivateLane.names,List.map_ofFn]
  rfl


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
local notation "configuredEdge" => DescentCommonPalette.rotorEdgeEquiv G D P.layers mult C.packet u
local notation "bareActor" => Equiv.symm (DescentCommonPalette.rotorSiteEquiv G D P.layers mult C.packet u)
local notation "installedSize" => tapBits D u G P
local notation "bareIndex" => bareSlot G C D P.layers mult u
local notation "bareRow" => bareSpineRow G C D P
local notation "qty" => C.privateRows G mult P.layers p
local notation "code" => storedAddress G C mult P.layers p
local notation "face" v => fun a => Option.map (Equiv.symm configuredEdge) (cableFace A v a)

include hp in
omit [Fintype R] in
private theorem actual_address {v : (A).Site} (l : Lane p (boundaryWidth A v)) (q : PrivateLane G)
    (read : (Sum.map Subtype.val Subtype.val l.port,l.start,l.stride)=
      (Sum.inl (DescentCommonPalette.rotorEdge G D P.layers mult C.packet u q.edge),q.start,q.stride)) :
    laneAddress (μ v) (face v) l=code q:=by
  have port : Sum.map Subtype.val Subtype.val l.port=.inl ((configuredEdge) q.edge) :=
    congrArg Prod.fst read
  have start : l.start=q.start := congrArg (fun a=>a.2.1) read
  have stride : l.stride=q.stride := congrArg (fun a=>a.2.2) read
  have live : (face v) l.port=some q.edge ∧ (μ v) l.port=q.units G C mult P.layers := by
    cases eqp : l.port with
    | inl e =>
      have cable : e.val=(configuredEdge) q.edge :=
        Sum.inl.inj (by simpa only [eqp,Sum.map_inl] using port)
      constructor
      · change some ((configuredEdge).symm e.val)=some q.edge
        rw [cable,Equiv.symm_apply_apply]
      · change (A).width e.val/p=_
        rw [cable]
        exact C.privateUnits_width G D P.layers mult p hp q
    | inr pin => simp [eqp] at port
  change ((face v) l.port,l.start/p,min (l.stride+1) ((μ v) l.port-l.start/p))=_
  rw [live.1,start,stride,live.2]; rfl

omit [Fintype R] in
theorem root_address_formals (v : Fin (2^n)) (r : Fin P.layers) (b : Fin C.batches) :
    (argumentAddresses (μ ⟨v,.inl false⟩) (face ⟨v,.inl false⟩) ((prg ⟨v,.inl false⟩).op (r,b)))=
      ((qty (finProdFinEquiv (r,b)).val ⟨v,.inl false⟩).map code):=by
  rw [C.root_rows G,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  obtain ⟨t,rfl⟩:=(rowSerial G.arcs mult C.packet v).surjective j
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  exact actual_address G C D p hp contact input site owner align s w first last P _ _ <|
    C.root_reference_read G D p hp contact input site owner align s w first last P key v r b t

omit [Fintype R] in
theorem spine_address_formals (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v))
    (t : SpineRow (r:=P.layers) (m:=C.batches) (installedSize v)) :
    (argumentAddresses (μ ⟨v,.inr i⟩) (face ⟨v,.inr i⟩) ((prg ⟨v,.inr i⟩).op (.inl t)))=
      (qty (tapOrder P.layers C.batches (installedSize v) i (.inl t)).val ⟨v,.inr (bareIndex v i)⟩).map code:=by
  rw [tapOrder_spine_cast (DescentCommonPalette.rotor_count_eq G D P.layers mult C.packet u v).symm
    P.layers C.batches (installedSize v) (C.subrow G mult v) (tapBits_bare G C D P v) i t]
  refine Eq.trans ?_ (congrArg (List.map code) (C.spine_rows G mult P.layers p v (bareIndex v i) (bareRow v t)).symm)
  change (argumentAddresses _ _ (equalOp (Y:=2^n) (.wire (tap v i true t)) (.wire (tap v i false t))))=_
  refine (equal_addresses (Y:=2^n) (μ ⟨v,.inr i⟩) (face ⟨v,.inr i⟩)
    (tap v i true t) (.wire (tap v i false t))).trans ?_
  change [laneAddress _ _ (tap v i true t),laneAddress _ _ (tap v i false t)]=[_,_]
  have side (dir : Bool) := actual_address G C D p hp contact input site owner align s w first last P
    (tap v i dir t) (C.spineReference G mult P.layers p v (bareIndex v i) dir (bareRow v t))
    (C.spine_reference_read G D p hp contact input site owner align s w first last P v i dir t)
  exact congrArg₂ List.cons (side true) (congrArg List.singleton (side false))

omit [Fintype R] in
private theorem picked_addresses (e : (H).Edge) (dir : Bool) (r : Fin P.layers) (b : Fin C.batches) (j : Fin (mult*C.packet)) :
    sourceAddresses (μ (DescentPhysicalSplit.tap H (.inr (e,dir)))) (face (DescentPhysicalSplit.tap H (.inr (e,dir)))) (get (.inr (e,dir)) r b j)=
      [code (C.supplyReference G mult P.layers p e dir r b j.val)]:=by
  have hit:=C.supply_reference_read G D p hp contact input site owner align s w first last P key e dir r b j
  cases eqn:get (.inr (e,dir)) r b j with
  | fixed bit=>simp [eqn] at hit
  | wire l=>
    simp only [eqn,Option.some.injEq] at hit
    exact congrArg (fun a=>[a]) (actual_address G C D p hp contact input site owner align s w first last P l _ hit)

omit [Fintype U] [Fintype R] [Fintype W] in
private theorem address_name_bare (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v)) :
    name H v i = name H₀ v (bareIndex v i) :=
  DescentCommonPalette.rotor_name_cast G D P.layers mult C.packet u v (bareIndex v i)

omit [Fintype R] in
private theorem address_leg_transport (v₀ v₁ : (A).Site) (eqn : v₀=v₁)
    (l : LaneSource p (boundaryWidth A v₀)) :
    sourceAddresses (μ v₁) (face v₁) (eqn ▸ l : LaneSource p (boundaryWidth A v₁)) = sourceAddresses (μ v₀) (face v₀) l := by
  cases eqn
  rfl

omit [Fintype R] in
theorem selected_address_formals (v : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v))
    (t : Block P.layers C.batches (installedSize v i)) :
    ∃ tail : List (LaneAddress (Q).Edge),argumentAddresses (μ ⟨v,.inr i⟩) (face ⟨v,.inr i⟩) ((prg ⟨v,.inr i⟩).op (.inr t)) =
      (qty (tapOrder P.layers C.batches (installedSize v) i (.inr t)).val
        ⟨v,.inr (bareIndex v i)⟩).map code ++ tail := by
  let backReq := C.spineReference G mult P.layers p v (bareIndex v i) true (bareRow v ⟨i,t⟩)
  have back := actual_address G C D p hp contact input site owner align s w first last P _ _
    (C.spine_reference_read G D p hp contact input site owner align s w first last P v i true ⟨i,t⟩)
  have suffix (e : Leg H) (j : Fin (legBits D u G P e)) :
      ∃ tail : List (LaneAddress (Q).Edge),code backReq :: sourceAddresses (μ (DescentPhysicalSplit.tap H e)) (face (DescentPhysicalSplit.tap H e)) (get e t.1 t.2.1 j) =
        ((match e with
          | .inl _ => [backReq]
          | .inr (edge,dir) => [backReq,C.supplyReference G mult P.layers p edge dir t.1 t.2.1 j.val]).map code) ++ tail := by
    rcases e with ⟨a,b⟩ | ⟨edge,dir⟩
    · exact ⟨_,rfl⟩
    · refine ⟨[],?_⟩
      exact congrArg (List.cons (code backReq)) (picked_addresses G C D p hp contact input site owner align s w first last P key edge dir t.1 t.2.1 j)
  rw [tapOrder_selected_cast (DescentCommonPalette.rotor_count_eq G D P.layers mult C.packet u v).symm
    P.layers C.batches (installedSize v) (C.subrow G mult v) (tapBits_bare G C D P v) i t]
  change ∃ tail : List (LaneAddress (Q).Edge),
    argumentAddresses (μ ⟨v,.inr i⟩) (face ⟨v,.inr i⟩) ((prg ⟨v,.inr i⟩).op (.inr t)) =
      (qty (tapOrder P.layers C.batches (C.subrow G mult v) (bareIndex v i) (.inr (bareRow v ⟨i,t⟩).2)).val
        ⟨v,.inr (bareIndex v i)⟩).map code ++ tail
  rw [C.selected_rows G mult P.layers p v (bareIndex v i) (bareRow v ⟨i,t⟩).2]
  change ∃ _,argumentAddresses _ _ (DescentLaneGates.equalOp (Y:=2^n) (.wire (tap v i true ⟨i,t⟩)) (mode v i t.1 t.2.1 t.2.2))=_
  obtain ⟨tail, endEq⟩ := suffix (name H v i) t.2.2
  refine ⟨tail, (equal_addresses (Y:=2^n) (μ ⟨v,.inr i⟩) (face ⟨v,.inr i⟩) (tap v i true ⟨i,t⟩) (mode v i t.1 t.2.1 t.2.2)).trans ?_⟩
  apply (congrArg₂ List.cons back (address_leg_transport G C D p contact input site owner align s w first last P _ _ (tap_named H v i) (get (name H v i) t.1 t.2.1 t.2.2))).trans
  rw [←address_name_bare G C D p contact input site owner align s w first last P v i]
  apply endEq.trans
  let rowValue := bareRow v ⟨i,t⟩
  have sameMatch (leg : Leg H) :
      (match leg with
        | .inl _ => [backReq]
        | .inr (e,dir) => [backReq,C.supplyReference G mult P.layers p e dir t.1 t.2.1 t.2.2.val]) =
      (let back := C.spineReference G mult P.layers p v (bareIndex v i) true ⟨bareIndex v i,rowValue.2⟩
       match (show Leg H₀ from leg) with
       | .inl _ => [back]
       | .inr (e,dir) => [back,C.supplyReference G mult P.layers p e dir rowValue.2.1 rowValue.2.2.1 rowValue.2.2.2.val]) := by
    rcases leg with x | ⟨e,dir⟩ <;> rfl
  exact congrArg (fun xs => xs.map code ++ tail) (sameMatch (name H v i))


local notation "physical" => deviceOrder G hw C.batches p hp contact input site owner align key D (.good first last pay P)

omit [Fintype R] in
theorem rotor_address_formals (actor : (A).Site) (z : (prg actor).Node) :
    ∃tail : List (LaneAddress (Q).Edge),(argumentAddresses (μ actor) (face actor) ((prg actor).op z))=
      (qty (physical actor z).val (bareActor actor)).map code++tail:=by
  rcases actor with ⟨v,(_|_)|i⟩
  · rcases z with ⟨r,b⟩
    exact ⟨[],by rw [List.append_nil];exact C.root_address_formals G D p hp contact input site owner align s w first last P key v r b⟩
  · exact z.elim
  · rcases z with a|b
    · exact ⟨[],by rw [List.append_nil];exact C.spine_address_formals G D p hp contact input site owner align s w first last P key v i a⟩
    · exact C.selected_address_formals G D p hp contact input site owner align s w first last P key v i b


omit [Fintype R] in
/-- A private hit at the flattened issued ordinal determines its actual incident
device cable and the exact aligned word on that cable. -/
theorem rotor_address_key (actor : (A).Site) (z : (prg actor).Node)
    (block : ∀a,boundaryWidth A actor a=(μ actor) a*p) (arg within : ℕ) (l : PrivateLane G)
    (hit : (C.flattened G mult P.layers p (physical actor z).val (bareActor actor))[arg]?=some (l,within)) :
    ∃b : BlockRef p (boundaryWidth A actor),
      ((ofProgram (μ actor) block hp (prg actor)).keys z)[arg]?=some (.inl b) ∧
      b.cableNumber A actor=some ((configuredEdge) l.edge,l.start/p+within):=by
  let words:=(ofProgram (μ actor) block hp (prg actor)).keys z
  let origin:=C.flattened G mult P.layers p (physical actor z).val (bareActor actor)
  obtain ⟨tail,form⟩:=C.rotor_address_formals G D p hp contact input site owner align s w first last P key actor z
  have physicalWords : words.map (keyAddress (face actor))=
      origin.map (location G p)++tail.flatMap expandAddress:=by
    refine (program_words (μ actor) block hp (face actor) (prg actor) z).trans ?_
    refine (congrArg (List.flatMap expandAddress) form).trans ?_
    rw [List.flatMap_append]
    congr 1
    simp [origin,flattened,List.flatMap_map,List.map_flatMap,private_words]
  have below:arg<origin.length:=(List.getElem?_eq_some_iff.mp hit).choose
  have atArg:=congrArg (fun li=>li[arg]?) physicalWords
  rw [List.getElem?_map,List.getElem?_append_left (by simpa using below),List.getElem?_map,hit] at atArg
  obtain ⟨keyRef,found,ident⟩:=Option.map_eq_some_iff.mp atArg
  cases keyRef with
  | inr hid=>exact hid.port.elim
  | inl b=>
    refine ⟨b,found,?_⟩
    cases at_:b.port with
    | inl e =>
      have identified := ident
      simp only [keyAddress, cableFace, at_, Sum.elim_inl, location] at identified
      have decoded : ((configuredEdge).symm e.val,b.block)=(l.edge,l.start/p+within) := Option.some.inj identified
      rw [BlockRef.cableNumber, at_]
      have mounted := congrArg (fun q : (Q).Edge × ℕ => some ((configuredEdge) q.1,q.2)) decoded
      exact (congrArg (fun v : (A).Edge => some (v,b.block))
        ((configuredEdge).apply_symm_apply e.val).symm).trans mounted
    | inr f=>
      simp only [keyAddress,cableFace,at_,Sum.elim_inr,location] at ident
      contradiction



end Physical
end
end Hierarchy.DescentRotorOperandQueryROM.Shape

end OAI
