import OAI.Hierarchy.DescentSignedRosterWindows

namespace OAI
/-! # Signed windows from a consecutive emission of normalized reset cables -/

noncomputable section
set_option quotPrecheck false

namespace Hierarchy.DescentResetWindowFields
open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase DescentNextSignedWindow
open scoped Classical

variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J]
  [Fintype V] [DecidableEq V] [Fintype E] {d k i : ℕ} {bits : P → ℕ}
  {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge ↪ ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : Stage.Host J V k ↪ ℕ)
local notation "B" => Stage.source A native
local notation "stream" => Stage.stream A native
local notation "terms" => Stage.measured A native S ready
local notation "live" => DescentPackedOperand.Public.endpoint A native S ready names
variable (C : Blocks (Stage.source A native) E) (marked : E → Prop)

/-- A marked parent emits separate cables. All grains of an unmarked parent
belong to one cable, whose first grain supplies their common source handle. -/
structure Emission where
  units : (Σ e, Fin (C.count e)) ≃ Stage.Grain A
  order_eq : ∀ e j, C.order ⟨e,j⟩ = stream (units ⟨e,j⟩)
  within_at : ∀ e j, (units ⟨e,j⟩).2.val = if marked e then 0 else j.val
  core_at : ∀ e j, (units ⟨e,j⟩).1 ∈ W.core ↔ marked e
  first_of_edge : ∀ e (j : Fin (C.count e)),
    units ⟨e,if marked e then j else ⟨0,Nat.zero_lt_of_lt j.isLt⟩⟩ =
      ⟨(units ⟨e,j⟩).1,⟨0,Nat.zero_lt_of_lt (units ⟨e,j⟩).2.isLt⟩⟩

variable (emit : Emission A native C marked)

omit [Fintype E] in
theorem src_at (e : E) (j : Fin (C.count e)) :
    Stage.home A (W.graph.src (emit.units ⟨e,j⟩).1) = C.src e := by
  have ends := C.atSource e j
  rw [emit.order_eq] at ends
  simpa only [Stage.source,Equiv.symm_apply_apply] using ends

omit [Fintype E] in
theorem dst_at (e : E) (j : Fin (C.count e)) :
    Stage.home A (W.graph.dst (emit.units ⟨e,j⟩).1) = C.dst e := by
  have ends := C.atTarget e j
  rw [emit.order_eq] at ends
  simpa only [Stage.source,Equiv.symm_apply_apply] using ends

omit [Fintype E] in
theorem serial (e : E) (j : Fin (C.count e)) (side : Bool) :
    (live side (emit.units ⟨e,j⟩)).wire.val =
      (B).serial (C.src e) (C.dst e) (C.order ⟨e,⟨0,Nat.zero_lt_of_lt j.isLt⟩⟩)+j.val := by
  let x := emit.units ⟨e,j⟩
  let t := C.order ⟨e,j⟩
  have order : stream x = t := (emit.order_eq e j).symm
  have src := src_at A native C marked emit e j
  have dst := dst_at A native C marked emit e j
  have atSrc : (B).src t = C.src e := C.atSource e j
  have atDst : (B).dst t = C.dst e := C.atTarget e j
  have bound := Incidence.parallel_child C e j
  cases side with
  | false =>
    change (B).serial (Stage.home A (W.graph.src x.1)) ((B).peer _ (stream x)) (stream x) = _
    rw [order, src]
    have peer : (B).peer (C.src e) t = C.dst e := (ite_eq_left atSrc).trans atDst
    rw [peer]
    exact bound
  | true =>
    change (B).serial (Stage.home A (W.graph.dst x.1)) ((B).peer _ (stream x)) (stream x) = _
    rw [order, dst]
    have peer : (B).peer (C.dst e) t = C.src e := by
      by_cases same : (B).src t = C.dst e
      · exact (ite_eq_left same).trans (atDst.trans (same.symm.trans atSrc))
      · exact (ite_eq_right same).trans atSrc
    rw [peer]
    exact (by simpa only [atSrc,atDst] using ((B).both_ends t).symm : (B).serial (C.dst e) (C.src e) t = _).trans bound

omit [Fintype E] in
theorem metadata (e : E) (j : Fin (C.count e)) (side : Bool) :
    (live side (emit.units ⟨e,j⟩)).within.val = (if marked e then 0 else j.val) ∧
    (live side (emit.units ⟨e,j⟩)).target = side ∧
    (live side (emit.units ⟨e,j⟩)).markedOut = (decide (marked e) && !side) := by
  have offset := emit.within_at e j
  have core := emit.core_at e j
  cases side <;> by_cases active : marked e <;>
    simp [DescentPackedOperand.Public.endpoint,Stage.live,Stage.recover,Stage.isMarkedOut,
      Stage.signedBit,Exchange.sourcePort,Exchange.targetPort,offset,core,active]
  all_goals simpa only [active, ite_true, ite_false] using! offset

omit [Fintype E] in
theorem sourceWire (e : E) (j : Fin (C.count e)) (side : Bool) :
    let root := C.src e
    let member : Local C root := ⟨e,Nat.zero_lt_of_lt j.isLt,Or.inl rfl⟩
    (live side (emit.units ⟨e,j⟩)).sourceWire.val =
      ((B).position terms root (Incidence.candidate C root member ⟨0,member.property.1⟩)).val+
        (if marked e then j.val else 0) := by
  intro root member
  let x := emit.units ⟨e,j⟩
  let pos : Stage.Positive A := ⟨x.1,Nat.zero_lt_of_lt x.2.isLt⟩
  let first : Fin (C.count e) := if marked e then j else ⟨0,Nat.zero_lt_of_lt j.isLt⟩
  have origin := src_at A native C marked emit e j
  have transport (h : Stage.Host J V k) (eqn : Stage.home A (W.graph.src pos.val)=h) :
      Stage.outgoing A native S ready pos = Stage.outgoingAt A native S ready h pos eqn := by
    subst h
    rfl
  have data : (live side x).sourceWire=Stage.outgoing A native S ready pos := by cases side <;> rfl
  have atFirst : Stage.firstAt A native root pos origin=Incidence.candidate C root member first := by
    apply Subtype.ext
    change stream ⟨x.1,⟨0,pos.property⟩⟩=C.order ⟨e,first⟩
    rw [emit.order_eq]
    exact congrArg stream (emit.first_of_edge e j).symm
  rw [data,transport root origin]
  change ((B).position terms root (Stage.firstAt A native root pos origin)).val=_
  rw [atFirst,Incidence.child C root terms member first]
  by_cases yes : marked e <;> simp only [first,yes,ite_true,ite_false]

local notation "Host" => Stage.Host J V k
local notation "Face" => Roster.Face A native C
local notation "Unit" => GrainPorts.Unit A native C

def record (h : Host) (u : Face h) (neighbor : Fin A.degree) : Record A.degree A.cap :=
  let e := u.val.1
  let first : Fin (C.count e) := ⟨0,u.property.1⟩
  let root := C.src e
  let src : Local C root := ⟨e,u.property.1,Or.inl rfl⟩
  { side := u.val.2, neighbor := neighbor, marked := decide (marked e), count := C.count e,
    position := ((B).position terms h (Incidence.candidate C h (Roster.resident A native C h u) first)).val,
    shared := (B).serial root (C.dst e) (C.order ⟨e,first⟩),
    atSource := ((B).position terms root (Incidence.candidate C root src first)).val }

local notation "rec" => record A native S ready C marked

include emit in
omit [Fintype E] in
theorem render_actual (h : Host) (t : Unit h) (neighbor : Fin A.degree)
    (peer : (Stage.live A native S ready names h (GrainPorts.port A native C h t)).neighbor=neighbor) :
    render (rec h (Roster.face A native C h t) neighbor) t.val.1.2.val =
      some (Stage.live A native S ready names h (GrainPorts.port A native C h t)) := by
  let e := t.val.1.1
  let j := t.val.1.2
  let side := t.val.2
  have actual : Stage.live A native S ready names h (GrainPorts.port A native C h t)=
      live side (emit.units ⟨e,j⟩) := by
    rw [GrainPorts.at_end]
    change live side ((stream).symm (C.order ⟨e,j⟩))=_
    rw [emit.order_eq,Equiv.symm_apply_apply]
  rw [actual] at peer ⊢
  have md := metadata A native S ready names C marked emit e j side
  apply DescentNextSignedWindow.«matches» (rec h (Roster.face A native C h t) neighbor) j _ peer
  · exact serial A native S ready names C marked emit e j side
  · have src := sourceWire A native S ready names C marked emit e j side
    by_cases hm : marked t.val.1.1 <;> simpa [record, Roster.face, e, hm] using! src
  · by_cases hm : marked t.val.1.1 <;> simpa [record, Roster.face, e, hm] using md.1
  · exact md.2.1
  · exact md.2.2

include emit in
/-- The signed SRAM window agrees with every real slot, including unused
slots and the two incident signs of a loop. -/
theorem scope {c : ℕ} (h : Host) (addr : Local C h ↪ Fin c) (neighbor : Face h → Fin A.degree)
    (near : ∀ t : Unit h, (Stage.live A native S ready names h (GrainPorts.port A native C h t)).neighbor =
      neighbor (Roster.face A native C h t)) (j : Fin (2*A.cap)) :
    let info := fun f => rec h f (neighbor f)
    let rows := Roster.rows A native C h addr info
    let panel := Stage.signedPanel A native S ready names h j
    (panel=none → ∀ a,(rows a).bind (fun r=>read r j)=none) ∧
    (∀ t,panel=some t → ∃ a,(rows a).bind (fun r=>read r j)=some t ∧
      ∀ b,b≠a → (rows b).bind (fun r=>read r j)=none) := by
  intro info rows panel
  have weight (f : Face h) : (info f).count=C.count f.val.1 := rfl
  let eqv := Roster.physical A native C h addr info weight
  apply DescentNextSignedWindow.complete A native S ready names C h rows eqv _ _ j
  · intro t
    dsimp only [eqv, rows]
    rw [Roster.physical_data A native C h addr info weight,Roster.physical_at A native C h addr info weight]
    exact GrainPorts.address A native C h S ready t
  · intro t
    dsimp only [eqv, rows]
    rw [Roster.physical_data A native C h addr info weight,Roster.physical_at A native C h addr info weight]
    exact render_actual A native S ready names C marked emit h t _ (near t)

/-- Store each surviving parent in the short incident slot of its actual
first child. Sorting and casting into the capacity preserve injectivity. -/
def residentAddress (h : Host) : Local C h ↪ Fin A.cap where
  toFun e := (B).position terms h (Incidence.candidate C h e ⟨0,e.property.1⟩)
  inj' := by
    intro e f same
    have eqn := ((B).position terms h).injective same
    have packed := congrArg Subtype.val eqn
    change C.order ⟨e.val,⟨0,e.property.1⟩⟩=C.order ⟨f.val,⟨0,f.property.1⟩⟩ at packed
    exact Subtype.ext (congrArg Sigma.fst (C.order.injective packed))

def firstUnit (h : Host) (f : Face h) : Unit h :=
  ⟨(⟨f.val.1,⟨0,f.property.1⟩⟩,f.val.2),f.property.2⟩

def neighbor (h : Host) (f : Face h) : Fin A.degree :=
  (Stage.live A native S ready names h (GrainPorts.port A native C h (firstUnit A native C h f))).neighbor

omit [Fintype E] in
private theorem portOrder (h : Host) (t : Unit h) :
    (Stage.ofPort A native h (GrainPorts.port A native C h t)).val=C.order t.val.1 := by
  have word (p : A.CellPorts h.1.1 h.1.2 h.2) :
      (Stage.ofPort A native h p).val=stream (Stage.recover A h p) := by cases p <;> rfl
  rw [word,(GrainPorts.value A native C h t).1]
  exact (stream).apply_symm_apply _

omit [Fintype E] in
theorem near (h : Host) (t : Unit h) :
    (Stage.live A native S ready names h (GrainPorts.port A native C h t)).neighbor=
      neighbor A native S ready names C h (Roster.face A native C h t) := by
  let u := firstUnit A native C h (Roster.face A native C h t)
  change (Stage.neighbors A native names).slot h (Stage.ofPort A native h (GrainPorts.port A native C h t))=
    (Stage.neighbors A native names).slot h (Stage.ofPort A native h (GrainPorts.port A native C h u))
  apply ((Stage.neighbors A native names).same h _ _).2
  rw [portOrder A native C h t,portOrder A native C h u]
  obtain ⟨⟨⟨e,j⟩,s⟩,atHost⟩ := t
  change (B).peer h (C.order ⟨e,j⟩)=(B).peer h (C.order ⟨e,⟨0,Nat.zero_lt_of_lt j.isLt⟩⟩)
  simp only [Ends.peer,C.atSource,C.atTarget]

/-- Canonical signed records use only actual first-grain rank and observed
first-grain neighbor, with no externally selected positions or peer digits. -/
def canonicalRows (h : Host) :=
  Roster.rows A native C h (residentAddress A native S ready C h)
    (fun f => rec h f (neighbor A native S ready names C h f))

include emit in
theorem canonical_scope (h : Host) (j : Fin (2*A.cap)) :
    let rows := canonicalRows A native S ready names C marked h
    let panel := Stage.signedPanel A native S ready names h j
    (panel=none → ∀ a,(rows a).bind (fun r=>read r j)=none) ∧
    (∀ t,panel=some t → ∃ a,(rows a).bind (fun r=>read r j)=some t ∧
      ∀ b,b≠a → (rows b).bind (fun r=>read r j)=none) :=
  scope A native S ready names C marked emit h (residentAddress A native S ready C h)
    (neighbor A native S ready names C h) (near A native S ready names C h) j

end Hierarchy.DescentResetWindowFields
end

end OAI
