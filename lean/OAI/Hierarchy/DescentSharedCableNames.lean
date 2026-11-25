import OAI.Hierarchy.DescentSignedCableFields
import OAI.Hierarchy.DescentSharedCableSerial
import OAI.Hierarchy.DescentStageCablePorts
import OAI.Hierarchy.DescentPackingOrdinals

namespace OAI
/-! # Chronological signed cable slots at an actual measured group stage -/
namespace Hierarchy.DescentSharedCableNames
open DescentColonies DescentSIMDLookup DescentSixParty DescentHostDirectory
open scoped Classical BigOperators
noncomputable section

namespace Stage
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
abbrev Grain := Σe : W.graph.Edge,Fin (A.grainCount e)
abbrev Host (J V : Type) (k : ℕ) := (J×V)×Block k

def stream := DescentPacking.orderedUnits A.grainCount native native.injective

def home (u : W.graph.Site) : Host J V k := (A.pos u,A.block u)
def source : Ends (Host J V k) (Fintype.card (Grain A)) where
  src t:=home A (W.graph.src (((stream A native).symm t).1))
  dst t:=home A (W.graph.dst (((stream A native).symm t).1))
local notation "B" => source A native

def recover (h : Host J V k) : A.CellPorts h.1.1 h.1.2 h.2→Grain A
  | .inl ⟨e,u⟩=>⟨e.val,u⟩
  | .inr ⟨e,u⟩=>⟨e.val,u⟩

/-- Choose the source incidence when a grain is a loop; the target record
will address this very same local cable field. -/
def asPort (h : Host J V k) (j : ↥((B).incident h)) : A.CellPorts h.1.1 h.1.2 h.2 :=
  let q := (stream A native).symm j.val
  if left : ((B).src j.val)=h then
    .inl ⟨⟨q.1,congrArg Prod.fst left,congrArg Prod.snd left⟩,q.2⟩
  else
    have right : (B).dst j.val=h := (show (B).src j.val=h ∨ (B).dst j.val=h by simpa [Ends.incident] using j.property).resolve_left left
    .inr ⟨⟨q.1,congrArg Prod.fst right,congrArg Prod.snd right⟩,q.2⟩

theorem recover_port (h : Host J V k) (j : ↥((B).incident h)) :
    recover A h (asPort A native h j)=(stream A native).symm j.val := by
  by_cases left : (B).src j.val=h <;> simp [asPort,left,recover]

theorem measured (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (h : Host J V k) :
    ((B).incident h).card≤A.cap := by
  have inj : Function.Injective (asPort A native h) := by
    intro j k eqn
    have back:=congrArg (recover A h) eqn
    rw [recover_port,recover_port] at back
    exact Subtype.ext ((stream A native).symm.injective back)
  have count:=Fintype.card_le_of_injective (asPort A native h) inj
  exact (show ((B).incident h).card≤Fintype.card (A.CellPorts h.1.1 h.1.2 h.2) by simpa using count).trans
    (A.local_port_count S ready h.1.1 h.1.2 h.2)

def putAt (x : Block k) : J×V ↪ Host J V k := ⟨fun h=>(h,x),fun _ _ h=>congrArg Prod.fst h⟩
def near (h : Host J V k) := (groupedNear A.near h.1).map (putAt h.2)

theorem near_room (h : Host J V k) : (near A h).card≤A.degree := by
  simpa only [near,Finset.card_map,grouped_degree] using A.degreeBound h.1.2

theorem connected (q : Fin (Fintype.card (Grain A))) : (B).dst q∈near A ((B).src q) ∧ (B).src q∈near A ((B).dst q) := by
  let e:=((stream A native).symm q).1
  exact ⟨Finset.mem_map.mpr ⟨A.pos (W.graph.dst e),(A.peers e).1,Prod.ext rfl (A.same e)⟩,
    Finset.mem_map.mpr ⟨A.pos (W.graph.src e),(A.peers e).2,Prod.ext rfl (A.same e).symm⟩⟩

def neighbors (names : Host J V k↪ℕ) := (B).neighbors (near A) names (near_room A) (connected A native)

def ofPort (h : Host J V k) (q : A.CellPorts h.1.1 h.1.2 h.2) : ↥((B).incident h) := by
  cases q with
  | inl q => exact ⟨(stream A native ⟨q.1.val,q.2⟩),by
      apply Finset.mem_filter.mpr;refine ⟨Finset.mem_univ _,Or.inl ?_⟩
      simpa only [source,Equiv.symm_apply_apply,home] using Prod.ext q.1.property.1 q.1.property.2⟩
  | inr q => exact ⟨(stream A native ⟨q.1.val,q.2⟩),by
      apply Finset.mem_filter.mpr;refine ⟨Finset.mem_univ _,Or.inr ?_⟩
      simpa only [source,Equiv.symm_apply_apply,home] using Prod.ext q.1.property.1 q.1.property.2⟩

private theorem ofPort_val (h : Host J V k) (q : A.CellPorts h.1.1 h.1.2 h.2) :
    (ofPort A native h q).val=stream A native (recover A h q) := by
  cases q <;> rfl

def signedBit (h : Host J V k) : A.CellPorts h.1.1 h.1.2 h.2→Fin 2 := Sum.elim (fun _=>0) (fun _=>1)

def signed (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) : A.PortOrder (2*A.cap) := fun h x=>
  let H : Host J V k := (h,x)
  let slot q:=(B).position (measured A native S ready) H (ofPort A native H q)
  { toFun := fun q=>finProdFinEquiv (signedBit A H q,slot q)
    inj' := by
      intro a b eqn
      have parts := finProdFinEquiv.injective eqn
      have bits:=congrArg Prod.fst parts
      have poseq:=congrArg Prod.snd parts
      have same := ((B).position (measured A native S ready) H).injective poseq
      have values:=congrArg Subtype.val same
      change (ofPort A native H a).val=(ofPort A native H b).val at values
      rw [ofPort_val,ofPort_val] at values
      have source:=(stream A native).injective values
      cases a with
      | inl a => cases b with
        | inl b =>
          obtain ⟨⟨ae,ap⟩,au⟩:=a
          obtain ⟨⟨be,bp⟩,bu⟩:=b
          change (Sigma.mk ae au : Grain A)=⟨be,bu⟩ at source
          cases source;rfl
        | inr b => exact False.elim (by change (0:Fin 2)=1 at bits;exact (by decide : (0:Fin 2)≠1) bits)
      | inr a => cases b with
        | inl b => exact False.elim (by change (1:Fin 2)=0 at bits;exact (by decide : (1:Fin 2)≠0) bits)
        | inr b =>
          obtain ⟨⟨ae,ap⟩,au⟩:=a
          obtain ⟨⟨be,bp⟩,bu⟩:=b
          change (Sigma.mk ae au : Grain A)=⟨be,bu⟩ at source
          cases source;rfl }
abbrev Positive := { e : W.graph.Edge // 0<A.grainCount e }

def firstAt (h : Host J V k) (e : Positive A) (atSource : home A (W.graph.src e.val)=h) : ↥((B).incident h) :=
  ⟨stream A native ⟨e.val,⟨0,e.property⟩⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl (by
    simpa only [source,Equiv.symm_apply_apply] using atSource)⟩⟩

def outgoingAt (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (h : Host J V k) (e : Positive A)
    (atSource : home A (W.graph.src e.val)=h) := (B).position (measured A native S ready) h (firstAt A native h e atSource)

/-- The positive old cable is uniquely identified by the first grain's
physical slot at its own true source, irrespective of its total width. -/
def outgoing (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (e : Positive A) : Fin A.cap :=
  outgoingAt A native S ready (home A (W.graph.src e.val)) e rfl

theorem positive_before (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (h : Host J V k) (e f : Positive A)
    (ep : home A (W.graph.src e.val)=h) (fp : home A (W.graph.src f.val)=h) (old : native e.val<native f.val) :
    outgoingAt A native S ready h e ep<outgoingAt A native S ready h f fp := by
  apply ((B).position_lt (measured A native S ready) h _ _).2
  change (stream A native ⟨e.val,⟨0,e.property⟩⟩).val < (stream A native ⟨f.val,⟨0,f.property⟩⟩).val
  simp only [stream,DescentPacking.orderedUnits_val,Nat.add_zero]
  have prior:=ProtocolRAMPortRanks.prefix_disjoint A.grainCount native old
  have pos:=e.property
  omega

theorem outgoing_lt (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (e f : Positive A)
    (same : W.graph.src e.val=W.graph.src f.val) :
    outgoing A native S ready e<outgoing A native S ready f ↔ native e.val<native f.val := by
  let h:=home A (W.graph.src f.val)
  have there : home A (W.graph.src e.val)=h:=congrArg (home A) same
  have move {x : Host J V k} (u : Positive A) (p : home A (W.graph.src u.val)=x) :
      outgoing A native S ready u=outgoingAt A native S ready x u p := by cases p;rfl
  rw [move e there,move f (rfl : home A (W.graph.src f.val)=h)]
  rcases lt_trichotomy (native e.val) (native f.val) with old|eq|rev
  · exact iff_of_true (positive_before A native S ready h e f there rfl old) old
  · have sameEdge : e=f:=Subtype.ext (native.injective eq)
    subst f
    exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · exact iff_of_false (not_lt.mpr (positive_before A native S ready h f e rfl there rev).le) (not_lt.mpr rev.le)

theorem outgoing_identify (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (e f : Positive A)
    (same : W.graph.src e.val=W.graph.src f.val) (ticket : outgoing A native S ready e=outgoing A native S ready f) : e=f := by
  rcases lt_trichotomy (native e.val) (native f.val) with less|eq|more
  · exact False.elim (((outgoing_lt A native S ready e f same).2 less).ne ticket)
  · exact Subtype.ext (native.injective eq)
  · exact False.elim (((outgoing_lt A native S ready f e same.symm).2 more).ne ticket.symm)

include native in
theorem grain_room (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (e : W.graph.Edge) :
    A.grainCount e≤A.cap := by
  let h:=home A (W.graph.src e)
  let associate (j : Fin (A.grainCount e)) : ↥((B).incident h) :=
    ⟨stream A native ⟨e,j⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl (by simp [source,h])⟩⟩
  have inj : Function.Injective associate := by
    intro a b eqn
    have grains : (Sigma.mk e a : Grain A)=⟨e,b⟩ :=(stream A native).injective (congrArg Subtype.val eqn)
    exact heq_iff_eq.1 (Sigma.mk.inj grains).2
  have count:=Fintype.card_le_of_injective associate inj
  exact (show A.grainCount e≤((B).incident h).card by simpa using count).trans (measured A native S ready h)

/-- Source-half sorting never introduces a new order among formerly active
outgoing edges in the same block. In particular the native matcher may walk
the source subbank linearly and retain precisely the old edge ordering. -/
theorem out_before (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (h : Host J V k)
    (e f : PackedCensus.Out W A.pos A.block h.1 h.2) (old : native e.val<native f.val) :
    let pick:=PackedCensus.portOfOut W A.pos A.block A.grainCount A.quantum_positive h.1 h.2
    let addr:=signed A native S ready h.1 h.2
    addr (pick e)<addr (pick f) := by
  intro pick addr
  let resident:=(B).position (measured A native S ready) h
  have sourceVal (p : PackedCensus.Out W A.pos A.block h.1 h.2) : (addr (pick p)).val=
      (resident (ofPort A native h (pick p))).val := by
    change (finProdFinEquiv ((0:Fin 2),resident (ofPort A native h (pick p)))).val=_
    simp [finProdFinEquiv_apply_val]
  change (addr (pick e)).val<(addr (pick f)).val
  rw [sourceVal,sourceVal]
  apply ((B).position_lt (measured A native S ready) h _ _).2
  change (stream A native ⟨e.val,⟨0,A.quantum_positive _ e.property.2⟩⟩).val <
    (stream A native ⟨f.val,⟨0,A.quantum_positive _ f.property.2⟩⟩).val
  simp only [stream,DescentPacking.orderedUnits_val,Nat.add_zero]
  have earlier:=ProtocolRAMPortRanks.prefix_disjoint A.grainCount native old
  have positive:=A.quantum_positive e.val e.property.2
  omega
end Stage

namespace Stage
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : Host J V k↪ℕ)
local notation "B" => source A native
local notation "fit" => measured A native S ready
local notation "roster" => neighbors A native names

def isMarkedOut (h : Host J V k) : A.CellPorts h.1.1 h.1.2 h.2→Bool
  | .inl ⟨e,u⟩=>decide (e.val∈W.core ∧ u.val=0)
  | .inr _=>false

def live (h : Host J V k) (p : A.CellPorts h.1.1 h.1.2 h.2) : Live A.degree A.cap :=
  let j := ofPort A native h p
  let v := (B).peer h j.val
  let grain := recover A h p
  { neighbor:=(roster).slot h j
    wire:=⟨(B).serial h v j.val,(B).serial_lt fit h v j.val (((B).mem_parallel ..).2 ⟨j.property,rfl⟩)⟩
    sourceWire:=outgoing A native S ready ⟨grain.1,Nat.zero_lt_of_lt grain.2.isLt⟩
    within:=grain.2.castLE (grain_room A native S ready _)
    target:=decide ((signedBit A h p).val=1)
    markedOut:=isMarkedOut A h p }

def signedPanel (h : Host J V k) (s : Fin (2*A.cap)) : Option (Live A.degree A.cap) :=
  let addr:=signed A native S ready h.1 h.2
  if hit : ∃p,addr p=s then some (live A native S ready names h hit.choose) else none

theorem signed_read (h : Host J V k) (p : A.CellPorts h.1.1 h.1.2 h.2) :
    signedPanel A native S ready names h (signed A native S ready h.1 h.2 p)=some (live A native S ready names h p) := by
  let addr:=signed A native S ready h.1 h.2
  have hit : ∃a,addr a=addr p:=⟨p,rfl⟩
  unfold signedPanel
  rw [dite_eq_left hit,addr.injective hit.choose_spec]

theorem signed_empty (h : Host J V k) (s : Fin (2*A.cap)) (none : ∀p,signed A native S ready h.1 h.2 p≠s) :
    signedPanel A native S ready names h s=Option.none := by simp [signedPanel,not_exists.mpr none]

theorem census_read (h : Host J V k) (p : A.CellPorts h.1.1 h.1.2 h.2) :
    censusTag (signedPanel A native S ready names h (signed A native S ready h.1 h.2 p))=
      if isMarkedOut A h p then 3 else 1 := by rw [signed_read];rfl

theorem census_unused (h : Host J V k) (s : Fin (2*A.cap)) (none : ∀p,signed A native S ready h.1 h.2 p≠s) :
    censusTag (signedPanel A native S ready names h s)=0 := by rw [signed_empty A native S ready names h s none];rfl
theorem marked_iff (h : Host J V k) (p : A.CellPorts h.1.1 h.1.2 h.2) :
    isMarkedOut A h p=true ↔ ∃o,PackedCensus.portOfOut W A.pos A.block A.grainCount A.quantum_positive h.1 h.2 o=p := by
  constructor
  · cases p with
    | inl p =>
      obtain ⟨⟨e,atEnd⟩,grain⟩:=p
      intro active
      change decide (e∈W.core ∧ grain.val=0)=true at active
      obtain ⟨paid,zero⟩:=of_decide_eq_true active
      have coordinate : grain=⟨0,A.quantum_positive e paid⟩:=Fin.ext zero
      subst grain
      exact ⟨⟨e,atEnd,paid⟩,rfl⟩
    | inr p => simp [isMarkedOut]
  · rintro ⟨o,rfl⟩
    change decide (o.val∈W.core ∧ (0:ℕ)=0)=true
    exact decide_eq_true ⟨o.property.2,rfl⟩


end Stage

end
end Hierarchy.DescentSharedCableNames

end OAI
