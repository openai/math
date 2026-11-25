import OAI.Hierarchy.DescentPackedOperandPublic
import OAI.Hierarchy.DescentParallelBaseStream

namespace OAI
/-! # Small-ROM streamed first serials of the true ordinary cable operands -/

namespace Hierarchy.DescentPackedOperand.Public
open DescentColonies DescentSixParty DescentSharedCableNames DescentSIMDLookup
open DescentParallelBase Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section

structure Roster {U E : Type} [Fintype E] [DecidableEq U] {n : ℕ} {B : Ends U n}
    (C : Blocks B E) (D K L c : ℕ) where
  address : ∀ h, Local C h ↪ Fin c
  entry : ∀ h, Local C h → Entry D K L
  peer : ∀ h e f,(entry h e).peer=(entry h f).peer ↔ other C h e=other C h f
  order : ∀ h e f,other C h e=other C h f →
    (priority (entry h e)<priority (entry h f) ↔ C.first e.val<C.first f.val)
  weight : ∀ h e,(entry h e).weight.val=C.count e.val

namespace Roster
variable {U E : Type} [Fintype E] [DecidableEq U] {n : ℕ} {B : Ends U n}
    {C : Blocks B E} {D K L c H groups : ℕ}
variable (r : Roster C D K L c) (hosts : Fin H → Fin groups → Option U)

def field (slot : Fin c) (h : Fin H) (g : Fin groups) : Option (Entry D K L) :=
  (hosts h g).bind (fun u=>place (r.address u) (r.entry u) slot)

theorem capacity (occupied : ∀ u,(B.incident u).card≤L) (slot : Fin c) (h : Fin H) (g : Fin groups) :
    ∑i,Stream.qty (r.field hosts slot h g) (r.field hosts i h g)<2^(Packed.bits L) := by
  cases eqn : hosts h g with
  | none => simp [field,eqn,Stream.qty]
  | some host =>
    simpa only [field,eqn,Option.bind_some] using Stream.capacity C host (r.address host) (r.entry host)
      (r.peer host) (r.order host) (r.weight host) slot occupied

end Roster

private theorem lane_value {H groups M w a : ℕ} {bank : Bank}
    {cells : Fin H→Fin groups→Cell a} {done : Memory w}
    (read : DescentPackedColony.Reads bank cells M done) (wordRoom : a*M≤w)
    (h : Fin H) (g : Fin groups) (hm : 0<M) :
    digit a (lane g hm).val (done (bank.base+(row H groups M (position h g hm)).val)).val=(cells h g).val := by
  let p:=position h g hm
  have inside := (data cells p).isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) wordRoom)
  have eqn : p.2.val*M+(lane g hm).val=g.val := Nat.div_add_mod' ..
  have valid : p.2.val*M+(lane g hm).val<groups := eqn.trans_lt g.isLt
  change digit a (lane g hm).val (done (bank.base+(row H groups M p).val)).val=_
  rw [read p,Fin.val_cast_of_lt inside]
  unfold data
  rw [digit_encode,dite_eq_left valid]
  exact congrArg (fun j=>(cells h j).val) (Fin.ext eqn)

variable {F P J V : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {d k i : ℕ} {bits : P→ℕ}
    {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (sites : Stage.Host J V k ↪ ℕ)
local notation "B" => Stage.source A native
local notation "stream" => Stage.stream A native
local notation "location" => Stage.Host J V k

omit [Fintype P] in
/-- The lookup table consults only the two short entries being compared.
The returned base serial is independent of the number of candidate columns. -/
theorem stream_first {E : Type} [Fintype E] {c D K H groups M w : ℕ} (C : Blocks B E)
    (r : Roster C D K A.cap c) (hosts : Fin H→Fin groups→Option location) (slot : Fin c)
    (tables : DescentPackedZip.Tables) (q : Expr) (item : Fin c→Expr) (out : Bank) (m : Memory w)
    (fit : ∀ j,DescentPackedZip.Fits tables q (item j) (PackedBase.width D K A.cap)
      (PackedBase.width D K A.cap) M out.base w)
    (rom : DescentPackedZip.Static tables (Stream.compareWord D K A.cap) M m)
    (query : DescentPackedZip.Source q (fun h g=>PackedBase.word (r.field hosts slot h g)) M m)
    (inputs : ∀ j,DescentPackedZip.Source (item j) (fun h g=>PackedBase.word (r.field hosts j h g)) M m)
    (room : out.base+H*chunks groups M<2^w) (wordRoom : Packed.bits A.cap*M≤w)
    (hm : 0<M) (h : Fin H) (g : Fin groups) (host : location) (here : hosts h g=some host)
    (e : Local C host) (atRow : r.address host e=slot) (target : Bool) :
    let op:=Stream.instruction tables q item
    let done:=image out.base (H*chunks groups M) op m
    let zero : Fin (C.count e.val):=⟨0,e.property.1⟩
    let first:=(Stage.stream A native).symm (C.order ⟨e.val,zero⟩)
    (scan w out.base (H*chunks groups M) op).Exec m done (4+H*chunks groups M*(2*op.work+4)) ∧
      digit (Packed.bits A.cap) (lane g hm).val (done (out.base+(row H groups M (position h g hm)).val)).val=
        (endpoint A native S ready sites target first).wire.val ∧ CheapCode (scan w out.base (H*chunks groups M) op) := by
  intro op done zero first
  have occupied := Stage.measured A native S ready
  obtain ⟨actual,stored,cheap⟩ := Stream.run tables q item out m fit (r.field hosts slot)
    (r.field hosts) (r.capacity hosts occupied slot) rom query inputs room
  refine ⟨actual,?_,cheap⟩
  have queryHere : r.field hosts slot h g=some (r.entry host e) := by
    simp only [Roster.field,here,Option.bind_some,←atRow,place_at]
  have every (j : Fin c) : r.field hosts j h g=place (r.address host) (r.entry host) j := by
    simp [Roster.field,here]
  have number := lane_value stored wordRoom h g hm
  rw [number]
  change ∑j,Stream.qty (r.field hosts slot h g) (r.field hosts j h g)=_
  simp_rw [queryHere,every]
  change base (place (r.address host) (r.entry host)) (r.entry host e)=_
  rw [authentic C host (r.address host) (r.entry host) (r.peer host) (r.order host) (r.weight host) e,boundary]
  have left : Stage.home A (W.graph.src first.1)=C.src e.val := C.atSource e.val zero
  have right : Stage.home A (W.graph.dst first.1)=C.dst e.val := C.atTarget e.val zero
  change (Stage.source A native).serial (C.src e.val) (C.dst e.val) (C.order ⟨e.val,zero⟩)=
    (Stage.source A native).serial (Stage.home A (W.graph.src first.1)) (Stage.home A (W.graph.dst first.1)) (stream first)
  rw [left,right]
  exact congrArg ((Stage.source A native).serial _ _) ((Stage.stream A native).apply_symm_apply _).symm

end
end Hierarchy.DescentPackedOperand.Public

end OAI
