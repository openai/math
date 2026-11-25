import OAI.Hierarchy.DescentRotorOrientedQuery
import OAI.Hierarchy.DescentOperandFamilyBook

namespace OAI
/-! # Reading every private rotor operand from one mounted directed-cable dictionary -/
namespace Hierarchy.DescentRotorOperandQueryROM
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local DescentResetHostSize
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {n h : ℕ} (board : NonlinearExpanders.Graph n h)
local notation "Q" => DescentCommonPalette.rotor board

/-- This static chart includes all sides, signed endpoints, allowed residual intervals, rotor
sockets and scheduled layer-batches. The seven numerical output fields share the same chart. -/
abbrev Coord (r addresses : ℕ) :=Bool×Bool×Code r×(Q).Edge×Fin addresses
def count (r addresses : ℕ) :=2*(2*((2^(r+1))*(Fintype.card (Q).Edge*addresses)))
def index (r addresses : ℕ) : Coord board r addresses↪Fin (count board r addresses) :=
  DescentResetCableSlots.prod finTwoEquiv.symm.toEmbedding
    (DescentResetCableSlots.prod finTwoEquiv.symm.toEmbedding (DescentResetCableSlots.prod (DescentResetCableSlots.interval r)
      (DescentResetCableSlots.prod (DescentRosterOrder.compact (DescentResetWireTags.rotorWire board)) (Function.Embedding.refl _))))

structure Shape where
  depth : ℕ
  packet : ℕ
  gain : ℕ
  batches : ℕ
  residual : ℕ
  addresses : ℕ
  fieldBits : ℕ
  queryBits : ℕ
  lanes : ℕ

namespace Shape
variable (C : Shape)
local notation "J" => Fin (count board C.residual C.addresses)
local notation "P" => Coord board C.residual C.addresses
local notation "xF" => Cell C.fieldBits
def value (p : P) (x : Fin 3→xF) : Cell C.queryBits :=
  (DescentRotorOrientedQuery.word board C.depth C.packet C.gain C.batches p.2.2.2.2.val
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 x).val

def readLaw (j : J) (x : Fin 3→xF) : Cell C.queryBits :=
  if hit : ∃p,index board C.residual C.addresses p=j then C.value board hit.choose x else 0

theorem registered (p : P) (x : Fin 3→xF) :
    C.readLaw board (index board C.residual C.addresses p) x=C.value board p x := by
  have h : ∃t,index board C.residual C.addresses t=index board C.residual C.addresses p:=⟨p,rfl⟩
  simp only [readLaw,dite_eq_left h,(index board C.residual C.addresses).injective h.choose_spec]

theorem padded (j : J) (x : Fin 3→xF) (miss : ¬∃p,index board C.residual C.addresses p=j) :
    C.readLaw board j x=0:=by simp [readLaw,miss]

private theorem no_input (j : J) : C.readLaw board j (fun _=>0)=0:=by
  unfold readLaw
  split
  · simp [value,DescentRotorOrientedQuery.word,DescentFullRotorQuery.query]
  · rfl

def unit :=DescentOperandFamilyBook.unit 3 C.fieldBits
def size :=DescentOperandFamilyBook.words (count board C.residual C.addresses) 3 C.fieldBits C.lanes
def endAddress (base : ℕ) :=base+C.size board
def program (base w : ℕ) :=DescentOperandFamilyBook.program (C.readLaw board) C.lanes base w
def image {w : ℕ} (base : ℕ) (mem : Memory w) :=DescentOperandFamilyBook.image (C.readLaw board) C.lanes base mem
def expr (base : ℕ) (j : J) (src : Fin 3→Expr) :=DescentOperandFamilyBook.expr (C.readLaw board) C.lanes base j src

theorem any {w : ℕ} (base : ℕ) (mem : Memory w) (room : C.endAddress board base<2^w) :
    (C.program board base w).Exec mem (C.image board base mem) (4+10*C.size board) ∧ CheapCode (C.program board base w) ∧
    (∀t,t<base ∨ C.endAddress board base≤t→C.image board base mem t=mem t) ∧
    ∀i,Static (DescentOperandFamilyBook.tables (C.readLaw board) C.lanes base i)
      (DescentOperandFamilyBook.gate (C.readLaw board) i).eval C.lanes (C.image board base mem) :=
  DescentOperandFamilyBook.any (C.readLaw board) C.lanes base mem room

theorem expr_work (base : ℕ) (j : J) (src : Fin 3→Expr) (t : ℕ) (price : ∀i,(src i).work≤t) :
    (C.expr board base j src).work≤14+3*(t+11) :=
  DescentOperandFamilyBook.expr_work (C.readLaw board) C.lanes base j src t price

theorem issued {H G w : ℕ} (base : ℕ) (j : J) (src : Fin 3→Expr) (mem : Memory w)
    (x : Fin H→Fin G→Fin 3→xF) (held : ∀i,(src i).Fits w base)
    (prior : ∀i,Source (src i) (fun v g=>x v g i) C.lanes mem) (room : C.endAddress board base<2^w) :
    (C.expr board base j src).Fits w (C.endAddress board base) ∧
    Source (C.expr board base j src) (fun v g=>C.readLaw board j (x v g)) C.lanes (C.image board base mem) :=
  DescentOperandFamilyBook.issued (C.readLaw board) (C.no_input board) C.lanes base j src mem x held prior room

theorem size_le (w : ℕ) (limit : C.unit*C.lanes≤w/2) :
    C.size board≤(3+count board C.residual C.addresses)*(2*2^(w/2)) :=
  DescentOperandFamilyBook.size_le _ _ _ _ w limit

end Shape
end
end Hierarchy.DescentRotorOperandQueryROM

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
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


open DescentResetLocalRoster DescentRotorOperandTicket
local notation "r" => (Z).k-(T).commonDepth
local notation "sz" => 2^(Z).n



open DescentNextSignedWindow
local notation "A₁" => B.next.placement
local notation "ord₁" => B.next.order.trans Fin.valEmbedding

open DescentRotorOperandQueryROM DescentSIMDLookup
def rotorQueryShape (m span field target lanes : ℕ) : Shape :=
  ⟨height,(Z).width,f,m,r,span,field,target,lanes⟩

theorem rotor_query_at {p₀ field target lanes span : ℕ} (proof : B.Recorded p₀) (u : Host)
    (s : Bool) (g₀ : (placement).Good) (e : (DescentCommonPalette.rotor (Z).graph).Edge) (m : ℕ)
    (x : Fin 3→Cell field) (capRead : (x 0).val=input.placement.cap)
    (chosen : (x 1).val=((Z).goodLabel T g₀).val.1+1 ∧ (x 2).val%2=0)
    (face : Roster.Face A₁ ord₁ (blocks B) u) (isEdge : face.val.1=privateWire B (goodOccurrence B s g₀ e))
    (layer : Fin ((Z).circuit s g₀).layers) (batch : Fin m)
    (within : layer.val*m+batch.val<span) (wide : 2*totalLocal B<2^target) :
    let cfg:=rotorQueryShape B m span field target lanes
    let chart:=index (Z).graph r span
    (cfg.readLaw (Z).graph (chart (s,face.val.2,(Z).goodLabel T g₀,e,⟨layer.val*m+batch.val,within⟩)) x).val=
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) face).val+1 := by
  intro cfg chart
  refine (congrArg Fin.val (cfg.registered (Z).graph (s,face.val.2,(Z).goodLabel T g₀,e,⟨layer.val*m+batch.val,within⟩) x)).trans ?_
  have exactValue:=issued_signed_query B proof u s g₀ e m x capRead chosen face isEdge layer batch
  refine (congrArg (fun a : ℕ=>(a:Cell target).val) exactValue).trans ?_
  exact Fin.val_cast_of_lt (Nat.lt_of_le_of_lt (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) face).isLt wide)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
