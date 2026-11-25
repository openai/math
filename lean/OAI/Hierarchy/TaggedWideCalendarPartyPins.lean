import OAI.Hierarchy.TaggedWideCalendarPacketUse
import OAI.Hierarchy.TaggedWirePacketMiddleFieldsRead
import OAI.Hierarchy.TaggedWideCalendarDatePins

namespace OAI
/-! # Fixed ballot and gathered-word pin maps of every retained signed branch -/

noncomputable section
namespace Hierarchy.WireTelescope.PassMatrix
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal TraceWords
open Tagged WideControlJoin WideStack ProtocolRAM ProtocolRAM.Calendar WideCPU
open Probe ChosenPackets ChosenPackets.RowRouting TurnShelf
open scoped Classical BigOperators

variable {F V : Type} [Field F] [Fintype V]
abbrev Gathered (V : Type) (D width : ℕ) := (V⊕(Fin D×Fin width))⊕(Fin D×Fin width)
abbrev Seen (V : Type) (D width : ℕ) := Gathered V D width⊕Bool

/-- Constants remain literals of the final flat network, including zero-padded
native turns and bits beyond the physical RAM word. -/
def specialize (N : BitNetwork F (Fintype.card (V⊕Bool))) : BitNetwork F (Fintype.card V) :=
  WideHost.localFamily (fun _ : Unit=>N) (fun _ a=>a)

theorem specialize_value (N : BitNetwork F (Fintype.card (V⊕Bool))) (v : V→Bool) :
    TypedWiring.value (specialize N) v=TypedWiring.value N (Sum.elim v id) := by
  rw [specialize,WideHost.localFamily_eval,Fintype.prod_unique]
  rfl

omit [Field F] in
theorem specialize_cost (N : BitNetwork F (Fintype.card (V⊕Bool))) :
    (specialize N).cells+(specialize N).internal=N.cells+N.internal := by
  rw [specialize,WideHost.localFamily_size,Fintype.sum_unique]

namespace PartyPins
variable {D width n k M e p digits : ℕ}

/-- The original ballot begins with tag, candidate and counters, followed by
turn words, the two low budgets, local-neighbor keys and the middle fields. -/
def socketStart (old M D : ℕ) := old+((M*3)*5+(D+D))
def middleStart (old M D k : ℕ) := socketStart old M D+k

variable (old : ℕ) (le : n≤M) (read : ℕ→ℕ→V⊕Bool)
local notation "S" => Seen V D width
local notation "Mid" => Fin (middleRoom n (2^e))
def host (a : V⊕Bool) : S := Sum.map (fun v=>Sum.inl (Sum.inl v)) id a
def field (f : PacketTurns.MiddleField n) (b : ℕ) : S :=
  host (D:=D) (width:=width) (read (middleStart old M D k+
    (PacketTurns.middleNumber M (PacketTurns.Operands.middleLift le f)).val) b)

def turn (slot : Fin (n*3)) (f : Control p e) : S :=
  host (D:=D) (width:=width) (read (old+(finProdFinEquiv (slot,(projection f).1)).val) (projection f).2)

variable {A E B : Type} [Fintype A] [Fintype E] [Fintype B] [Nonempty (Fin k)]
    {edge : E→Chord k} {req : A→E} (P : Packet F edge req) (G : PortGraph (Fin k) B) {r : ℕ}
    (i : Fin k) (t : (portGraph k).Port i) (localEnds : Fin n→Chord k)
    (fit : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) t.val.1)
local notation "readField" => field (D:=D) (width:=width) (k:=k) old le read
local notation "source" => S⊕Mid

def keyPin (a : Fin k) (j : Fin digits) : source :=
  .inl (host (read (socketStart old M D+a.val) j.val))

def countPin (a : Fin P.terms) (j : Fin (Nat.clog 2 (r+1))) : source⊕Bool :=
  .inl (.inl (host (read (2+a.val) j.val)))

def middleBody : BitNetwork F (Fintype.card source) :=
  Middle.packetOrient localEnds i
    (fun pair j=>.inl (.inl (readField (.inr pair) j.val)))
    (fun u side j=>if side then .inl (.inl (readField (.inl (u.1,3)) j.val)) else .inr false)
    (fun j=>.inl (.inr j))
    (fun u (j : Fin (e+1))=>.inl (readField (.inl (u.1,if u.2 then 5 else 4)) j.val))
    (signedUse (cap:=2^e) P G i t fit (keyPin (M:=M) (width:=width) (n:=n) (e:=e) (digits:=digits) old read)
      (countPin (D:=D) (width:=width) (n:=n) (e:=e) read P)
      (fun h : Fin D×Fin width=>.inl (.inl (.inl (.inr h)))))

/-- One chosen menu atom and one of its public local parties. No parameter of
this circuit is the input-dependent physical placement, counts or role widths. -/
def circuit : BitNetwork F (Fintype.card (Gathered V D width)) :=
  specialize <| partyProgram n
    (fun h=>readField (.inl (h.1,if h.2 then 2 else 1)) 0)
    (fun a j=>readField (.inl (a,0)) j.val)
    (middleBody (e:=e) (digits:=digits) old le read P G i t localEnds fit)
    (fun (sf : Fin (n*3)×Control p e)=>turn (D:=D) (width:=width) old read sf.1 sf.2)
    (.inr false) (fun h=>.inl (.inr h))

/-- All factors other than the packet terminal are gather, padding and turn
circuits. Their dependence on the dense aperture is linear times its bit length. -/
def partyCost (k _D n p e digits ports terminal : ℕ) :=
  let cap:=2^e
  let pairs:=n*2
  let middle:=middleRoom n cap
  middle+middle*(200*(e+1)+65)+
    (pairs*cap+pairs*(cap*(200*(e+1)+65))+pairs*pairs*(2308*cap*(cap.log2+2))+
      (73*(ports*cap)+(177^(k*digits)*Fintype.card (Fin k → Computability.VPVNP.BurstRAM.Word digits)*terminal)))+
    (n*3)*(2308*TurnShelf.width p e*(e+p+2))

set_option maxHeartbeats 1000000 in
theorem circuit_cost :
    let net:=circuit (e:=e) (p:=p) (digits:=digits) (D:=D) (width:=width) old le read P G i t localEnds fit
    let term:=P.terminal G i t fit
    net.cells+net.internal≤partyCost k D n p e digits (Fintype.card ((portGraph k).Port i)) (term.cells+term.internal) := by
  intro net term
  unfold net circuit
  rw [specialize_cost]
  apply le_trans (partyProgram_bill ..)
  dsimp only [partyCost]
  refine Nat.add_le_add_right (Nat.add_le_add_left ?_ _) _
  unfold middleBody
  refine (Middle.packetOrient_cost (F:=F) (V:=source) (bits:=e+1) (cap:=2^e)
    localEnds i _ _ _ _ _).trans ?_
  refine Nat.add_le_add_left (Nat.add_le_add_left ?_ _) _
  exact signedUse_cost (cap:=2^e) P G i t fit _ _ _

end PartyPins
end Hierarchy.WireTelescope.PassMatrix
end

end OAI
