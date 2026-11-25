import OAI.Hierarchy.TaggedWideCalendarSocket
import OAI.Hierarchy.TaggedWirePacketGatheredPass
import OAI.Hierarchy.TaggedWideMiddleGuard

namespace OAI
/-! # One retained signed party and its actual installed turn network -/

noncomputable section
open scoped Fin.CommRing
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Tagged AdaptiveProbe TurnShelf CalendarTape
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.Diagonal MotifOuterTerms TraceWords
open scoped Classical BigOperators

variable {F V : Type} [Field F] [Fintype V] {D K p e : ℕ}

private theorem amountRoom (e : ℕ) : 2^e < 2^(e+1) := by
  rw [Nat.pow_succ]; have h : 0<2^e := by positivity
  omega

/-- This fixed branch uses the signed terminal on the literal shared intermediate
word. The guard suppresses every unused digit, and the comparator checks each
of the three native turns of every intermediate role. -/
def partyProgram (n : ℕ) (incident : Fin n×Bool→V) (qty : Fin n→Fin (e+1)→V)
    (packet : BitNetwork F (Fintype.card (V⊕Fin (middleRoom n (2^e)))))
    (ctl : Fin (n*3)×Control p e→V) (zero : V) (post : Fin D×Fin K→V) :
    BitNetwork F (Fintype.card V) :=
  hiddenEntry ((guardMiddle n (2^e) (e+1) (amountRoom e).le incident qty).network (F:=F)) packet
    (installNet F ctl (packetData n (2^e) (neighborPin n zero post)))

theorem partyProgram_bill (n : ℕ) (incident : Fin n×Bool→V) (qty : Fin n→Fin (e+1)→V)
    (packet : BitNetwork F (Fintype.card (V⊕Fin (middleRoom n (2^e)))))
    (ctl : Fin (n*3)×Control p e→V) (zero : V) (post : Fin D×Fin K→V) :
    let N:=partyProgram n incident qty packet ctl zero post
    N.cells+N.internal≤ middleRoom n (2^e)+middleRoom n (2^e)*(200*(e+1)+65)+
      (packet.cells+packet.internal)+(n*3)*(2308*TurnShelf.width p e*(e+p+2)) := by
  intro N
  unfold N partyProgram
  rw [hidden_fee,installNet_size]
  have mask := WidePadding.Ports.cost (F:=F) (guardMiddle n (2^e) (e+1) (amountRoom e).le incident qty)
  have route := TurnShelf.size F (n*3) p e
  omega

variable {S N H copies count W r : ℕ}
    {row : Row F S H copies} {phys : Fin N→Chord S} (R : RowRouting row phys) (c : Histogram (Fin H) copies) (s : Fin S)
local notation "roles" => Fintype.card R.Roles
local notation "old" => Installs.starts (source:=R.source) R.order
local notation "run" => R.install.steps R.order
local notation "w" => Installs.numbered R.order (R.bits c)
local notation "mass" => routeLoad run w
local notation "shift" => AggregatePrefix.paidShift run w R.ordinal phys
local notation "wout" => congrArg (installedWidths phys) (R.install.counted R.order (R.bits c))
local notation "before" => fun (i : Fin roles) (b : Bool)=>(halfCode i b).val
variable (rest : Widths S) (gs : Fin r→Widths S) (pick : Fin r)
local notation "total" => fun q : (portGraph S).Port s=>(rest+∑i,gs i) q.val.1
variable (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K
    (fun q => (rest+∑i,gs i) q.val.1))
local notation "after" => fun (i : Fin N) (b : Bool)=>roles*2+PacketNeighbor.index parts ((rowGraph phys).vertex i (!b))

theorem partyProgram_value (shape : gs pick=R.post c) (away : ∀i,i≠pick→Subsingleton (State (gs i) s))
    (z : State (rest+∑i,gs i) s) (short : ∀i,(run i).length≤2) (turns : Fin count≃Positions run)
    (ctl : Fin (roles*3)×Control p e→V) (post : Fin D×Fin K→V) (zero : V) (v : V→Bool)
    (cap : ∀q,total q≤K) (sectors : roles*2+D<2^p) (oldFit : ∀i,w i≤2^e)
    (chordFit : ∀i,installedWidths phys mass (phys i)≤2^e) (live : ∀i,w i<2^W)
    (o : PacketTurns.Operands fun i=>(run i).length) (mem : Memory W) (rowArg : Word W)
    (party : Expr) (width nbr : Fin D→Expr) (here : party.eval mem rowArg=(s.val : Word W))
    (geom : PacketTurns.Reads old phys run w o mem rowArg) (sites : S≤2^W) (rows : N≤2^W)
    (mounted : PacketTurns.NeighborReads mem rowArg parts width nbr)
    (cpu : ∀t f,v (ctl (t,f))=(((o.column (o.gatheredWords R.ordinal width nbr) party
      (finProdFinEquiv (t,(projection f).1))).eval mem rowArg).val.testBit (projection f).2))
    (data : ∀q j,v (post (q,j))=ChordAperture.canonical parts (fun p i=>(z p).val.testBit i) q j)
    (pad : v zero=false)
    (roleBits : 2^p≤2^W) (laneBits : 2^e≤2^W)
    (incident : Fin roles×Bool→V) (qty : Fin roles→Fin (e+1)→V)
    (packet : BitNetwork F (Fintype.card (V⊕Fin (middleRoom roles (2^e)))))
    (sides : ∀i b,v (incident (i,b))=decide ((rowGraph old).vertex i b=s))
    (amount : ∀i j,v (qty i j)=TraceWords.bits (⟨w i,(oldFit i).trans_lt (amountRoom e)⟩ : Word (e+1)) j)
    (a : State row.input s)
    (signed : ∀y,TypedWiring.value packet (Sum.elim v (packedMiddle c s (middlePlace R c s (2^e) oldFit) y))=
      row.entry c s a y) :
    let out:=cast (congrArg (fun U=>State U s) shape) (blockPortState gs s ((splitPortState rest (∑i,gs i) s z).2) pick)
    TypedWiring.value (partyProgram roles incident qty packet ctl zero post) v=R.entry c s a out := by
  intro out
  apply hidden_entry R c s _ _ _ v (middlePlace R c s (2^e) oldFit) a out
  · exact guard_middle R c s (amountRoom e).le oldFit incident qty v sides (amountRoom e) amount
  · exact signed
  · exact gathered_pass R c s rest gs pick parts shape away z short turns ctl post zero v cap sectors oldFit
      chordFit live o mem rowArg party width nbr here geom sites rows mounted cpu data pad roleBits laneBits

end Hierarchy.WireTelescope.ChosenPackets.RowRouting
end

end OAI
