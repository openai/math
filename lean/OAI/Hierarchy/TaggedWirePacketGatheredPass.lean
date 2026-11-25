import OAI.Hierarchy.TaggedWirePacketGatheredGate
import OAI.Hierarchy.TaggedWirePacketGatheredOpcode
import OAI.Hierarchy.TaggedWirePacketGatheredRoom

namespace OAI
/-! # The native intra-packet installation factor on the selected row of the full physical pass -/
noncomputable section
open scoped Fin.CommRing
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Diagonal.MotifOuterTerms Routing Tagged AdaptiveProbe TurnShelf CalendarTape
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators

variable {F V : Type} [Field F] [Fintype V] {S N H copies D K count p e W r : ℕ}
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

theorem gathered_pass (shape : gs pick=R.post c) (away : ∀i,i≠pick→Subsingleton (State (gs i) s))
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
    (roleBits : 2^p≤2^W) (laneBits : 2^e≤2^W) :
    let out:=cast (congrArg (fun U=>State U s) shape) (blockPortState gs s ((splitPortState rest (∑i,gs i) s z).2) pick)
    ∀y,TypedWiring.value (installNet F ctl (packetData roles (2^e) (neighborPin roles zero post)))
        (Sum.elim v (packedMiddle c s (middlePlace R c s (2^e) oldFit) y))=
      Installs.transport (R.shape c) rfl (R.install.operator R.order (R.bits c) R.ordinal) s y out := by
  let out:=cast (congrArg (fun U=>State U s) shape) (blockPortState gs s ((splitPortState rest (∑i,gs i) s z).2) pick)
  have fit:=PacketTurns.gathered_fits old phys run w R.ordinal parts short turns
    (sectors.trans_le roleBits) live (fun i=>(chordFit i).trans laneBits)
  apply gathered_gate R c s parts short turns ctl post zero v out (fun p i=>(z p).val.testBit i)
    cap sectors oldFit chordFit _ _ _ data pad fit
  · intro q
    have h : gs pick q.val.1≤(∑i,gs i) q.val.1 := by
      simpa only [Finsupp.finsetSum_apply] using Finset.single_le_sum (f:=fun i=>gs i q.val.1)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ pick)
    rw [←show gs pick=installedWidths phys mass from shape.trans (wout).symm]
    exact h.trans (Nat.le_add_left ..)
  · intro q j
    rw [show (out q).val=((blockPortState gs s ((splitPortState rest (∑i,gs i) s z).2) pick) q).val
      from PacketNeighbor.state_cast_val shape s _ q]
    exact (PassMatrix.active_digit rest gs pick s away z q
      (j.cast (congrArg (fun z : Widths S=>z q.val.1) (shape.trans (wout).symm).symm))).symm
  · dsimp only
    intro t f
    rw [cpu]
    exact congrArg (fun x : Word W=>x.val.testBit (projection f).2)
      (PacketTurns.gathered_column old phys run w R.ordinal o mem rowArg geom sites rows parts width nbr mounted
        short turns party here live t (projection f).1)

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
