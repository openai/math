import OAI.Hierarchy.DescentTerminalPeerRank
import OAI.Hierarchy.DescentTerminalPointerBasis
import OAI.Hierarchy.DescentTerminalBookCompaction

namespace OAI
/-! # Both coordinates of one fine wire read from measured terminal geometry -/
namespace Hierarchy.DescentTerminalLocalPortBook
open DescentSIMDLookup DescentTerminalPointerDigits DescentTerminalPeerChronology DescentSharedCableNames
open DescentCompiler DescentSixParty DescentColonies DescentPackedTicketChronology DescentChosenRouter
open DescentTerminalGraphRows DescentTerminalGraphPositions DescentTerminalBoundaryBasis
open DescentTerminalPortChart DescentTerminalCableOrder DescentKernelHistory DescentPacking Computability.BorderVNP.Crossing
open ThreeFlat.Routing
open scoped Classical
noncomputable section

/-- A single host computes all fine coordinates below one true short grain. -/
def operandOffset {D cap:ℕ} (all:Fin (2*cap)→Option (Stage.Live D cap)) (u:Stage.Live D cap)
    (scale low:ℕ) := lower (grains all) (grain u).1*scale+(u.within.val*scale+low)

def portOffset {D cap:ℕ} (keys:Finset ℕ) (here other group block blocks scale low:ℕ) (u:Stage.Live D cap) :=
  (keys.filter (·<wingKey here other group block blocks u)).card*scale+low

variable {F P V : Type} [Field F] [Fintype P] [Fintype V] [DecidableEq V] {groups d k i Hn : ℕ}
    {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε:ℝ}
    (A : GroupStage W G price ε (Fin groups) V k)
    (hosts : V↪Fin Hn) (S : AtomSchedule) (ready : A.StateBounds S i)
    (native : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (names : Stage.Host (Fin groups) V k↪ℕ)
    (coords : Function.Injective (fun v=>(A.pos v,A.block v)))
    (named:SiteOrder A hosts) (sorted:SourceSorted W native)
local notation "ord" => native.trans Fin.valEmbedding
local notation "H" => Hn
local notation "home" => fun v:W.graph.Site=>hosts (Prod.snd (A.pos v))
variable (v:W.graph.Site) (pin:Attached W.graph v↪ℕ) {p scale:ℕ} (hp:0<p) (whole:A.z*G.b=scale*p)
local notation "h" => Stage.home A v
local notation "r" => DescentTerminalPortChart.rank A ord S ready names v pin
local notation "live" => Stage.live A ord S ready names h
local notation "board" => Stage.signedPanel A ord S ready names h

include coords whole in
theorem cable_operand_read (u:A.CellPorts (h).1.1 (h).1.2 (h).2) (e:Incident W.graph v)
    (j:Fin (A.grainCount e.val)) (found:Stage.recover A h u=⟨e.val,j⟩) (l:Fin scale) :
    let index:=j.val*scale+l.val
    let word:Fin (poolBatchCount (W.graph.width e.val) p):=⟨index,by
      rw [repetitions A S ready hp scale whole]
      have le:=Nat.mul_le_mul_right scale j.isLt;rw [Nat.succ_mul] at le;omega⟩
    operandOffset board (live u) scale l.val =
      (DescentTerminalGraphRows.number W.graph p v r ⟨.inl e,word⟩).val := by
  intro index word
  have trueKey:=grain_read A ord S ready names v u e j found
  have alive:0<A.grainCount e.val:=Nat.zero_lt_of_lt j.isLt
  have code : r (.inl e)=(live u).neighbor.val*A.cap+((live u).wire.val-(live u).within.val):=by
    rw [positive_rank A ord S ready names v pin e alive]
    exact (congrArg Prod.fst trueKey).symm
  have localDigit:(live u).within.val=j.val:=congrArg Prod.snd trueKey
  have clip:(index+1)*p≤W.graph.width e.val:=by
    have space:=Nat.mul_le_mul_right p word.isLt
    rwa [show poolBatchCount (W.graph.width e.val) p*p=W.graph.width e.val from
      DescentTerminalGraphVolume.exact_pieces p _ hp ⟨A.grainCount e.val*scale,by
        rw [A.grainCount_fit S ready e.val,whole];ring⟩] at space
  have rd:=cable_digit A ord S ready names v coords pin hp scale whole 0 0 ∅ e index clip
    (live u).neighbor.val ((live u).wire.val-(live u).within.val) code
  change lower (grains board) (grain (live u)).1*scale+index+1=
    (DescentTerminalGraphRows.number W.graph p v r ⟨.inl e,word⟩).val+1 at rd
  simpa only [operandOffset,localDigit] using Nat.add_right_cancel rd

variable (ext:P↪ℕ) (nodes:W.graph.Site↪ℕ) (ops:∀v,Boundary W.graph v↪ℕ)
local notation "L" => order W.graph home native p ext nodes ops
include named sorted hp whole in
theorem group_read (u:A.CellPorts (h).1.1 (h).1.2 (h).2) (other:Fin H)
    (friend:hosts ((Stage.source A ord).peer h (Stage.ofPort A ord h u).val).1.2=other)
    (g:Order.Group L (home v)) (neighbor:g.val=some other) (nm:Order.At L (home v) g)
    (l:Fin scale) (j:Fin (poolBatchCount (W.graph.width (Stage.recover A h u).1) p))
    (atWord:j.val=(Stage.recover A h u).2.val*scale+l.val)
    (name:nm.val=.inl ⟨(Stage.recover A h u).1,j⟩) :
    portOffset (keySet A hosts S ready native (home v) other) (home v).val other.val (A.pos v).1.val
      (A.block v).val (2^k) scale l.val (live u)=(Order.inGroup L (home v) g nm).val := by
  have key:=wing_key A hosts S ready native names h u
  simp only [friend] at key
  change wingKey (home v).val other.val (A.pos v).1.val (A.block v).val (2^k) (live u) =
    grainKey A hosts S ready native (min (home v).val other.val) (Stage.recover A h u) at key
  rw [portOffset,key]
  exact (group_slot A hosts S ready native named sorted ext nodes ops hp whole (home v) other g neighbor
    nm (Stage.recover A h u) l j atWord name).symm

end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
