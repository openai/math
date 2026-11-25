import OAI.Hierarchy.DescentDatedSortedPathSocket
import OAI.Hierarchy.DescentSharedLeafImage
import OAI.Hierarchy.DescentDepotReceiver
import OAI.Hierarchy.DescentDatedSortedOperandAdapter

namespace OAI
/-! # Broadcast a physically decoded old walk to the live lanes of each resolver row -/
namespace Hierarchy.DescentDatedOperandReadPipeline.SortedInput
open DescentDatedSourcePathDirectory DescentSortedRoster DescentHaloWalkRAM DescentSIMDLookup DescentPackedZip
open DescentSharedLeafLookup DescentPackedColony.Phase.Arena DescentRawCablePanel DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
namespace Broadcast
variable (g : Geometry)
local notation "K" => g.hosts
local notation "G" => g.groups
local notation "M" => g.lanes
local notation "P" => g.paths
local notation "a" => g.digitBits
def finish (base : ℕ) :=Public.stop base K G M a
def layout (base : ℕ) (visited : Bank) :=Public.header base K G M a visited

/-- The literal directory is independent of the roster contents. The public host map has a sentinel
for every padded receiver and the broadcast table truncates the last word to the live groups. -/
def image (base oldHosts pitch w : ℕ) : Image w :=
  let I:=Public.literals base 1 K G M a w
  {I with value:=fun i=>if hit : i-base<K*chunks G M then
      (number (DepotRAM.Material.Route.receiver oldHosts pitch ((row K G M).symm ⟨i-base,hit⟩).1):Word w)
    else I.value i}

def phase (base oldHosts pitch w : ℕ) : NativePhase w :=
  let I:=image g base oldHosts pitch w
  ⟨I.program,4+10*I.length,I.output,I.hardware.1⟩

def port (base oldHosts : ℕ) (visited sorted : Bank) (s : Fin P) : Expr :=
  let B:=layout g base visited
  let receiver:=Expr.lookup B.start .row
  let decoded:=(Sorted.expr visited sorted oldHosts s).atRow receiver
  let digit:=Expr.branch .eq receiver (.lit oldHosts) (.lit 0) decoded
  .lookup B.broadcast (.op .add (.lookup B.cut .row) digit)

def value {oldHosts : ℕ} (pitch : ℕ) (reach : Fin oldHosts→Fin P→Option (Fin oldHosts)) (s : Fin P) : Values g a :=
  fun h _=>(DepotRAM.Material.Route.receiver oldHosts pitch h).elim 0 (fun v=>(Sorted.rawAtOrdinal reach v s:Cell a))

theorem any {base oldHosts pitch w : ℕ} (m : Memory w) (room : finish g base<2^w) :
    Step base (finish g base) (phase g base oldHosts pitch w) m :=by
  let I:=image g base oldHosts pitch w
  have order : base≤finish g base:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have space : I.low+I.length<2^w:=by change base+(finish g base-base)<2^w;rwa [Nat.add_sub_of_le order]
  have run:=I.issue m space
  exact ⟨order,run.1,run.2.2⟩

structure Issued (base oldHosts pitch : ℕ) (vis : Bank) {w : ℕ} (m : Memory w) : Prop where
  host : ∀p : Row K G M,m ((layout g base vis).start.base+(row K G M p).val)=
    (number (DepotRAM.Material.Route.receiver oldHosts pitch p.1):Word w)
  cut : ∀p : Row K G M,m ((layout g base vis).cut.base+(row K G M p).val)=(((usedRow p).val*2^a:ℕ):Word w)
  repeatWord : ∀i : Fin (M+1),∀x : Cell a,m ((layout g base vis).broadcast.base+repeatAddr i x)=((repeated i x).val:Word w)

theorem issued {base oldHosts pitch w : ℕ} (vis : Bank) (m : Memory w) (space : finish g base<2^w) :
    Issued g base oldHosts pitch vis ((phase g base oldHosts pitch w).image m) :=by
  let I:=image g base oldHosts pitch w
  let J:=Public.literals base 1 K G M a w
  let pad:=Public.stride K G M
  have rows : K*chunks G M≤pad:=Nat.le_pow_clog (by decide) _
  have middle : base+2*pad≤finish g base:=Nat.le_add_right ..
  have order : base≤finish g base:=(Nat.le_add_right ..).trans middle
  have room : I.low+I.length<2^w:=by change base+(finish g base-base)<2^w;rwa [Nat.add_sub_of_le order]
  have installed:=(I.issue m room).2.1
  have standard:=Public.mounted base 1 K G M a vis J.value (fun _ _ _=>rfl)
  constructor
  · intro p
    let j:=row K G M p
    have live : j.val<K*chunks G M:=j.isLt
    have bound : base+j.val<finish g base:=by omega
    change I.output m (base+j.val)=(number (DepotRAM.Material.Route.receiver oldHosts pitch p.1):Word w)
    simpa [I,image,j,live] using installed (base+j.val) (Nat.le_add_right ..) bound
  · intro p
    let j:=row K G M p
    have live : j.val<K*chunks G M:=j.isLt
    have outside : ¬(base+pad+j.val-base<K*chunks G M):=by omega
    have read:=installed (base+pad+j.val) (by change base≤_;omega) (by change _<finish g base;omega)
    exact (show I.output m (base+pad+j.val)=J.value (base+pad+j.val) by simpa only [I,image,dite_eq_right outside] using read).trans (standard.cut p)
  · intro i x
    let j:=repeatAddr i x
    have token : (finProdFinEquiv (i,x)).val=j:=by simp [j,repeatAddr,Nat.mul_comm,Nat.add_comm]
    have small : j<Public.words a M:=token ▸ (finProdFinEquiv (i,x)).isLt
    have width : Public.words a M≤2^(Nat.clog 2 (Public.words a M)):=Nat.le_pow_clog (by decide) _
    have bound : base+2*pad+j<finish g base:=by change _<base+2*pad+_;omega
    have outside : ¬(base+2*pad+j-base<K*chunks G M):=by omega
    have read:=installed (base+2*pad+j) (by change base≤_;omega) bound
    exact (show I.output m (base+2*pad+j)=J.value (base+2*pad+j) by simpa only [I,image,dite_eq_right outside] using read).trans (standard.broadcast i x)

end Broadcast
end
end Hierarchy.DescentDatedOperandReadPipeline.SortedInput

end OAI
