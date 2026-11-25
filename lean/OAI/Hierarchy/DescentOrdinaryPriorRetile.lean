import Mathlib.Util.AssertNoSorry
import OAI.Hierarchy.DescentPreviousOperandLayout
import OAI.Hierarchy.DescentOrdinaryRoleRetile
import OAI.Hierarchy.DescentOverlapTariff
import OAI.Hierarchy.DescentPackedColumnHardware
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! The seven previous operand fields share one native width conversion dictionary.
Each resulting page stores all old-node digits and uses the successor's ordinary page order. -/
namespace Hierarchy.DescentOrdinaryPriorRetile
open DescentSIMDLookup DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentSixParty.Chronology ProtocolRAM DescentPackedZip DescentColonies.SplitRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (l : Layout) (lanes base prior : ℕ)
def shape : Layout := {l with lanes}
def digits := (l.size+2)*l.nodes
def pages := (7*l.operands)*l.blocks
def number : Pages l.operands × Fin l.blocks ≃ Fin (pages l) := finProdFinEquiv
def output := Overlap.dest base l.hosts l.groups l.lanes lanes (digits l)
set_option quotPrecheck false
local notation "h" => l.hosts
local notation "g" => l.groups
local notation "a" => digits l
local notation "out" => output l lanes base
local notation "nrows" => (shape l lanes).rows
local notation "n" => pages l
def roof := out+n*nrows+2^(Nat.clog 2 (nrows+1))
def bank (x : Fin l.blocks) (p : Pages l.operands) := previousBank (shape l lanes) out x p

def roster : DescentOrdinaryRoleRetile.Layout := ⟨pages l,l.hosts,l.groups,l.lanes,lanes,digits l⟩
theorem translated : roof l lanes base=base+roof l lanes 0 := (roster l lanes).translated base
theorem base_le : base≤roof l lanes base := (roster l lanes).base_le base

def sources (i : Fin (pages l)) : Bank :=
  let pair:=(number l).symm i
  previousBank l prior pair.2 pair.1
def expr:= (roster l lanes).expr base (sources l prior)
def scans:= (roster l lanes).scans base (sources l prior)
def phase (w : ℕ):= (roster l lanes).phase base (sources l prior) w

variable {w : ℕ}

theorem any (m : Memory w)
    (old : ∀(x : Fin l.blocks) (pg : Pages l.operands), (previousBank l prior x pg).Fits w base)
    (room : roof l lanes base < 2^w) :
    (phase l lanes base prior w).Runs m ∧
    ∀i : ℕ, i < base ∨ roof l lanes base ≤ i → (phase l lanes base prior w).image m i=m i := by
  apply DescentOrdinaryRoleRetile.Layout.any (roster l lanes) base (sources l prior) m
  · intro i
    exact old ((number l).symm i).2 ((number l).symm i).1
  · exact room

theorem number_val (x : Fin l.blocks) (p : Pages l.operands) :
    ((number l) (p,x)).val=p.val*l.blocks+x.val:=by
  change x.val+l.blocks*p.val=p.val*l.blocks+x.val
  ac_rfl

private theorem roster_bank (x : Fin l.blocks) (p : Pages l.operands) :
    (roster l lanes).bank base ((number l) (p,x))=bank l lanes base x p :=by
  simp only [DescentOrdinaryRoleRetile.Layout.bank,bank,previousBank,number_val,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]
  rfl

theorem placed (room : roof l lanes base < 2^w) (x : Fin l.blocks) (p : Pages l.operands) :
    (bank l lanes base x p).Fits w (roof l lanes base) ∧ nrows≤(bank l lanes base x p).size:=by
  rw [←roster_bank]
  exact (roster l lanes).placed base room ((number l) (p,x))

theorem reads (m : Memory w)
    (old : ∀(b : Fin l.blocks) (pg : Pages l.operands), (previousBank l prior b pg).Fits w base)
    (room : roof l lanes base < 2^w) (x : Fin l.blocks) (p : Pages l.operands)
    (value : Fin l.hosts → Fin l.groups → Cell (digits l))
    (live : 0<l.lanes) (read : Reads (previousBank l prior x p) value l.lanes m) :
    Reads (bank l lanes base x p) value lanes ((phase l lanes base prior w).image m) :=by
  let i:=(number l) (p,x)
  have physical : sources l prior i=previousBank l prior x p:=by simp [sources,i]
  have cap : h*chunks g l.lanes≤(previousBank l prior x p).size:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  rw [←roster_bank]
  exact (roster l lanes).reads base (sources l prior) m (fun z=>old ((number l).symm z).2 ((number l).symm z).1) room i value live
    (by change h*chunks g l.lanes ≤ (sources l prior i).size;rw [physical];exact cap)
    (by change Reads (sources l prior i) value l.lanes m;rw [physical];exact read)

end
end Hierarchy.DescentOrdinaryPriorRetile

end OAI
