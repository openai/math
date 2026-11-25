import OAI.Hierarchy.DescentNamedSeedPosition
import OAI.Hierarchy.DescentNamedSeedHeadData
import OAI.Hierarchy.DescentNamedShellAddress
import OAI.Hierarchy.DescentMaximumDegreeQuota
import OAI.Hierarchy.DescentPrivateDonorBillNumbers

namespace OAI
/-! # Parameters of the original seed and its first registered date -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentDatedSeedStartup
open Chronology Catalyst DescentSeedRoot
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)
variable (t f g drift : ℕ) (S : AtomSchedule) (k tail h : ℕ) (x : ShellSource F h)
variable {A : Type} (steps : List (DescentTerminalEpochChart.Source A)) (bins raw : ℕ)
local notation "p" => headGrain G S k h
local notation "s" => S.firstWidth G.b p
local notation "V" => originalSeedHead G op drift x.X steps S k tail h x.sites
  (maximumDegree (t+1)) (S.epochPower^S.priceExponent) s bins raw
local notation "l" => (V).layout G t f g drift h

/-- The initial room and the five physical register parameters on the dyadic
host count used in the public source.  The operand width uses the fixed
calendar degree. The actual initial roster has three sockets. -/
theorem original_initial_parameters (dyadic : ∃a,x.sites=2^a) :
    Fintype.card (Vertex x.X) ≤ (V).hosts ∧ x.sites=(V).hosts ∧
    (V).hosts=DescentDyadicSpan.span x.sites ∧ (V).hosts=hostRows x.sites ∧
    ((V).position G op t f g drift h).ports.venue.degree=3 ∧
    (V).degree=maximumDegree (t+1) ∧ (l).wire=S.epochPower^S.priceExponent ∧
    (l).history=s ∧ (l).seedWidth=s ∧
    (l).operandBits=DescentOperandWidth.recordBits G S k tail drift (maximumDegree (t+1)) p := by
  have card:=(DescentInitialHost.«initialize» x.X).2.1
  change Fintype.card (Vertex x.X)+Fintype.card (Cable x.X)+_≤10*(x.X.size+1) at card
  have vertices : Fintype.card (Vertex x.X)≤x.sites :=by have opened:=x.opened;omega
  obtain ⟨a,shape⟩:=dyadic
  have exactHeight : x.sites=DescentDyadicSpan.span x.sites :=by
    rw [shape]
    unfold DescentDyadicSpan.span
    rw [Nat.clog_pow 2 a (by decide)]
  exact ⟨vertices,rfl,exactHeight,exactHeight,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
