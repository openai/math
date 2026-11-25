import OAI.Hierarchy.DescentTerminalCohortInvoice
import OAI.Hierarchy.DescentTerminalCohortScale
import OAI.Hierarchy.DescentNativeSocketScale

namespace OAI
/-! # A common terminal replay price on the same stage and selected dyadic sockets -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentExteriorReplay DescentTerminalCohortArena
open DescentStaticWordColumn ProtocolRAM Computability.VPVNP.BurstRAM Filter
open scoped Topology
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F)
variable (t f g reset τ B:ℕ)
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
local notation "S" => fun J M=>stageNumbers G t J f g reset M (tail τ J)
local notation "k" => fun J=>groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "ℓ" => fun J=>(t+1)*J
local notation "hidden" => fun J=>k J*ℓ J
local notation "chart" => fun J=>8+capRate G t g*ℓ J

/-- The stable roster contains one native record per actual frozen cohort.
Its printed controller, initialization and every ancestry load are all included. -/
theorem stage_cohort_tariff (baseSize:10≤B) (reserve:2*localSocketRate G t g≤τ) :
    ∀ᶠ h:ℕ in atTop, let J:=Nat.log 2 h/(2*B); ∀M E s w factor first:ℕ,
      let runCfg:=S J M
      let frozen:=hidden J
      let q_:=Nat.clog 2 (NativeBranch.localLimit G runCfg)
      let n:=E*2^frozen
      let H:=runCfg.hostSize runCfg.length
      ∀(hops:ℕ→Hop) (source:Bank) (room:stop first frozen (chart J) n H<2^w),
        2^h≤2*(M*runCfg.copies)→2^J≤ s→w≤factor*h→h≤32*(2^q_*s)→
        H*h*2^J≤M*(runCfg.copies*s)→
        (clocks n (schedule hops runCfg.length)+ticks first frozen (chart J) n H room source+
          7*names ((steps w n (schedule hops runCfg.length)).seq (DescentTerminalCohortArena.machine first frozen
            (chart J) n H room source)))*w*2^J≤63000*factor*((runCfg.copies*s)*(M+2^J*E)) := by
  filter_upwards [cohort_tables t κ (capRate G t g) B baseSize,
    eventually_late (25600*(t+1)) B (by omega),Filter.eventually_ge_atTop 10] with h tables late large
  intro J M E s w factor first runCfg frozen q_ n H hops source room input pop arch packed positions
  let live := tail τ J + k J
  have kk:k J≤κ*(J+1):=groupBits_linear ..
  have full:=tables (k J) kk
  have queries:=native_socket_scale G t J f g reset M τ
  have rate : 2≤localSocketRate G t g:=by unfold localSocketRate;omega
  have threshold:25600*(t+1)≤2^(J+1):=late.trans (by have:=Nat.lt_two_pow_self (n:=J+1);omega)
  have extra:=cohort_ancestors J t (localSocketRate G t g) τ q_ (k J) h s rate reserve queries.1 threshold packed
  have popSize:n*2^live=E*runCfg.copies:=by
    change (E*2^(k J*ℓ J))*2^(tail τ J+k J)=E*(2^(tail τ J)*(2^(k J))^(ℓ J+1))
    rw [Nat.mul_assoc,←pow_add,←pow_mul,←pow_add]
    congr 2; ring
  have stash:2^(h/2)*h*2^J≤M*(runCfg.copies*s):=calc
    _ ≤ (M*runCfg.copies)*2^J := Nat.mul_le_mul_right _ (table_fund large input)
    _ ≤ (M*runCfg.copies)*s := Nat.mul_le_mul_left _ pop
    _ = _ := by ring
  exact cohort_tariff hops first frozen (chart J) runCfg.length n H w room source M runCfg.copies s E live (2^J) h
    factor popSize extra full.1 full.2 positions stash arch
end
end Hierarchy.DescentSixParty

end OAI
