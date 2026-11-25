import OAI.Hierarchy.ProbeFixedMarketLayout
import OAI.Hierarchy.ProbeFixedFailureFit

namespace OAI
/-! # Native purchase readiness from the original CT run and the actual chronological prefix -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StripDirectory PurchaseFrozen
open scoped Fin.CommRing Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "d" => (2^v.W)
local notation "A" => v.privateArena P z width
local notation "fmt" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "W" => wordBits z d copies
local notation "V" => Whole.markets v.mesh v.finish (v.basePhase width) fmt

/-- Recursive readiness consumes only the prefix which already ran. In particular it
can prove the frozen component of the present event before executing that event. -/
theorem dated_market_ready (π : Equiv.Perm (Fin (2^z))) (raw mid : Boot.Tape z d)
    (receipt : Boot.Receipt V π raw mid) (a : Attempt) (prior tail : List Event)
    (split : events v.mesh=prior++Event.attempt a::tail) (ran : Calendar.mounted C prior mid)
    (initial : heapEnd z d copies≤P.joint.initial) (capacity : (A).endAddress v.mesh<2^W)
    (height : 2*k+v.sampler.degree≤z)
    (maximum : v.menu.maximum<2^W) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (directory : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial) :
    ((C).frozen a).ready ((guard C a).apply (run C prior mid)) := by
  have mem : Event.attempt a∈events v.mesh := by rw [split];simp
  have ordered : ((events v.mesh).map (position v.mesh)).Pairwise (·<·) := by
    rw [positions];exact List.pairwise_lt_range
  rw [split,List.map_append,List.map_cons] at ordered
  obtain ⟨_,_,cross⟩:=List.pairwise_append.mp ordered
  have earlier (e : Event) (he:e∈prior) : position v.mesh e<position v.mesh (.attempt a) :=
    cross _ (List.mem_map_of_mem he) _ (List.mem_cons_self ..)
  have frame:=v.market_frames P z width r banks src tab dst owners a prior
    (initial.trans (v.market_initial_floor P z width)) earlier
  obtain ⟨i,hi⟩:=Whole.market_at v.mesh v.finish (v.basePhase width) fmt mem
  let market:=(fmt a).atTime v.mesh v.finish (v.basePhase width) a
  have opened:=receipt.ready_after_prefix (v.market_layout P z width initial) C prior a i
    Nat.one_le_two_pow ran
  rw [hi] at opened
  exact opened frame.1 frame.2.1 (v.market_dimensions P z width a mem initial capacity height)
    (v.market_stock_end P z width a) (v.market_failure_fits P z width a mem capacity maximum threshold directory)
    ((v.market_regions P z width a).2.1.trans (v.market_regions P z width a).2.2.1)
    frame.2.2 (v.market_capacity P z width a mem capacity)

/-- The original permutation input is an actual tape. Its subdivision initializes the
geometry and all chronological sampler pages before reaching this dated purchase. -/
theorem dated_market_from_input (π : Equiv.Perm (Fin (2^z))) (rest : Boot.Tape z d)
    (a : Attempt) (prior tail : List Event) (split : events v.mesh=prior++Event.attempt a::tail)
    (initial : heapEnd z d copies≤P.joint.initial) (capacity : (A).endAddress v.mesh<2^W)
    (height : 2*k+v.sampler.degree≤z)
    (maximum : v.menu.maximum<2^W) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (directory : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial) :
    let raw:=Boot.permutationWords π rest
    let init:=Boot.booted V ((A).endAddress v.mesh) raw
    (subdivisionProgram z d).Exec (Boot.initial V ((A).endAddress v.mesh) raw) init (subdivisionConstant d*2^z) ∧
    (Calendar.mounted C prior init→((C).frozen a).ready ((guard C a).apply (run C prior init))) := by
  let raw:=Boot.permutationWords π rest
  obtain ⟨ran,receipt⟩:=Boot.start V (v.market_layout P z width initial) Nat.one_le_two_pow π raw
    (Boot.permutationWords_get π rest)
  exact ⟨ran,fun hp=>v.dated_market_ready P z width r banks src tab dst owners π _ _ receipt a prior tail
    split hp initial capacity height maximum threshold directory⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
