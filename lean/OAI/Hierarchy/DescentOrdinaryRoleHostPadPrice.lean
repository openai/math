import OAI.Hierarchy.DescentOrdinaryRoleHostPad
import OAI.Hierarchy.DescentOrdinaryHostPadPrice
import OAI.Hierarchy.DescentOrdinaryArgumentRetilePrice
import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! The original role repitch is charged on the actual predecessor rectangle. The host extension is
charged on the current rectangle using the paid packed lane occupancy. -/
namespace Hierarchy.DescentOrdinaryRoleHostPad.Layout
open DescentSIMDLookup DescentStaticWordColumn
noncomputable section
variable (L : Layout) (base : ℕ) (prior : Fin L.blocks→ProtocolRAM.Bank) (w h ratio u₀ u₁ : ℕ)
theorem word_bill (old : 0<L.beforeLanes) (new : 0<L.afterLanes) (live : 0<L.oldHosts)
    (inCap : L.beforeLanes≤h) (outCap : L.afterLanes≤h) (short : L.bits*L.beforeLanes≤h/2)
    (inFill : h≤L.beforeLanes*u₀) (outFill : h≤L.afterLanes*u₁) (bus : w≤ratio*h) :
    let p:=L.phase base prior w
    (p.ticks+7*names p.program)*w≤
      (4096*ratio*(L.blocks+1)*(h+3*L.oldHosts*h+L.oldHosts*L.groups*(2*u₀+u₁))+
        (4096*ratio)*(2*(h+1)^2*2^(h/2))*h)+
      512*ratio*(L.blocks+1)*(h+L.hosts*h+L.hosts*L.groups*u₁):=by
  have one:=L.retile.word_bill base prior w h ratio u₀ u₁ old new live inCap outCap short inFill outFill bus
  have two:=L.rect.fee (L.split base) (L.retile.bank base) w
  have dense:=DescentDatedSeedStartup.chunk_work L.hosts L.groups L.afterLanes h u₁ outFill
  let q:=L.rect.phase (L.split base) (L.retile.bank base) w
  let earlier:=L.retile.phase base prior w
  have local_ : (q.ticks+7*names q.program)*w≤512*ratio*(L.blocks+1)*(h+L.hosts*h+L.hosts*L.groups*u₁):=by
    calc _ ≤ (512*(L.blocks+1)*(L.rows+1))*(ratio*h):=Nat.mul_le_mul two bus
         _=512*ratio*(L.blocks+1)*(h+L.rows*h):=by ring
         _≤_:=Nat.mul_le_mul_left _ (by unfold rows; omega)
  change (earlier.ticks+q.ticks+7*names (earlier.program.seq q.program))*w≤_
  rw [names_seq]
  calc _=(earlier.ticks+7*names earlier.program)*w+(q.ticks+7*names q.program)*w:=by ring
       _≤_:=Nat.add_le_add one local_

end
end Hierarchy.DescentOrdinaryRoleHostPad.Layout

end OAI
