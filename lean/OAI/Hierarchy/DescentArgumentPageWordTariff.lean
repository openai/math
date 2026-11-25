import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! # A fixed setup, a once-only lookup, and a bounded scan per operand page -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSIMDLookup

theorem page_scan_words (H G M unit h w ratio pages cap cost : ℕ)
    (fill : h≤M*unit) (bus : w≤ratio*h)
    (price : cost≤cap*((pages+1)*(1+H*chunks G M)+(pages+1)*2^(h/2))) :
    cost*w≤cap*ratio*(pages+1)*(h+H*h+H*G*unit)+cap*ratio*(pages+1)*2^(h/2)*h :=by
  have rows:=chunk_work H G M h unit fill
  calc
    _ ≤ (cap*((pages+1)*(1+H*chunks G M)+(pages+1)*2^(h/2)))*(ratio*h) :=Nat.mul_le_mul price bus
    _ = cap*ratio*(pages+1)*(h+(H*chunks G M)*h)+cap*ratio*(pages+1)*2^(h/2)*h :=by ring
    _ ≤ _ :=by
      rw [Nat.add_assoc h]
      gcongr

end Hierarchy.DescentDatedSeedStartup

end OAI
