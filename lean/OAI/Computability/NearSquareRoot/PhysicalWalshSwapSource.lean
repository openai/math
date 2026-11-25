import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSwapBits
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapOrdinal

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SwapWord

/-- Grouping the trailing spectator into the rectangular payload commutes
with reading back the physical source ordinal of the interchange. -/
theorem source_stride (H G B S n : ℕ) :
    SwapOrdinal.source H G (B*S) n = SwapOrdinal.source H G B (n/S)*S+n%S := by
  simp only [SwapOrdinal.source,SwapOrdinal.rank,show B*S = S*B by ring,
    ← Nat.div_div_eq_div_mul n S B,Nat.mod_mul]
  ring

/-- A rectangular interchange on the two high fields is exactly the packed
word operation, with the complete arbitrary suffix inside its low payload. -/
theorem rectangular (lo hi w : ℕ) (s : Shape) (n : ℕ) (apart : lo+w ≤ hi) :
    SwapOrdinal.source (2^w) (2^(hi-(lo+w))) (2^lo*s.suff) n = stride s (run lo hi w) n := by
  rw [source_stride]
  unfold stride
  apply congrArg (fun v => v*s.suff+n%s.suff)
  generalize n/s.suff = q
  simp only [SwapOrdinal.source,Nat.div_div_eq_div_mul, ← pow_add,
    show lo+w+(hi-(lo+w))=hi by omega]
  rfl

end PhysicalWalshNode.SwapWord

end NearSquareRoot
end Computability
end OAI
