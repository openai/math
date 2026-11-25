import OAI.Computability.BorderVNP.CubeISAOwnedRawStrictTail
import OAI.Computability.BorderVNP.CubeTeamDeclarationEntries

/-! # Physical source and destination geometry of an unvalidated strict row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.CellDispatch RoutingISA.OwnedStages RoutingISA.OwnedVertex
open Physical Physical.Owned Tally Scatter VPVNP.BurstRAM DiagonalResidueRAM

/-- All source and destination geometry needed by a returning strict side. These
bounds do not constrain the advertised cut counts or the actual crossing-stream values. -/
structure RawSideSpace {w n d : ℕ} (blocks b h K s : ℕ) (v : CheckAddresses)
    (single out : ℕ) (i : Fin (n+1)) (pair : Symbols d) (pub : Arg → Word w) (src : Set ℕ) : Prop where
  /-- Physical frame and mixed-radix packet bounds. -/
  packet : PacketRoom (v.layout d blocks b h) w n b h K s (pub 0).val
  /-- Ordered singleton-family allocation. -/
  singleton : SingleRoom w n d (blocks*(h*b)) (pub 0).val single
  /-- Input metadata survives writes to the row banks. -/
  frame : Protected (v.layout d blocks b h) n (pub 0).val src
  /-- The actual singleton key count and bank pointer are source words. -/
  fields : (pub 0).val+56 ∈ src ∧ (pub 0).val+88 ∈ src
  /-- Every selected packet rectangle misses all protected inputs. -/
  packetSource : ∀ p : Packet n d blocks, p.1.1 i = pair → ∀ x ∈ src,
    x < bankAt v.bank (bankWidth n b h K s) p ∨ bankAt v.bank (bankWidth n b h K s) p+bankWidth n b h K s ≤ x
  /-- Every singleton destination lies outside the protected source words. -/
  singleSource : ∀ u z : Label (n+1) d, ∀ j < blocks*(h*b),
    singleBase single (d^(n+1)) (blocks*(h*b)) (finFunctionFinEquiv u).val (finFunctionFinEquiv z).val+j ∉ src
  /-- All singleton destinations start after the packet bank. -/
  beforeSingle : v.bank+(d*d)^(n+1)*2*blocks*bankWidth n b h K s ≤ single
  /-- The vertex directory starts after the packet bank. -/
  beforeVertex : v.bank+(d*d)^(n+1)*2*blocks*bankWidth n b h K s ≤ out
  /-- The terminal directory cursor fits the machine word. -/
  directory : out+(2*blocks*(d.choose 2)^n)*(3*2^n) < 2^w
  /-- The vertex directory is separated from all protected source words. -/
  source : ∀ x ∈ src, x < out ∨ out+(2*blocks*(d.choose 2)^n)*(3*2^n) ≤ x
  /-- Scratch for the following row checker is physically allocated. -/
  checker : LocalRow.Space (v.layout d blocks b h) w n b h K s (readings pub 0) v.actual v.claimed

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
