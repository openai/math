import OAI.Hierarchy.DescentResetSourceSlotCode
import OAI.Hierarchy.DescentResetRosterFunctions

namespace OAI
/-! # Rank programs computed solely from the numerical reset calendar -/
namespace Hierarchy.DescentResetLocalRoster
open DescentResetCompactParent

noncomputable def publicBefore (degree k n height common cap code : ℕ) :=
  DescentResetParentCodec.before (H:=degree+2) (r:=k) (Y:=2^n) (L:=(2^k+1)*(degree+2)*2^k)
    (cap:=cap) (links:=max (2^n) (2^height)) (program:=code) common

def keyCount (degree k n height cap code : ℕ) :=
  DescentResetParentCodec.capCount (degree+2) k (2^n) ((2^k+1)*(degree+2)*2^k)
    cap (max (2^n) (2^height)) code

def fieldBits (nextCap : ℕ) := Nat.clog 2 (max 5 (nextCap+2))
def originalBits (degree k n height cap code gain : ℕ) :=
  Nat.clog 2 (max (max 5 (2^gain*cap+1)) (keyCount degree k n height cap code))

noncomputable def publicSourceSlot (degree k n height cap code slots : ℕ) (j : ℕ) :=
  sourceSlotCode (degree+2) k (2^n) ((2^k+1)*(degree+2)*2^k) cap
    (max (2^n) (2^height)) code (2*(2^k*(2*cap))) (2^height) j slots

noncomputable def programCount {n d : ℕ} (A : NonlinearExpanders.Graph n d) (height : ℕ):=
  DescentResetCableSlots.cableCap A height

theorem same_count {n n' d : ℕ} (A : NonlinearExpanders.Graph n d) (B : NonlinearExpanders.Graph n' d)
    (dim : n=n') (board : HEq A B) (height : ℕ) : programCount A height=programCount B height := by
  subst n';rw [eq_of_heq board]
end Hierarchy.DescentResetLocalRoster

end OAI
