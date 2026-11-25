import OAI.Hierarchy.DescentNativeSocketScale
import OAI.Hierarchy.DescentTerminalHostInvoice

namespace OAI
/-! # Fixed terminal scan passes paid by the original terminal host reserve -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- Additional clocked column passes at each frozen host use the declared tail reserve. -/
theorem preflight_host_units (t J f g reset M τ h s charge : ℕ)
    (reserve : localSocketRate G t g+charge≤τ) :
    let S:=stageNumbers G t J f g reset M (tail τ J)
    let j:=Nat.clog 2 (NativeBranch.localLimit G S)
    h≤32*(2^j*s) →
    S.hostSize S.length*scale J charge*h*2^J≤M*(S.copies*s) := by
  intro S j packed
  let a:=localSocketRate G t g
  have small : 2^j≤ scale J a := (native_socket_scale G t J f g reset M τ).2.2.1
  have exp : scale J (a+charge)≤2^(tail τ J) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ reserve)
  have stack : 2^j*scale J charge≤2^(tail τ J) :=
    (Nat.mul_le_mul_right _ small).trans ((scale_mul J a charge).le.trans exp)
  have slab : 32≤2^(capRate G t g*((t+1)*J)+8+cutRate t f g) := by
    change 2^5≤2^_
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply terminal_host_price G t J f g reset M (tail τ J) h s (scale J charge)
  calc
    _ ≤ scale J charge*(32*(2^j*s)) := Nat.mul_le_mul_left _ packed
    _ = s*((2^j*scale J charge)*32) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul stack slab)

end Hierarchy.DescentSixParty

end OAI
