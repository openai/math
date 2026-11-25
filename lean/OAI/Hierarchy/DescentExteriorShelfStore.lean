import OAI.Hierarchy.DescentPublicExteriorRelocation

namespace OAI
/-! # Addressing the seventeen original exterior shelf banks -/
namespace Hierarchy.DescentExteriorShelf
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (j r t e origin : ℕ)
local notation "B" => bank j r t e origin
local notation "H" => span j r t e

/-- A literal memory shelf, with an arbitrary starting address suitable
for appending it to the previously installed controller header. -/
def store {w : ℕ} (m : Memory w) (content : Fin 17→Fin H→Word w) : Memory w := fun a=>
  if used : origin≤a ∧ a<origin+17*H then
    let delta:=a-origin
    have positive : 0<H := Nat.two_pow_pos _
    have bound : delta<17*H := by dsimp [delta]; omega
    content ⟨delta / H,(Nat.div_lt_iff_lt_mul positive).mpr bound⟩
      ⟨delta % H,Nat.mod_lt delta positive⟩
  else m a

theorem store_read {w : ℕ} (m : Memory w) (content : Fin 17→Fin H→Word w) (i : Fin 17) (u : Fin H) :
    store j r t e origin m content ((B i.val).base+u.val)=content i u := by
  have hi:=i.isLt
  have hu:=u.isLt
  have step : (i.val+1)*H≤17*H := Nat.mul_le_mul_right H i.isLt
  rw [Nat.add_mul,one_mul] at step
  have range : origin≤(B i.val).base+u.val ∧ (B i.val).base+u.val<origin+17*H := by
    change origin≤origin+i.val*H+u.val ∧ origin+i.val*H+u.val<origin+17*H
    omega
  simp only [store,dite_eq_left range]
  have delta : (B i.val).base+u.val-origin=i.val*H+u.val := by change origin+i.val*H+u.val-origin=_;omega
  have positive : 0<H := Nat.two_pow_pos _
  congr 1
  · apply Fin.ext
    change ((B i.val).base+u.val-origin) / H=i.val
    rw [delta,Nat.mul_comm i.val H,Nat.mul_add_div positive,Nat.div_eq_of_lt hu,Nat.add_zero]
  · apply Fin.ext
    change ((B i.val).base+u.val-origin) % H=u.val
    rw [delta,Nat.mul_add_mod_of_lt hu]

end
end Hierarchy.DescentExteriorShelf

end OAI
