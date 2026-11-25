import OAI.Hierarchy.DescentRegisteredResetRegions
import OAI.Hierarchy.DescentRegisteredPresenceTariff
import OAI.Hierarchy.DescentRegisteredResetPrimitiveRegions
import OAI.Hierarchy.DescentRegisteredResetSheets
import OAI.Hierarchy.DescentRegisteredMetadataTariff

namespace OAI
/-! Each of the fifteen contributions is taken from the program executed at the
actual register. A single shared expense remains after summing their prices. -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset NativePitch Chronology Chronology.RegisterTimeline Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (K : Parameters)

theorem all_regions (saving : ℕ) (i : Fin 15) : Region G board op K i saving :=by
  fin_cases i
  · exact archive G board op K saving
  · exact roots G board op K saving
  · exact actor G board op K saving
  · exact received G board op K saving
  · exact compact G board op K saving
  · exact contact G board op K saving
  · exact masks G board op K saving
  · exact numbered G board op K saving
  · exact sheets G board op K saving
  · exact funding G board op K saving
  · exact venue G board op K saving
  · exact mover G board op K saving
  · exact classes G board op K saving
  · exact birth G board op K saving
  · exact metadata G board op K saving

/-- Constants depend only on the fixed calendar design, before the public skew
and word-size cutoff. The same constants cover all attained input graphs. -/
theorem reset_date_price (saving : ℕ) :
    ∃lead exponent cutoff : ℕ,∀τ B,0 < τ → 0 < B → 2*τ+cutoff ≤ B →
      G.b ≤ 2^(capRate G K.t K.g) → ∀ᶠ h : ℕ in atTop,∀a : Sample G board op K τ B h,
      a.Geometry → a.ReachedAt →
      let J:=Nat.log 2 h/(2*B)
      a.code.tariff ≤ a.hostWork*(lead*scale J exponent)+a.groupWork*(lead*scale J exponent)+
        a.copies/(2^J)^saving :=
  join G board op K saving (all_regions G board op K (saving+1))

theorem original_reset_move_price (saving : ℕ) :
    ∃lead exponent cutoff : ℕ,∀τ B,0 < τ → 0 < B → 2*τ+cutoff ≤ B →
      G.b ≤ 2^(capRate G K.t K.g) → ∀ᶠ h : ℕ in atTop,∀a : Sample G board op K τ B h,
      a.Geometry → a.ReachedAt → ∀(seats profile : ℕ→ℕ) (header : ℕ),
      let J:=Nat.log 2 h/(2*B)
      let tb:=tail τ J
      let S:=stageNumbers G K.t J K.f K.g K.reset a.copies tb
      let k:=groupBits K.t J S.hostGain S.capGain (cutRate K.t K.f K.g)
      let move:=resetMove (G:=G) (S:=S) (a.menu seats profile header) k a.age a.w a.position a.cap a.space
      move.code.tariff ≤ S.hostSize a.age*h*(lead*scale J exponent)+
        S.hostSize a.age*(S.groupCount a.age*S.radix)*(lead*scale J exponent)+a.copies/(2^J)^saving :=by
  obtain ⟨lead,ex,cutoff,bill⟩:=reset_date_price G board op K saving
  exact ⟨lead,ex,cutoff,fun τ B t den room branch=>(bill τ B t den room branch).mono
    (fun _ issued a geometry reached _ _ _=>issued a geometry reached)⟩

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
