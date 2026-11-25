import OAI.Computability.BorderVNP.TransmissionChosenArena
import OAI.Computability.BorderVNP.TransmissionStartupRate
import OAI.Computability.BorderVNP.TeamProcessorLiteralScale

/-! # A uniform physical startup allocation for the selected stretch reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial VPVNP VPVNP.BurstRAM Filter
open TeamContraction.ProcessorSlots

variable {K : Type*} [Field K] {dim labels : ℕ} {ι : Type} [Fintype ι]
variable {G : PaidIdentity K dim labels} {aux : ι → K} {q : ℕ}
variable {pc reg routines m g : ℕ} {Q Γ : Type} [Fintype Q]

set_option maxRecDepth 3500 in
/-- For each charged chart family one length threshold works for every later chart,
selected program, actual exterior routing and team. The chosen packet fits on the
literal advice slots, and the complete startup arena leaves a full batch of n-word
processor regions free below the physical word ceiling. -/
theorem StretchSchedule.eventually_chosenArena (sched : StretchSchedule) (f : ℕ → ℕ)
    (poly : PolynomiallyBounded f) (A C : ℕ) {α ξ : ℝ} (hx : 0 < ξ) (hxa : ξ ≤ α)
    (P : TeamOpcode.Program pc reg 32 routines) (lib : Fin routines → TeamSite.Macro Q Γ m g) :
    ∀ᶠ n : ℕ in atTop, let r := stretch sched.ρ n
      let T := f (adviceScale sched.σ sched.ρ n)
      let teams := sched.teamsPred n
      let W := sched.word n
      let link := TeamScales.link ξ (teams+1) n
      let free := siteFree P lib α r W n
      ∀ {k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
        {R : CommonField G aux q k s ord} (chart : AdvisedBranch R) [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
        (reader : ChosenReader chart (teams+1) r (sched.multBits n) (sched.tally n) W (T+6)),
        reader.charge ≤ A*(T+1)^C →
        ∀ (L : Routing.WireLayout (teams+1) r link) (e : ℕ), 0 < L.header →
        SiteGeometry P lib α ξ r n teams W e → TeamScales.logWidth r n ≤ W →
        let arena := reader.startupArena (n := n) P lib free link L.header
        reader.packetBitCount ≤ r ∧ arena.next < r*n ∧ arena.next+r*n < 2^W := by
  filter_upwards [sched.eventually_nativePackets (G := G) (aux := aux) (q := q) f poly A C 1,
    StartupArena.eventually_fits hx hxa] with n packets space
  intro r T teams W link free k s ord R chart _ _ reader charge L e hdr geometry wide arena
  let loc : ReaderPlacement W := ⟨0,0,0,0,0,0,0,0,fun _ => 0⟩
  have cost := packets chart reader charge 0 0 0 0 0 loc.extension
  change 1*((reader.packetAt loc).bits.length+_+_+1+_) < r at cost
  rw [one_mul,reader.packetAt_length] at cost
  have copied : reader.packetBitCount ≤ r := by omega
  have three := L.three
  let edge : Routing.Block (teams+1) := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),Nat.zero_lt_one⟩
  have header : L.header ≤ r*link := by have := L.fits edge; omega
  have procs : 0 < r := Nat.pos_of_mul_pos_right (hdr.trans_le header)
  have peers : 0 < link := Nat.pos_of_mul_pos_left (hdr.trans_le header)
  have positive : 0 < TeamScales.block ξ n := by
    have row := geometry.localInput
    have used := Nat.mul_pos (by omega : 0 < teams) peers
    change 2*TeamScales.literal α n + teams*link ≤ 3*TeamScales.block ξ n at row
    omega
  have bounds := space r (teams+1) L.header reader.packetBitCount W procs three header
    (copied.trans (Nat.le_mul_of_pos_right r positive)) wide
  have size : arena.literal = TeamScales.literal α n := geometry.literalSize
  have eq : arena = (⟨teams+1,r,TeamScales.literal α n,link,L.header,reader.packetBitCount⟩ : StartupArena) := by
    change (⟨teams+1,r,arena.literal,link,L.header,reader.packetBitCount⟩ : StartupArena) = _
    rw [size]
  exact ⟨copied,eq.symm ▸ bounds⟩

end Diagonal

end BorderVNP
end Computability
end OAI
