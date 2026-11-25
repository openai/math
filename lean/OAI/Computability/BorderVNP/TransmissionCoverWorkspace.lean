import OAI.Computability.BorderVNP.TransmissionEarlyWorkspace
import OAI.Computability.BorderVNP.DiagonalExternalSewScale

/-! # Demand and geometry scratch for the actual rounded initial product cover -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open Filter TeamScales Packing
open GeometryAdviceRate (packetWords)

/-- The unfiltered demand rows are placed at the true startup end. The subsequent
geometry packet and its outputs therefore stay addressable at the actual initial
cover depth and ceiling block width. The estimate uses the full count of occupied
processor slots, including at least all literal slots. -/
theorem eventually_cover_workspace (I : Type) [Fintype I] [Nonempty I]
    {α τ : ℝ} (ha : 0 < α) (ha' : α < 1/1000) (ht : 0 < τ) (hts : τ < α/100)
    {K : ℕ} (hK : 1 ≤ K) (fan : τ*Real.logb 2 K ≤ α) (factor : ℕ) (positive : 0 < factor) :
    ∀ᶠ n : ℕ in atTop, ∀ (r header copied w slots u k o b : ℕ) (D : Directory.Layout),
      0 < r → 0 < slots → r*literal α n ≤ slots → slots ≤ r*n →
      let N := teams α τ K n
      let V := CoverScale.sites I (CoverScale.initialDepth I r n)
      let arena : StartupArena := ⟨N,r,literal α n,link (τ/5) N n,header,copied⟩
      D.teams = N → D.processors = r → D.entries = K^epochs τ n*V → D.fields = 2 →
      D.block = blockWidth slots V → D.literal = literal α n →
      header ≤ r*arena.link → copied ≤ r*block (τ/5) n → logWidth r n ≤ w → 1 ≤ b → 1 ≤ w →
      packetWords k u o b*w ≤ r*width n (95/100:ℝ) →
      let fresh := arena.next+7*D.candidates
      let stop := GeometryAdvice.Allocation.stop fresh u k o b w
      arena.frame+112 ≤ arena.next ∧ arena.next+7*D.candidates = fresh ∧
      factor*(stop-arena.next) ≤ r*n ∧ stop < 2^w := by
  have cover := eventually_rpow_gap (by norm_num : (0:ℝ) < 9/10) (CoverScale.sites I 1)
  have stages := eventually_geometry_stop ha ha' ht.le hK fan 1 factor
  have blocks := Diagonal.ExternalSew.eventually_block_fields I ha ha' ht.le hts hK fan
  have arenas := StartupArena.eventually_fits (by linarith : 0<τ/5) (by linarith : τ/5≤α)
  filter_upwards [cover,stages,blocks,arenas,eventually_many_teams ha τ hK 3] with n cn ns nb na three
  intro r header copied w slots u k o b D hr hs enough short N V arena team procs entries fields width lit
    hdr packet wide hb hw data fresh stop
  have ci : (CoverScale.sites I 1 : ℝ) ≤ (r:ℝ)*(n:ℝ)^(9/10:ℝ) := by
    rw [Real.rpow_zero,mul_one] at cn
    exact cn.trans (le_mul_of_one_le_left (by positivity) (by exact_mod_cast hr))
  have cap := (CoverScale.initial_sites I ci).2
  obtain ⟨gpos,blockFits,_,_⟩ := nb r hr slots hs short
  have a := na r N header copied w hr three hdr packet wide
  have cost := ns r V arena.next u k o b w D team procs entries fields (width ▸ gpos)
    (lit ▸ (enough.trans (width ▸ blockFits))) (by simpa only [one_mul] using cap) hb hw data
  refine ⟨?_,rfl,cost.1,cost.2 positive a.2⟩
  dsimp only [StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]
  omega

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
