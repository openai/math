import OAI.Computability.BorderVNP.DiagonalNativeTimedArenaSchedule
import OAI.Computability.BorderVNP.DiagonalNativeTimedArenaReject

/-! # Both modes and the complete malformed-exterior test for the selected reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP BurstRAM TeamScales TeamContraction TeamContraction.ProcessorSlots
open Branch Crossing MvPolynomial RoutingISA RoutingISA.Evaluator TeamSite Filter
open FieldProcessor (Scale freeWidth)
open scoped Classical BigOperators

variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {G : PaidIdentity F D m}
variable {S : PackedHistoryCircuit.Normalized.SiteSchedule G}
variable {a extra E d Q A B j : ℕ} {s : EpochScales S a extra}
variable {ι : Type} [Fintype ι] {aux : ι → F} {q : ℕ}

set_option maxRecDepth 4500 in
/-- On the true joint length sequence, the selected residue reader's packet and
the ordinary scalar bank fit on every team. Its sewn contraction therefore has
exactly the reference and positive evaluator terms, simultaneously for every chart,
placement of the remaining evaluator fields, private site descriptions and live pin. -/
theorem JointSchedule.eventually_chosen_packet_checks (b : JointSchedule s (E+1) d Q A B j)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k : ℕ)
    {Qstate Γ : Type} [Fintype Qstate] {μ g : ℕ} (eval : Code) (he : eval.withoutAccept = true)
    (lib : Fin 8 → Macro Qstate Γ μ g) (mark : Fin 8 → Γ) (distinct : ∀ i, (lib i).alphabet.blank ≠ mark i) :
    let P := (withStartup eval).program
    let physical := TimedProcessor.machine P lib mark
    let ξ := (s.τ:ℝ)/5
    ∀ᶠ t : ℕ in atTop, let n := t+1
      let r := stretch b.ρ n
      let H := b.physical
      let W := H.word n
      let R := H.teamsPred n
      let T := f (adviceScale b.σ b.ρ n)
      let e := Wires.sortExponent (block ξ n)
      ∃ geo : Scale physical ((withStartup eval).slots+1) 64 32 s.α ξ r n R W e,
      ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField G aux q l size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart (R+1) r (H.multBits n) (H.tally n) W (T+6)),
        reader.charge ≤ c*(T+1)^k → ∀ (L : Routing.WireLayout (R+1) r (H.link n)), 0 < L.header →
        let free := freeWidth physical s.α 32 64 r W n
        let arena := programArena physical R r W n free (link ξ (R+1) n) L.header reader.packetBitCount
        ∀ (valuation entry totals : Fin (R+1) → ℕ) (extension : Fin (R+1) → Fin 81 → Word W),
          let pack := fun u => reader.packetAt (ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (extension u))
          AllocatedPacketModes eval lib mark geo L.header reader.packetBitCount pack ∧
          AllocatedPacketReady eval lib mark geo L.header reader.packetBitCount pack ∧
          AllocatedPacketRejects eval lib mark geo L.header reader.packetBitCount pack := by
  intro P physical ξ
  have τpos : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have positive : 0 < ξ := by dsimp [ξ]; positivity
  have small : ξ ≤ 1 := by dsimp [ξ]; linarith [s.tau_small,s.alpha_small]
  have eta : 2*(s.α:ℝ) ≤ 1-ξ := by dsimp [ξ]; linarith [s.tau_small,s.alpha_small]
  filter_upwards [b.eventually_chosen_packet_modes (aux:=aux) (q:=q) f hf c k eval he lib mark distinct,
    (tendsto_add_atTop_nat 1).eventually (eventually_allocatedPacketReady eval lib mark positive small eta),
    (tendsto_add_atTop_nat 1).eventually (b.eventually_lengths 0),
    (tendsto_add_atTop_nat 1).eventually (b.eventually_physical_arena (G:=G) (aux:=aux) (q:=q) f hf c k P lib physical)]
    with t offered checks sizes room
  intro n r H W R T e
  have hn : 1 ≤ n := Nat.succ_pos t
  have linkEq : H.link n = link ξ (R+1) n := by
    dsimp only [H,R,ξ]
    rw [(b.sizes hn).1]
    rfl
  obtain ⟨geo,modes⟩ := offered
  refine ⟨geo,?_⟩
  intro l size ord common chart prime alg reader charge L hdr free arena valuation entry totals extension pack
  have identity := modes chart reader charge L hdr valuation entry totals extension
  have three := L.three
  let edge : Routing.Block (R+1) := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),Nat.zero_lt_one⟩
  have hcap : L.header ≤ r*H.link n := by have := L.fits edge; omega
  obtain ⟨copies,_,ceiling⟩ := room chart reader charge L.header hcap
  have allocated : arena.next+r*n < 2^W := by
    dsimp only [arena,programArena]
    rw [←linkEq]
    exact ceiling
  have ready := checks geo L.header reader.packetBitCount pack three sizes.teams.2 hdr
    (linkEq ▸ hcap) (fun u => (reader.packetAt_length _).le) copies
    ((Nat.le_add_right arena.next (r*n)).trans_lt allocated)
  exact ⟨identity,ready,ready.rejects eval lib mark geo L.header reader.packetBitCount pack he⟩

end Diagonal

end BorderVNP
end Computability
end OAI
