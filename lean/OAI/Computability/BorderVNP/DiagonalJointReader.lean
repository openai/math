import OAI.Computability.BorderVNP.DiagonalPhysicalSchedule
import OAI.Computability.BorderVNP.DiagonalJointWords
import OAI.Computability.BorderVNP.TransmissionChosenArenaRate

/-! # The field chart, native reader and startup arena for the chosen schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial VPVNP BurstRAM TeamScales TeamContraction.ProcessorSlots Filter
open scoped Classical

universe u v

variable {D m : ℕ} [NeZero D] {F : Type v} [Field F] {G : PaidIdentity F D m}
variable {S : PackedHistoryCircuit.Normalized.SiteSchedule G}
variable {a extra : ℕ} {s : EpochScales S a extra} {E d Q A B j : ℕ}

/-- A single advice polynomial for all later ground fields, at the actual
number of teams, candidate size, batch and occurrence width. It covers all
the public words. Every fixed polynomial in the ceiling fits the batch. -/
theorem JointSchedule.reader_inputs (b : JointSchedule s E d Q A B j)
    {ι : Type} [Fintype ι] (aux : ι → F) (q : ℕ) [CharP F q] :
    ∃ f : ℕ → ℕ, PolynomiallyBounded f ∧
    (∀ C k : ℕ, ∀ᶠ n : ℕ in atTop, C*(f (adviceScale b.σ b.ρ n)+1)^k < stretch b.ρ n) ∧
    ∀ᶠ n : ℕ in atTop,
      let T := f (adviceScale b.σ b.ρ n)
      b.physical.word n ≤ T ∧ b.physical.tally n ≤ T ∧
      ∀ k, k+1 = n → ∀ ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)),
      ∀ (K : Type u) [Field K] [CharP K q],
        BorderApprox (k+1) (stretch b.σ n) (map (Int.castRingHom K) (Pstar (k+1))) →
        ∃ (R : CommonField G aux q k (stretch b.σ n) ord) (chart : AdvisedBranch R),
          ReaderInputs chart (b.physical.teamsPred n+1) (stretch b.ρ n) (b.physical.multBits n) T := by
  let amount n := b.physical.teamsPred n+1+b.physical.multBits n+b.physical.tally n+b.physical.word n
  obtain ⟨W,x,resource⟩ := b.physical.resources
  obtain ⟨f,hf,room,charts⟩ := eventually_reader_inputs.{u,v} q G aux b.sigma_pos b.sigma_rho amount resource
  refine ⟨f,hf,room,?_⟩
  filter_upwards [charts] with n hn
  obtain ⟨cap,supply⟩ := hn
  dsimp only [amount] at cap
  refine ⟨by omega,by omega,?_⟩
  intro k hk ord K fk char small
  exact supply k hk _ le_rfl _ (by dsimp only [amount]; omega) _ (by dsimp only [amount]; omega) ord K small

variable {ι : Type} [Fintype ι] {aux : ι → F} {q : ℕ}

set_option maxRecDepth 4000 in
/-- A length threshold precedes every actual finite-field chart and its
chosen reader. Its encoded star and program, scalar staging clock, subtotals,
and workspace fit on the same sequence as the rounded shortening and parse. -/
theorem JointSchedule.eventually_reader_room (b : JointSchedule s (E+1) d Q A B j)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k factor cut : ℕ)
    {pc μ g : ℕ} {Qstate Γ : Type} [Fintype Qstate]
    (P : TeamOpcode.Program pc 64 32 8) (lib : Fin 8 → TeamSite.Macro Qstate Γ μ g) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let T := f (adviceScale b.σ b.ρ n)
      let H := b.physical
      let W := H.word n
      let R := H.teamsPred n+1
      LengthBudget b cut n ∧
      ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField G aux q l size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart R r (H.multBits n) (H.tally n) W (T+6)),
        reader.charge ≤ c*(T+1)^k →
        (∀ base entry row col totals : ℕ, ∀ ext : Fin 81 → Word W,
          let packet := reader.nativePacket base entry row col totals ext
          factor*(packet.bits.length+jointBudget packet.bits.length W+reader.charge+1+
            R*((pairedTableParameters (l+1) size+Fintype.card (G.Entry ⊕ ι))*H.tally n)) < r) ∧
        ∀ (L : Routing.WireLayout R r (TeamScales.link ((s.τ:ℝ)/5) R n)) (depth : ℕ),
          0 < L.header → SiteGeometry P lib s.α ((s.τ:ℝ)/5) r n (H.teamsPred n) W depth →
          let arena := reader.startupArena (n := n) P lib (siteFree P lib s.α r W n)
            (TeamScales.link ((s.τ:ℝ)/5) R n) L.header
          reader.packetBitCount ≤ r ∧ arena.next < r*n ∧ arena.next+r*n < 2^W := by
  have α0 : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have τ0 : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have hx : 0 < (s.τ:ℝ)/5 := by positivity
  have hxa : (s.τ:ℝ)/5 ≤ (s.α:ℝ) := by linarith [s.tau_small]
  filter_upwards [b.eventually_lengths cut,b.eventually_word_capacity 1 1,
    b.physical.eventually_nativePackets (G := G) (aux := aux) (q := q) f hf c k factor,
    b.physical.eventually_chosenArena (G := G) (aux := aux) (q := q) f hf c k hx hxa P lib]
    with n hn word packet arena
  refine ⟨hn,?_⟩
  intro l size ord common chart prime alg reader charge
  refine ⟨packet chart reader charge,?_⟩
  intro L depth hdr geo
  exact arena chart reader charge L depth hdr geo word.1

set_option maxRecDepth 4000 in
/-- The selected reader's exact bit count and startup arena also fit for any
fixed physical program table, in particular the timed private interpreter.
Its literal length includes that table's actual encoded prefix. -/
theorem JointSchedule.eventually_physical_arena (b : JointSchedule s (E+1) d Q A B j)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k : ℕ)
    {pc μ g : ℕ} {Qstate Γ : Type} [Fintype Qstate]
    (P : TeamOpcode.Program pc 64 32 8) (lib : Fin 8 → TeamSite.Macro Qstate Γ μ g)
    (physical : UniversalMachine.Program) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let T := f (adviceScale b.σ b.ρ n)
      let W := b.physical.word n
      let R := b.physical.teamsPred n+1
      let link := b.physical.link n
      ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField G aux q l size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart R r (b.physical.multBits n) (b.physical.tally n) W (T+6)),
        reader.charge ≤ c*(T+1)^k → ∀ header ≤ r*link,
        let free := FieldProcessor.freeWidth physical s.α 32 64 r W n
        let arena : StartupArena := ⟨R,r,TeamContraction.entryLiteral physical (W+1) n
          (prefixCapacity r 32 64 W n+1+free),link,header,reader.packetBitCount⟩
        reader.packetBitCount ≤ r ∧ arena.next < r*n ∧ arena.next+r*n < 2^W := by
  have α0 : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have τ0 : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have hx : 0 < (s.τ:ℝ)/5 := by positivity
  have hxa : (s.τ:ℝ)/5 ≤ (s.α:ℝ) := by linarith [s.tau_small]
  filter_upwards [b.physical.eventually_nativePackets (G := G) (aux := aux) (q := q) f hf c k 1,
    (b.program.table P lib physical).stretched b.rho_omega.le,b.eventually_word_capacity 1 1,
    b.eventually_lengths 0,StartupArena.eventually_fits hx hxa,eventually_ge_atTop 1]
    with n pkt tables words sizes alloc hn
  intro r T W R link l size ord common chart prime alg reader charge header hheader free arena
  have geo := tables (b.physical.teamsPred n)
  have hfree : arena.literal = literal s.α n := geo.literalSize
  let loc : ReaderPlacement W := ⟨0,0,0,0,0,0,0,0,fun _ => 0⟩
  have hp := pkt chart reader charge 0 0 0 0 0 loc.extension
  change 1*((reader.packetAt loc).bits.length+_+_+1+_) < r at hp
  rw [one_mul,reader.packetAt_length] at hp
  have copied : reader.packetBitCount ≤ r := by omega
  have big := sizes.teams.1
  have pos : 1 ≤ block ((s.τ:ℝ)/5) n := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow (by exact_mod_cast hn : 1 ≤ (n:ℝ))
      (show 0 ≤ 1-(s.τ:ℝ)/5/3 by linarith [s.tau_small,s.alpha_small])
  have hlink : link = TeamScales.link ((s.τ:ℝ)/5) R n := by
    dsimp [link,R]
    rw [(b.sizes hn).1]
    rfl
  have hfit := alloc r R header reader.packetBitCount W (stretch_one ..) big
    (hlink ▸ hheader) (copied.trans (Nat.le_mul_of_pos_right _ pos)) words.1
  have eq : arena = (⟨R,r,literal s.α n,TeamScales.link ((s.τ:ℝ)/5) R n,
      header,reader.packetBitCount⟩ : StartupArena) := by
    change (⟨R,r,arena.literal,link,header,reader.packetBitCount⟩ : StartupArena) = _
    rw [hfree,hlink]
  exact ⟨copied,eq.symm ▸ hfit⟩

end Diagonal

end BorderVNP
end Computability
end OAI
