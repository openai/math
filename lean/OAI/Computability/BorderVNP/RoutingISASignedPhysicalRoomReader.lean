import OAI.Computability.BorderVNP.DiagonalJointReader
import OAI.Computability.BorderVNP.DiagonalPowerWords

/-! # The final reader and the unary source roster on the selected schedule

The selected board has one physical query bit per pin or subtotal digit and
one free input per finite-field guess. The packet bound also charges the
entire rectangular subtotal roster across all teams. This supplies a
length-only bound on all unary source slots even before choosing any path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueEntryInput ResidueRates ResiduePins DiagonalResidueRAM
open VPVNP VPVNP.BurstRAM TeamScales TeamContraction.ProcessorSlots Filter
open scoped Classical

variable {F : Type*} [Field F] {D m : ℕ} {G : PaidIdentity F D m}
    {ι : Type} [Fintype ι] {aux : ι → F} {q l size : ℕ}
    {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField G aux q l size ord} {chart : AdvisedBranch common}
    [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]

variable {R r W pin : ℕ}

local notation "par" => pairedTableParameters (l+1) size
local notation "labels" => Fintype.card (G.Entry ⊕ ι)
local notation "query" => Board.Physical par pin W (G.Entry ⊕ ι)
local notation "guesses" reader => Guess (Fin par) (ChosenReader.gridRank reader)
  (Nat.clog 2 common.p+1) (Nat.clog 2 common.p)


/-- The combined physical input, private guess, gate and machine word counts
are bounded by the charge of this particular chosen board circuit. -/
theorem ChosenReader.dimensions_le_charge (reader : ChosenReader chart R r W W W pin) :
    Fintype.card query + Fintype.card (guesses reader) + reader.gates + W ≤ reader.charge := by
  let x : ReaderSizes := ⟨par,adviceGateBudget (2*(l+1)) l size,labels,W,pin,W,
    Module.finrank (ZMod common.p) chart.E,reader.gridRank,W,common.p,common.p^reader.power,
    chart.pinRadius R r,(common.p^reader.power-1)*chart.degreeSum,reader.gridCard⟩
  have u : Fintype.card query = x.publicBits := by simp [Board.Physical,ReaderSizes.publicBits,x]
  have v : Fintype.card (guesses reader) = x.guessBits := by
    simp [ReaderSizes.guessBits,ResidueEntryBudget.guessWidth,x]
  rw [u,v]
  change x.publicBits+x.guessBits+reader.gates+x.word ≤ x.stagedCharge reader.gates
  have square := Nat.le_self_pow (by decide : 2 ≠ 0) (x.publicBits+x.guessBits+reader.gates+x.word+1)
  dsimp only [ReaderSizes.stagedCharge]
  omega

/-- Bounds for the source records, actual scalar RAM dimensions and circuit
literal, expressed in one scale used by the signed arena. -/
structure ChosenReader.PhysicalRoom (reader : ChosenReader chart (R+1) r W W W pin) (ceiling : ℕ) : Prop where
  parameters : par ≤ ceiling
  gadgets : labels ≤ ceiling
  word : W ≤ ceiling
  queryBits : Fintype.card query ≤ ceiling
  choiceBits : Fintype.card (guesses reader) ≤ ceiling
  gates : reader.gates ≤ ceiling
  pinBits : (par+2)*pin ≤ ceiling
  packet : reader.packetBitCount ≤ ceiling
  exponentWidth : Nat.clog 2 (r*(2*l+1)+1) ≤ W
  powerSlots : (R+1)*(par*Nat.clog 2 (r*(2*l+1)+1)) ≤ ceiling

/-- The finite type of weighted occurrences is the real batch, parameter
and binary-digit product counted in the source roster. -/
theorem ChosenReader.PhysicalRoom.power_card {reader : ChosenReader chart (R+1) r W W W pin} {C : ℕ}
    (room : reader.PhysicalRoom C) :
    Fintype.card (CellEntries.PowerSlot (Fin (R+1)) (Fin par) (Nat.clog 2 (r*(2*l+1)+1))) ≤ C := by
  simpa only [CellEntries.PowerSlot,Fintype.card_prod,Fintype.card_fin] using room.powerSlots

variable [NeZero D] {S : PackedHistoryCircuit.Normalized.SiteSchedule G}
    {a extra E d Q A B j : ℕ} {s : EpochScales S a extra}

/-- A single length threshold gives the final signed allocator its linear
ceiling, uniformly before the field chart, scalar circuit, word operands,
and assigned term are chosen. The startup packet and the whole unary roster
in fact each fit within the batch itself. -/
theorem JointSchedule.eventually_reader_physical_room (b : JointSchedule s (E+1) d Q A B j)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ l, n = l+1 →
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let W := b.physical.word n
      let T := f (adviceScale b.σ b.ρ n)
      ∀ {size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField G aux q l size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart R r W W W (T+6)),
        reader.charge ≤ c*(T+1)^k →
          reader.PhysicalRoom (r*n+1) ∧ reader.packetBitCount < r ∧
          R*(pairedTableParameters (l+1) size*Nat.clog 2 (r*(2*l+1)+1)) < r := by
  filter_upwards [b.physical.eventually_nativePackets (G:=G) (aux:=aux) (q:=q) f hf c k 1,
    b.eventually_word_capacity 1 1] with n packets words
  intro l eqn
  subst n
  intro r R W T size ord common chart prime alg reader bound
  let h := pairedTableParameters (l+1) size
  let u := Fintype.card (Board.Physical h (T+6) W (G.Entry ⊕ ι))
  let width := Nat.clog 2 (r*(2*l+1)+1)
  let loc : ReaderPlacement W := ⟨0,0,0,0,0,0,0,0,fun _ => 0⟩
  have paid := packets chart reader bound 0 0 0 0 0 loc.extension
  change 1*((reader.packetAt loc).bits.length+_+reader.charge+1+R*((h+labels)*W)) < r at paid
  rw [one_mul,reader.packetAt_length] at paid
  have costs := reader.dimensions_le_charge
  have hr := stretch_one b.ρ (l+1)
  have rn : r ≤ r*(l+1)+1 := (Nat.le_mul_of_pos_right r (Nat.succ_pos l)).trans (Nat.le_succ _)
  have wpos : 0 < W := by
    have cap : 1*(r*(l+1)+1)^1 < 2^W := words.2.2.1
    by_contra! bad
    rw [show W=0 by omega] at cap
    simp at cap
  have hw : width ≤ W := by
    apply LE.le.trans _ words.1
    rw [Shortening.PublicCapacity.public_logWidth]
    apply Nat.clog_mono_right
    change r*(2*l+1)+1 ≤ 2*(l+1)*r
    have pos : 1 ≤ r := hr
    nlinarith only [pos]
  have rect : R*(h*width) ≤ R*((h+labels)*W) :=
    Nat.mul_le_mul_left R (Nat.mul_le_mul (Nat.le_add_right ..) hw)
  have slots : R*(h*width) < r := by omega
  have us : u = 2*((h+2)*(T+6))+(h+labels)*W := by simp [u]
  have dims : h+labels ≤ u := (Nat.le_mul_of_pos_right _ wpos).trans (us ▸ Nat.le_add_left ..)
  change u + _ + reader.gates + W ≤ reader.charge at costs
  refine ⟨⟨?_,?_,?_,show u ≤ _ by omega,?_,?_,show (h+2)*(T+6) ≤ _ by omega,?_,hw,slots.le.trans rn⟩,?_,slots⟩
  all_goals omega

end Diagonal

end BorderVNP
end Computability
end OAI
