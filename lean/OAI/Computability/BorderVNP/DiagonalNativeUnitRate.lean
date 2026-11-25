import OAI.Computability.BorderVNP.DiagonalNativeUnitPacket
import OAI.Computability.BorderVNP.RoutingISATickBudget
import OAI.Computability.BorderVNP.PackedPotential

/-! # Tick budget for the real unit branch of the signed diagonal evaluator

All 81 extended frame words and the live-column test fit inside the processor
advice-bit count. The two exterior scans visit at most the exterior bit budget,
up to a fixed cost for each team. The resulting bound fits the rounded team clock
at every sufficiently large processor length, uniformly in the batch size.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open RoutingISA RoutingISA.Pins RoutingISA.Evaluator TeamScales Filter

/-- The physically placed reference packet includes every bit of every frame word,
and all the bits of the distinguished index. -/
theorem ReferencePacket.dimensions_le {w d count : ℕ} (p : ReferencePacket w d)
    (room : p.bits.length ≤ count) : w ≤ count ∧ d ≤ count := by
  rw [ReferencePacket.bits_length,ReferencePacket.offset,Nat.mul_add] at room
  omega

/-- Uniform numerical bound for the complete native unit path. The bit allowance of
the physical packet controls the word width and the entire pin comparison. -/
theorem packetUnitBudget_le {w d base : ℕ} (p : ReferencePacket w d) (A : AdviceLayout)
    (f : BroadcastFrame) (L : Layout) (ξ : ℝ) (n : ℕ)
    (fit : f.Fits w base) (hlink : f.link = link ξ f.teams n)
    (room : p.bits.length ≤ A.count) (count : A.count ≤ f.processors) (width : L.width = d) :
    packetUnitBudget A.count w f L ≤ 2048*(exterior ξ f.processors n + f.teams + f.processors + 1) := by
  obtain ⟨hw,hd⟩ := p.dimensions_le room
  have b := f.readTicks_le_exterior fit ξ n hlink
  have u := f.linkCheckTicks_le_exterior ξ n (headerSetup.slots+1) 1 hlink
  change f.linkCheckTicks (headerSetup.slots+1) 1 ≤ 97*(exterior ξ f.processors n + f.teams + 1) at u
  unfold packetUnitBudget jointBudget unitBudget
  rw [width]
  change 126+(41+A.count*10+1)+(19+8*81*(w+1)+8) +
    (f.readTicks+(2+(f.linkCheckTicks (headerSetup.slots+1) 1 + (44+2+d*13)))) ≤ _
  omega

/-- At the manuscript scales the measured unit path fits Lemma 7.1's tick cap.
The threshold is independent of the processor count, chosen packet, column, register
width, public scratch locations, and field characteristic. -/
theorem eventually_packetUnitBudget_le_ticks {ξ η : ℝ} (hξ : 0 < ξ) (hξ' : ξ ≤ 1)
    (hη : η ≤ 1-ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ (w d base : ℕ) (p : ReferencePacket w d) (A : AdviceLayout)
      (f : BroadcastFrame) (L : Layout), f.Fits w base → f.link = link ξ f.teams n →
      (f.teams:ℝ) ≤ (n:ℝ)^η → p.bits.length ≤ A.count → A.count ≤ f.processors → L.width = d →
      packetUnitBudget A.count w f L ≤ ticks ξ f.processors n := by
  have gap := Packing.eventually_le_rounded_width (show 1-ξ < 1-ξ/2 by linarith)
    (show 0 < 1-ξ/2 by linarith) (by norm_num : (0:ℝ) < 1) 8192
  filter_upwards [gap,eventually_ge_atTop 1] with n gapN hn
  intro w d base p A f L fit hlink teams room count hd
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have rpos : 1 ≤ f.processors := fit.procs
  have bits : 1 ≤ width n (1-ξ) := Nat.le_floor (by simpa only [Nat.cast_one] using Real.one_le_rpow hn' (sub_nonneg.mpr hξ'))
  have teams' : f.teams ≤ width n (1-ξ) :=
    Nat.le_floor (teams.trans (Real.rpow_le_rpow_of_exponent_le hn' hη))
  have hX : width n (1-ξ) ≤ exterior ξ f.processors n :=
    Nat.le_mul_of_pos_left _ rpos
  have hr : f.processors ≤ exterior ξ f.processors n := Nat.le_mul_of_pos_right _ bits
  have roomX := (packetUnitBudget_le p A f L ξ n fit hlink room count hd).trans
    (show 2048*(exterior ξ f.processors n+f.teams+f.processors+1) ≤ 8192*exterior ξ f.processors n by omega)
  have rounded : 8192 * width n (1-ξ) ≤ width n (1-ξ/2) := by
    have floor := Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hn') (1-ξ))
    change (width n (1-ξ):ℝ) ≤ _ at floor
    rw [one_mul] at gapN
    exact_mod_cast (mul_le_mul_of_nonneg_left floor (by norm_num : (0:ℝ) ≤ 8192)).trans gapN
  apply roomX.trans
  unfold exterior ticks
  rw [Nat.mul_left_comm]
  apply Nat.le_floor
  rw [Nat.cast_mul]
  gcongr
  exact (Nat.cast_le.mpr rounded).trans (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hn') _))

open VPVNP BurstRAM
open scoped Classical

variable {pc reg k routines m g : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)

/-- At the rounded team clock of Lemma 7.1, the actual unit-tagged computation on the
distributed packet gives the local unit column. The threshold comes before all physical
inputs, teams, layouts and packet choices. -/
theorem eventually_jointPacket_unit_value {ξ η : ℝ} (hξ : 0 < ξ) (hξ' : ξ ≤ 1) (hη : η ≤ 1-ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ (R r w a d e : ℕ) (S : SiteData R r reg k w a)
      (pack : Fin (R+1) → ReferencePacket w d) (fit : Fits P lib r w a R (link ξ (R+1) n) n e)
      (u : Fin (R+1)) (pin : Fin d → Bool) (ext : Exterior R r (link ξ (R+1) n) → Bool)
      (header dst ibase hbase starbase : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
      (s : Bank w) (A : AdviceLayout) (eval : Code), eval.withoutAccept = true →
      ∀ burst clock : ℕ, let G := wiring P lib (S.withPacket pack) d (link ξ (R+1) n) n e fit
        let L := G.pinLayout u ibase hbase starbase
        let F := G.processorFields u pin ext ibase hbase starbase
        let f := G.transferFrame u header dst
        let p := pack u
        (R+1:ℕ) ≤ width n η →
        PacketFrame L f A p.entry.length w (fun _ => 0) (operand pub) →
        f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
        ExtendedFrame.Fits w (pub 0).val A.dst p.entry.length →
        A.offset = adviceOffset P lib r w n → p.bits.length ≤ A.count → starbase = A.dst+p.offset →
        readings (processorMemory F w) (f.addr f.partner 0) = 0 →
        L.stride < 2^w → L.count < 2^w → L.width ≤ L.count →
        (starbase+d ≤ dst ∨ dst+header ≤ starbase) → (u = 0 → IdentityFits L w) →
        nativeValue (processorMachine (withStartup eval) pub mac s F) (ticks ξ r n) burst clock =
          if LocalUnit u pin p.reference ext then 1 else 0 := by
  filter_upwards [eventually_packetUnitBudget_le_ticks hξ hξ' hη] with n budget
  intro R r w a d e S pack fit u pin ext header dst ibase hbase starbase pub mac s A eval hc
    burst clock G L F f p teamBound scalar physical advice extended off packet star zero stride cap room apart pins
  have team : (f.teams:ℝ) ≤ (n:ℝ)^η :=
    (Nat.cast_le.mpr teamBound).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have time := budget w d (pub 0).val p A f L physical rfl team packet advice.count rfl
  exact jointPacket_unit_value P lib S pack _ n e fit u pin ext header dst ibase hbase starbase
    pub mac s A eval hc _ burst clock scalar physical advice extended off packet star zero stride cap
    room apart pins time

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
