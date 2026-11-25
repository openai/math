import OAI.Computability.BorderVNP.DiagonalSeedRouteHeader
import OAI.Computability.BorderVNP.DiagonalPositiveHeaderSyntax
import OAI.Computability.BorderVNP.TransmissionChosenPacket
import OAI.Computability.BorderVNP.CubeCommonVolume

/-! # A single physically parsed broadcast width before choosing a terminal history

The public volume, block count and declaration bound depend only on the
calibrated length. The reference packet controls the number of true tally
coordinates for each chart. All evaluation branches use the same positive
header format and the unit branch has the same physical width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader.PositiveFields

open _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical _root_.OAI.Computability.BorderVNP.Cube.RouteRecords TeamContraction.ProcessorSlots

/-- The encoded branch and the raw native parse use exactly the same full
header width. The three parsed fields exhaust the transmitted positions after the branch bit. -/
theorem emitted_length {a d cap teams dim reserve : ℕ} (profile : Fin reserve → Bool)
    (raw : Broadcast a d cap) (tally : ℕ) (claims : Fin teams → Fin dim → ℕ) :
    (emittedHeader profile raw tally claims 0).length = width reserve a d cap teams dim tally := by
  rw [emittedHeader_length,width]
  omega

/-- At an admitted length, the public width of the raw input header is bounded
before any encoded word, branch selector or subtotal has been chosen. -/
theorem width_le_of_packet {α : ℝ} {a n r teams dim tally w pin cap reserve rest : ℕ}
    (fit : HeaderFitsAt α a n) (hr : 1 ≤ r) (profile : (reserve:ℝ) ≤ r*(n:ℝ)^(19/20:ℝ))
    (p : ReferencePacket w pin) (room : p.bits.length+rest+1+teams*(dim*tally) ≤ r) (capFit : cap < 2^w) :
    (width reserve a (alphabet α n) cap teams dim tally : ℝ) ≤ r*(n:ℝ)^(24/25:ℝ) := by
  have bound := header_room_of_packet p room
  let raw : Broadcast a (alphabet α n) cap := ⟨fun _ => false,fun _ _ _ => false⟩
  let bits : Fin reserve → Bool := fun _ => false
  let claim : Fin teams → Fin dim → ℕ := fun _ _ => 0
  rw [← emitted_length bits raw tally claim]
  exact fit (extra := 0) hr (by simpa using profile) capFit bound.1 bound.2 bits raw claim

end TeamContraction.JointHeader.PositiveFields

namespace Diagonal

open Filter TeamScales Crossing Branch VPVNP VPVNP.BurstRAM
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamContraction.JointHeader TeamContraction.ProcessorSlots _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical

open scoped Classical

universe u
variable {D m : ℕ} [NeZero D] {F : Type u} [Field F] {e : PaidIdentity F D m} {S : SiteSchedule e}
variable {extra E dlog Q A B j : ℕ} {ι : Type} [Fintype ι] {aux : ι → F} {q : ℕ}

set_option maxRecDepth 4000 in
/-- Choose the same calibrated packet reservation for all physical terminal
histories and then bound the full positive header of every actual field
reader. The threshold is chosen before the ground field, curve and payload. -/
theorem JointSchedule.eventually_common_route_header {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) dlog Q A B j)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let T := f (adviceScale b.σ b.ρ n)
      let R := b.physical.teamsPred n+1
      let symbols := Cube.alphabet s.α n
      let X := R*exterior ((s.τ:ℝ)/5) r n
      let blocks := blocksFor X (cube.h*cube.b) (symbols^(cube.pred+1))
      let cap := declarationCap cube.pred symbols blocks cube.b cube.h cube.width
      let reserve := SeedPlan.profileReserve r n
      let tally := b.physical.tally n
      cap+1 < 2^b.physical.word n ∧
      ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))} {common : CommonField e aux q l size ord}
        (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart R r (b.physical.multBits n) tally (b.physical.word n) (T+6)),
        reader.charge ≤ c*(T+1)^k →
        let dim := pairedTableParameters (l+1) size+Fintype.card (e.Entry ⊕ ι)
        let len := PositiveFields.width reserve cube.pred symbols cap R dim tally
        0 < len ∧ (len:ℝ) ≤ r*(n:ℝ)^(24/25:ℝ) ∧
          ∀ bits : List Bool, bits.length = len → bits.head? = some true →
            ∃! p : PositiveFields reserve cube.pred symbols cap R dim tally, p.bits = bits := by
  filter_upwards [s.eventually_routed_headers,b.eventually_declaration_room cube,eventually_ge_atTop 1,
    b.physical.eventually_nativePackets (G := e) (aux := aux) (q := q) f hf c k 1] with n header decl hn native
  intro r T R symbols X blocks cap reserve tally
  have word : cap+1 < 2^b.physical.word n := (decl X le_rfl).2
  refine ⟨word,?_⟩
  intro l size ord common chart prime alg reader charge dim len
  let packet := reader.nativePacket 0 0 0 0 0 (fun _ => 0)
  have budget := native chart reader charge 0 0 0 0 0 (fun _ => 0)
  change 1*(packet.bits.length+jointBudget packet.bits.length (b.physical.word n)+reader.charge+1+R*(dim*tally)) < r at budget
  have enough : packet.bits.length+(jointBudget packet.bits.length (b.physical.word n)+reader.charge)+1+R*(dim*tally) ≤ r := by omega
  have profile : (reserve:ℝ) ≤ r*(n:ℝ)^(19/20:ℝ) := by
    exact (Nat.floor_le (by positivity : 0 ≤ (r:ℝ)*(n:ℝ)^(92/100:ℝ))).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hn : (1:ℝ) ≤ n) (by norm_num)) (by positivity))
  exact ⟨by dsimp only [len,PositiveFields.width]; omega,
    PositiveFields.width_le_of_packet header.1 (stretch_one ..) profile packet enough (Nat.lt_of_succ_lt word),
    fun bits size tag => PositiveFields.unique_parse bits size tag⟩

end Diagonal

end BorderVNP
end Computability
end OAI
