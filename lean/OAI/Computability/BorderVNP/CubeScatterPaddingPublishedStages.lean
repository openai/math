import OAI.Computability.BorderVNP.CubeScatterPaddingPublished
import OAI.Computability.BorderVNP.CubeScatterPaddingBanksOutside

/-! # Transporting the real boot, dynamic header, and powers images to the padding scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA RoutingISA.CubeHeaderInstall VPVNP.BurstRAM Tally
open TeamContraction.JointHeader TeamContraction.ProcessorSlots

variable {w n d blocks b h K s : ℕ}

/-- The actual boot state and the two native installation results give the published
frame at the verifier. Only primary words, three secondary header cells, and the
one selected divisor must survive the subsequent native stages. -/
theorem Published.of_native_fields {D : ℕ} {L : Pins.Layout} {F : Pins.ProcessorFields L}
    {broadcast : BroadcastFrame} {advice : AdviceLayout} {ref : ReferencePacket w D}
    {pub : Arg → Word w} {bits : List Bool} {registers : Bank w} {afterBoot : Memory w}
    (booted : BootHeaderState F broadcast advice ref pub bits registers afterBoot)
    (P : Pointers) (B : Bootstrap w) (team : ℕ) (axis : Fin (n+1))
    (pins : ref.extension = B.extension d n blocks b h s)
    (literal : ∀ j : Fin 81, ∀ v, P.operand n d b h K s (31+j.val) = some v → (B.old j).val = v)
    (publicTeam : readings pub 1 = team)
    (prior : ℕ → ℕ) (dynamic powers final : Memory w) (powerInput : ℕ → ℕ)
    (returnedHeader : readings dynamic = ((B.stat d n blocks b h s).decoder broadcast.dst).finalImage
      ((B.stat d n blocks b h s).image n (selectorWidth n K h) prior))
    (returnedAxis : readings dynamic ((B.stat d n blocks b h s).header+5) = axis.val)
    (returnedPowers : readings powers = CubePowers.image d P.powers (n+1) powerInput)
    (primaryKept : ∀ k, k=0 ∨ k ∈ fixedFields → final (readings pub 0+k) = afterBoot (readings pub 0+k))
    (headerKept : ∀ j ∈ [5,7,8], final ((B.stat d n blocks b h s).header+j) =
      dynamic ((B.stat d n blocks b h s).header+j))
    (powerKept : final (P.powers+axis.val) = powers (P.powers+axis.val)) :
    Published P B pub final team axis d blocks b h K s := by
  constructor
  · have boot := booted.core (0 : Fin 31)
    have same := primaryKept 0 (Or.inl rfl)
    change final (readings pub 0 + 0) = afterBoot (readings pub 0 + 0) at same
    change afterBoot (readings pub 0+0) = pub 1 at boot
    exact (congrArg Fin.val ((by simpa only [Nat.add_zero] using same.trans boot : final (readings pub 0) = pub 1))).trans publicTeam
  · intro j hj
    have retain := primaryKept (31+j.val) (Or.inr hj)
    exact (by simpa only [Nat.add_assoc,readings] using retain : final ((pub 0).val+31+j.val) = afterBoot ((pub 0).val+31+j.val)).trans
      ((booted.extension j).trans (congrFun pins j))
  · exact literal
  · exact (congrArg Fin.val (headerKept 5 (by simp))).trans returnedAxis
  · refine ⟨broadcast.dst,prior,?_⟩
    intro j hj
    exact (congrArg Fin.val (headerKept j (by simp_all))).trans (congrFun returnedHeader _)
  · exact ⟨powerInput,(congrArg Fin.val powerKept).trans (congrFun returnedPowers _)⟩

/-- A complete unchanged primary frame supplies the fixed fields as a special case. -/
theorem Published.of_native {D : ℕ} {L : Pins.Layout} {F : Pins.ProcessorFields L}
    {broadcast : BroadcastFrame} {advice : AdviceLayout} {ref : ReferencePacket w D}
    {pub : Arg → Word w} {bits : List Bool} {registers : Bank w} {afterBoot : Memory w}
    (booted : BootHeaderState F broadcast advice ref pub bits registers afterBoot)
    (P : Pointers) (B : Bootstrap w) (team : ℕ) (axis : Fin (n+1))
    (pins : ref.extension = B.extension d n blocks b h s)
    (literal : ∀ j : Fin 81, ∀ v, P.operand n d b h K s (31+j.val) = some v → (B.old j).val = v)
    (publicTeam : readings pub 1 = team)
    (prior : ℕ → ℕ) (dynamic powers final : Memory w) (powerInput : ℕ → ℕ)
    (returnedHeader : readings dynamic = ((B.stat d n blocks b h s).decoder broadcast.dst).finalImage
      ((B.stat d n blocks b h s).image n (selectorWidth n K h) prior))
    (returnedAxis : readings dynamic ((B.stat d n blocks b h s).header+5) = axis.val)
    (returnedPowers : readings powers = CubePowers.image d P.powers (n+1) powerInput)
    (primaryKept : ∀ k < 112, final (readings pub 0+k) = afterBoot (readings pub 0+k))
    (headerKept : ∀ j ∈ [5,7,8], final ((B.stat d n blocks b h s).header+j) =
      dynamic ((B.stat d n blocks b h s).header+j))
    (powerKept : final (P.powers+axis.val) = powers (P.powers+axis.val)) :
    Published P B pub final team axis d blocks b h K s :=
  of_native_fields booted P B team axis pins literal publicTeam prior dynamic powers final powerInput
    returnedHeader returnedAxis returnedPowers (fun k hk => primaryKept k (by
      rcases hk with rfl | h
      · decide
      · simp [fixedFields] at h
        omega)) headerKept powerKept

end Cube.Padding

end BorderVNP
end Computability
end OAI
