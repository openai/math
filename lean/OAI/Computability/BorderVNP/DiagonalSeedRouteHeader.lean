import OAI.Computability.BorderVNP.PackedHistorySeedExecution
import OAI.Computability.BorderVNP.PackedHistoryBroadcastRAM
import OAI.Computability.BorderVNP.PackedHistoryGeometryRate
import OAI.Computability.BorderVNP.DiagonalRouteHeaderCapacity
import OAI.Computability.BorderVNP.DiagonalCubeDeclarationRoom

/-! # Route capacity of the real sparse seed profile and cube declaration

The seed compiler counts every guess bit on the actual repeated grid. A length-only
reserved profile puts those bits in their native tree order and fills unused positions
with zeros. The independent finite reference packet supplies the word-width and
team-subtotal bounds needed by the joint route header.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch Packing Shortening Diagonal EnrichedOuter TeamScales
open VPVNP VPVNP.VerifierNetwork TeamContraction TeamContraction.ProcessorSlots
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
variable {n r d T copies headerFactor Q : ℕ}

/-- The physical bit positions that are actually counted by the seed compiler. -/
abbrev SeedSlot (S : SiteSchedule e) (n r d T : ℕ) :=
  Slot (fan S) (Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n)) T

/-- All seed choices fit the actual sublinear sparse history bound, independent
of the private field data used by any later history. -/
theorem profile_card_lt (plan : SeedPlan S n r d T copies headerFactor Q) :
    (Fintype.card (SeedSlot S n r d T) : ℝ) < r*(n:ℝ)^(92/100:ℝ) := by
  let f : Frame Unit (Boundary.Pins S (d+1) (boundaryShape S (d+1)) (60*logWidth r n) 0) :=
    Frame.initial (fun _ => ())
  have small : f.size ≤ 2 := by simp [f]
  exact (Nat.cast_le (α := ℝ)).mpr (Nat.le_add_left _ _) |>.trans_lt (plan.within f small)

/-- A uniform reserved profile length depending only on the external length and processor count. -/
noncomputable def profileReserve (r n : ℕ) : ℕ := ⌊(r:ℝ)*(n:ℝ)^(92/100:ℝ)⌋₊

/-- The real child-then-root tree enumeration fits the uniform profile reservation. -/
theorem profile_order_fits (plan : SeedPlan S n r d T copies headerFactor Q) (widths : ℕ → ℕ)
    (order : ∀ j, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n) j ≃ Fin (widths j)) :
    broadcastWidth (fan S) widths T ≤ profileReserve r n := by
  have card : Fintype.card (SeedSlot S n r d T) = broadcastWidth (fan S) widths T :=
    (Fintype.card_congr (broadcastOrder (fan S) widths order T)).trans (Fintype.card_fin _)
  rw [← card]
  exact Nat.le_floor (plan.profile_card_lt.le)

/-- The physical seed flags, including private-input-dependent acceptance, are
preserved exactly by the zero-padded encoding used in the header. -/
theorem profile_valid (plan : SeedPlan S n r d T copies headerFactor Q) (widths : ℕ → ℕ)
    (order : ∀ j, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n) j ≃ Fin (widths j))
    (bits : SeedSlot S n r d T → Bool) (ok : (SeedSlot S n r d T → Bool) → Prop) (passed : ok bits) :
    let live := broadcastOrder (fan S) widths order T
    validProfile live (plan.profile_order_fits widths order) ok
      (paddedProfile (reserve := profileReserve r n) live bits) :=
  ((acceptedPadded (broadcastOrder (fan S) widths order T) (plan.profile_order_fits widths order) ok) ⟨bits,passed⟩).property

/-- Every complete real seed header, including all padded profile positions, the
binary cube declaration and the true team subtotal array, fits the link bound.
The enumeration and padding are the ones consumed by the native profile RAM. -/
theorem header_capacity (plan : SeedPlan S n r d T copies headerFactor Q) {α : ℝ} {a w pin teams dim tally cap rest : ℕ}
    (fits : BorderVNP.Cube.RouteRecords.HeaderFitsAt α a n) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (packet : ReferencePacket w pin) (room : packet.bits.length+rest+1+teams*(dim*tally) ≤ r) (capFit : cap < 2^w)
    (widths : ℕ → ℕ) (order : ∀ j, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n) j ≃ Fin (widths j))
    (bits : SeedSlot S n r d T → Bool) (raw : BorderVNP.Cube.Physical.Broadcast a (BorderVNP.Cube.alphabet α n) cap)
    (claims : Fin teams → Fin dim → ℕ) :
    let live := broadcastOrder (fan S) widths order T
    let profile := paddedProfile (reserve := profileReserve r n) live bits
    validProfile live (plan.profile_order_fits widths order) (fun _ => True) profile ∧
      ((BorderVNP.Cube.RouteRecords.emittedHeader profile raw tally claims 0).length : ℝ) ≤ r*(n:ℝ)^(24/25:ℝ) := by
  intro live profile
  have room' := BorderVNP.Cube.RouteRecords.header_room_of_packet packet room
  have bound : (profileReserve r n : ℝ) ≤ r*(n:ℝ)^(19/20:ℝ) := by
    apply (Nat.floor_le (by positivity : 0 ≤ (r:ℝ)*(n:ℝ)^(92/100:ℝ))).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n) (by norm_num)) (by positivity)
  exact ⟨plan.profile_valid widths order bits (fun _ => True) trivial,
    fits (extra := 0) hr (by simpa using bound) capFit room'.1 room'.2 profile raw claims⟩

/-- For a larger profile used by the selected geometry program, the serialized
input-reference words alone pay for every reserved Boolean profile position. -/
theorem header_capacity_of_geometry {α : ℝ} {a w pin teams dim tally cap rest reserve k o b W : ℕ}
    (fits : BorderVNP.Cube.RouteRecords.HeaderFitsAt α a n) (hr : 1 ≤ r)
    (packet : ReferencePacket w pin) (room : packet.bits.length+rest+1+teams*(dim*tally) ≤ r)
    (capFit : cap < 2^w) (word : 1 ≤ W)
    (geometry : GeometryAdviceRate.packetWords k reserve o b*W ≤ r*width n (95/100:ℝ))
    (profile : Fin reserve → Bool) (raw : BorderVNP.Cube.Physical.Broadcast a (BorderVNP.Cube.alphabet α n) cap)
    (claims : Fin teams → Fin dim → ℕ) :
    ((BorderVNP.Cube.RouteRecords.emittedHeader profile raw tally claims 0).length : ℝ) ≤ r*(n:ℝ)^(24/25:ℝ) := by
  have charged : reserve ≤ r*width n (95/100:ℝ) := by
    have includeBits : reserve ≤ GeometryAdviceRate.packetWords k reserve o b := by unfold GeometryAdviceRate.packetWords; omega
    exact (includeBits.trans (Nat.le_mul_of_pos_right _ word)).trans geometry
  have scale : ((r*width n (95/100:ℝ):ℕ):ℝ) ≤ (r:ℝ)*(n:ℝ)^(19/20:ℝ) := by
    rw [Nat.cast_mul,show (19/20:ℝ) = 95/100 by norm_num]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by positivity)
  have bound := ((Nat.cast_le (α := ℝ)).mpr charged).trans scale
  have room' := BorderVNP.Cube.RouteRecords.header_room_of_packet packet room
  exact fits (extra := 0) hr (by simpa using bound) capFit room'.1 room'.2 profile raw claims

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

namespace Diagonal

open Filter TeamScales Crossing Epoch TeamContraction.ProcessorSlots
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule PackedHistoryCircuit.Normalized.EnrichedOuter
open _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical

universe u
variable {D m : ℕ} [NeZero D] {F : Type u} [Field F] {e : PaidIdentity F D m} {S : SiteSchedule e}
variable {extra E dlog Q A B j : ℕ}

/-- The actual simultaneous epoch calibration, rounded packet count, and common
processor word admit every genuine seed profile and compact cube declaration,
with the reference packet and the transmitted team subtotals in their real widths. -/
theorem JointSchedule.eventually_seed_route_header {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) dlog Q A B j) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let symbols := Cube.alphabet s.α n
      ∀ W : ℝ, W ≤ (R*exterior ((s.τ:ℝ)/5) r n : ℕ) →
      let blocks := blocksFor W (cube.h*cube.b) (symbols^(cube.pred+1))
      ∀ {d T copies headerFactor batch pin dim tally rest : ℕ}
        (_plan : SeedPlan S n r d T copies headerFactor batch)
        (packet : ReferencePacket (b.physical.word n) pin),
        packet.bits.length+rest+1+R*(dim*tally) ≤ r →
        ∀ (widths : ℕ → ℕ)
          (order : ∀ k, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n) k ≃ Fin (widths k))
          (bits : SeedPlan.SeedSlot S n r d T → Bool)
          (select : Packet cube.pred symbols blocks → Selector cube.pred cube.copies cube.h)
          (claims : Fin R → Fin dim → ℕ),
          let nativeOrder := broadcastOrder (fan S) widths order T
          let profile := paddedProfile (reserve := SeedPlan.profileReserve r n) nativeOrder bits
          ((RouteRecords.emittedHeader profile (broadcast cube.b cube.width select) tally claims 0).length : ℝ) ≤
            r*(n:ℝ)^(24/25:ℝ) := by
  filter_upwards [s.eventually_routed_headers,b.eventually_declaration_room cube,eventually_ge_atTop 1] with n room cap hn
  intro r R symbols W wire blocks d T copies headerFactor batch pin dim tally rest plan packet packetRoom widths order bits select claims
  have words : declarationCap cube.pred symbols blocks cube.b cube.h cube.width+1 < 2^b.physical.word n := (cap W wire).2
  exact (plan.header_capacity room.1 hn (stretch_one ..) packet packetRoom (Nat.lt_of_succ_lt words) widths order bits
    (broadcast cube.b cube.width select) claims).2

end Diagonal

end BorderVNP
end Computability
end OAI
