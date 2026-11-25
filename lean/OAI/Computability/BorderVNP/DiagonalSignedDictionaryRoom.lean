import OAI.Computability.BorderVNP.DiagonalFixedSignedSites
import OAI.Computability.BorderVNP.FiniteEvaluatorSignedLookupPointers
import OAI.Computability.BorderVNP.CubeISALocalRowGeometrySpace
import OAI.Computability.BorderVNP.CubeRouteDataLayouts

/-! # Fitting the actual fixed cube dictionary on the selected signed processor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Branch Crossing Cover TeamScales RoutingISA PackedHistoryCircuit.Normalized

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] (G : PaidIdentity F D m)
    (cube : FixedCube K) {S : SiteSchedule G} {a extra E d Q A B j : ℕ}
    {s : EpochScales S a extra} (b : JointSchedule s E d Q A B j)

/-- Every literal of the actual fixed cube table fits a selected RAM word,
uniformly over its later chart, selector, raw exterior and private claims. -/
theorem JointSchedule.eventually_signed_dictionary_values :
    ∀ᶠ n : ℕ in atTop, CubeConstants.valueBound (cube.cubeID G) < 2^(b.physical.word n) := by
  let bound := CubeConstants.valueBound (cube.cubeID G)
  filter_upwards [eventually_ge_atTop (max 1 bound)] with n large
  have hn : 1 ≤ n := (le_max_left ..).trans large
  let r := stretch b.ρ n
  have fitted := Nat.size_le.mp (CellMacro.Generator.size_le_logWidth n r (stretch_one ..))
  have grow : logWidth r n ≤ (logWidth r n)^(E+1) := Nat.le_self_pow (Nat.succ_ne_zero _) _
  rw [(b.sizes hn).2.2.1]
  exact ((le_max_right 1 bound).trans large).trans_lt
    (fitted.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) grow))

end Diagonal

namespace RoutingISA.SignedTaskArena

open DiagonalTallyPacketEmit
open private lookup_order from OAI.Computability.BorderVNP.FiniteEvaluatorSignedCubeAllocation
open private deck_room from OAI.Computability.BorderVNP.FiniteEvaluatorSignedLookupPointers
open private payload_room from OAI.Computability.BorderVNP.CubeISALocalRowGeometrySpace

/-- The concrete signed arena places the full constant dictionary between
the fixed frame and the paid physical word bound. -/
theorem Layout.signed_dictionary_addresses (t : Layout) {frame w : ℕ}
    (base : frame+112 ≤ t.cube.header.header) (room : t.after.packed ≤ 2^w) :
    frame+112 ≤ t.cube.stop ∧ CubeConstants.arenaEnd t.cube.stop t.id < 2^w := by
  obtain ⟨head,pack,ends,pub,_⟩ := lookup_order t
  have vertex : t.cube.vertexBase ≤ t.cube.publicBase :=
    (Nat.le_add_right ..).trans_eq t.cube.separated.2.2.1
  refine ⟨(((base.trans head).trans pack).trans ends).trans (vertex.trans pub),?_⟩
  simpa only [CubeConstants.arenaEnd,CubeConstants.ids,List.length_ofFn] using deck_room t room

/-- The two factors needed by the owned scanner already fit its physical
arena, including unused mixed-radix packet trials. -/
theorem Layout.signed_owned_scan_words (t : Layout) {frame w : ℕ} (fit : t.cube.ReplayRoom w frame) :
    t.cube.header.d^(t.cube.n+1) ≤ 2^w ∧
      Cube.Physical.Owned.packetTrials t.cube.n t.cube.header.d t.cube.header.blocks*(t.cube.h*t.cube.s) < 2^w := by
  have rows := t.cube.writer_order
  obtain ⟨_,_,_,_,pair,host,pairs,stop⟩ := rows
  have power : t.cube.alphabet ≤ t.cube.alphabet^2 := Nat.le_self_pow (by decide) _
  have lfit := fit.stopFit
  have first : t.cube.alphabet ≤ 2^w := by omega
  refine ⟨first,?_⟩
  obtain ⟨_,_,packets,pub,_⟩ := lookup_order t
  have vertex : t.cube.vertexBase ≤ t.cube.publicBase :=
    (Nat.le_add_right ..).trans_eq t.cube.separated.2.2.1
  have p := Nat.pow_le_pow_right (Nat.mul_pos fit.alphabet fit.alphabet) (Nat.le_succ t.cube.n)
  have count := Nat.mul_le_mul_right t.cube.header.blocks (Nat.mul_le_mul_right 2 p)
  have width := (payload_room t.cube.n t.cube.b t.cube.h t.cube.K t.cube.s).2
  have raw := Nat.mul_le_mul count width
  have paid : Cube.Physical.Owned.packetTrials t.cube.n t.cube.header.d t.cube.header.blocks*(t.cube.h*t.cube.s) ≤ t.cube.packetEnd :=
    raw.trans (Nat.le_add_left _ _)
  exact paid.trans_lt ((packets.trans (vertex.trans pub)).trans_lt fit.stopFit)

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
