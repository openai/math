import OAI.Computability.BorderVNP.PackedTerminalSignedIndexRange
import OAI.Computability.BorderVNP.PackedSewnRecordMeasures
import OAI.Computability.BorderVNP.PackedTerminalShape

/-! # The signed packet's actual two schemas and all its native word fits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Cover Epoch DeckGrid Shortening.PublicCapacity PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open PackedHistoryCircuit.Normalized.EnrichedOuter Diagonal Diagonal.ExternalSew TeamScales Filter
open Cover.AddressCircuit CellPacketGeometry CellPacketGeometry.History CellPacketGeometry.LiveWords CellSparse.Packet
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)
local notation "axes" => Fintype.card (Cube D)

/-- Fixed terminal tag capacity, independent of the length, chart and every
profile of the chronology. It includes the two sewn interval row shapes. -/
noncomputable def signedTagCapacity : ℕ := max 9 (birthTagBound e (0,false))

/-- Both word widths on the selected native signed tape. Its chronological
records retain their short scalar fields; the binding and report tables use
the actual hardware word. The same native capacity fits both anchor sorts
and every level of the ordered packet. -/
theorem eventually_signed_directory_bounds {a x : ℕ} (scale : EpochScales S a x)
    (holesCap g E : ℕ) :
    ∃ A : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let depth := start-1
      let T := epochs scale.τ n
      let log := logWidth r n
      let w := 60*log
      let native := log^(E+2)
      let tiles := CoverScale.sites (Cube D) start
      let cells := CoverScale.sites (Cube D) (EnrichedOuter.depth S start T)
      let live := teams scale.α scale.τ (fan S) n*tiles
      let shape := boundaryShape S start T
      let cap := signedTagCapacity (e := e)
      ∀ {qe qa : ℕ} (order : Fin (GridHosts.tileCount axes depth) ≃ (Fin axes → Deck (depth+2)))
        (position : (Fin axes → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
        (channels : ((Fin axes → Deck (depth+2)) × Direction axes) ↪ Fin qe)
        (groups : Fin (GridHosts.tileCount axes depth) ↪ Fin qa) (copies holes : ℕ),
        holes ≤ holesCap*GridHosts.tileCount axes depth →
        ∀ (dir : Directory.Layout) (_sites : dir.sites=tiles) (count : dir.entries=(fan S)^T*dir.sites)
          (number : e.Entry → ℕ) (positive : 0<shape.sites),
          let G := epoch S start w (Format.bottom (Seed.rows n r order position channels groups copies) holes w) T
          let F := G.schema.append (Sewn.schema (2*shape.edges+6*live) w)
          let L := FinalTies.tieSchema (shape.edges+4*live) live native
          let boxes := scheduledBoxes dir count number positive
          let rep := FinalReports.Spare.reports (C:=cells) (g:=g) (digits:=native) (E:=Fin dir.entries)
          let priv := FinalReports.Spare.priv (C:=cells) (g:=g) (digits:=native) (E:=Fin dir.entries)
          let rows := routingRows shape cells dir.entries live
          sourceVolume F L boxes rep ≤ A*rows*log^(max 2 (E+2)) ∧
          (256*sourceVolume F L boxes rep+2*rows+1 < 2^native ∧
            keyWidth axes (EnrichedOuter.depth S start T+1) ≤ native ∧ Nat.clog 2 rows ≤ native ∧
            w ≤ native ∧ cells+1 < 2^w ∧ shape.sites ≤ 2^w) ∧
          (∀ z, F.width z ≤ native) ∧ (∀ z, L.width z ≤ native) ∧
          ∃ sh : ∀ z, (F.tags z).length ≤ cap, ∃ th : ∀ z, (L.tags z).length ≤ cap,
          let tpl := template F L boxes sh th priv rep
          let len := (roster shape.sites F L).length
          shape.sites < 2^native ∧ cells < 2^native ∧ len < 2^native ∧
          tpl.publicDepth ≤ native ∧ tpl.chunkDepth ≤ native ∧ tpl.recordDepth ≤ native ∧
          Nat.clog 2 (len+(cells+1)) ≤ native ∧ Nat.clog 2 ((shape.sites+1)+len) ≤ native := by
  obtain ⟨A,source⟩ := eventually_scheduled_sourceVolume S scale holesCap g 1 (E+2)
  refine ⟨A,?_⟩
  filter_upwards [source,eventually_signed_packet_room A (max 2 (E+2)) E,
    eventually_compiled_dimensions S scale,eventually_ge_atTop (2^(360*axes+60))] with n numerator capacity dim hn
  intro r hr start depth T log w native tiles cells live shape cap qe qa order position channels groups copies holes holesBound
    dir siteCount count number positive G F L boxes rep priv rows
  let seed := Seed.rows n r order position channels groups copies
  let base := Format.bottom seed holes w
  have dims := dim r hr
  have rowFit : rows≤r*n := by
    change routingRows shape cells dir.entries live ≤ r*n
    rw [count,siteCount]
    exact dims.2.2.1
  have num := numerator r hr order position channels groups copies holes holesBound cells live dir count number positive
    native (by change native≤1*native; omega)
  have volume : sourceVolume F L boxes rep ≤ A*rows*log^(max 2 (E+2)) := by
    rw [signedSource_width_irrel F boxes rep native w]
    exact num
  have range := capacity r hr rows (sourceVolume F L boxes rep) rowFit volume
  have low : 360*axes+60 ≤ log := by
    change 360*axes+60 ≤ logWidth r n
    rw [public_logWidth,← Nat.clog_pow 2 (360*axes+60) (by decide)]
    exact Nat.clog_mono_right 2 (hn.trans ((Nat.le_mul_of_pos_left n (by decide : 0<2)).trans (Nat.le_mul_of_pos_right _ hr)))
  have maxWidth : (360*axes+60)*log ≤ native :=
    (Nat.mul_le_mul_right log low).trans ((sq log).symm.le.trans (Nat.pow_le_pow_right (by omega) (by omega)))
  have large : w ≤ native := (Nat.mul_le_mul_right log (Nat.le_add_left 60 (360*axes))).trans maxWidth
  have keySize : keyWidth axes (EnrichedOuter.depth S start T+1) ≤ native := dims.2.2.2.1.trans maxWidth
  have logs : Nat.clog 2 rows ≤ native := by
    change Nat.clog 2 (routingRows shape cells dir.entries live) ≤ native
    rw [count,siteCount]
    exact dims.2.2.2.2.2.1.trans maxWidth
  have rowWords : rows+1 < 2^w := by
    have npos : 0 < n := (Nat.two_pow_pos _).trans_le hn
    have rn : r*n+1 ≤ 2*n*r := by nlinarith only [Nat.mul_pos npos hr]
    have boxed : 2*n*r ≤ 2^log := by
      change 2*n*r ≤ 2^logWidth r n
      rw [public_logWidth]
      exact Nat.le_pow_clog (by decide) _
    exact ((Nat.succ_le_succ rowFit).trans (rn.trans boxed)).trans_lt (Nat.pow_lt_pow_right (by decide) (by
      change log < 60*log
      omega))
  have cellsSmall : cells+1 < 2^w := (Nat.succ_le_succ (show cells ≤ rows by
    dsimp only [rows,routingRows,CellAddressCircuit.count]; omega)).trans_lt rowWords
  have sitesSmall : shape.sites ≤ 2^w := (show shape.sites ≤ rows by
    dsimp only [rows,routingRows,CellAddressCircuit.count]; omega).trans (by omega)
  have h9 : 9 ≤ cap := le_max_left ..
  have initial : base.Bounded cap native := Format.bounded_bottom seed holes w
    (fun v u hu => (Seed.row_fields n r order position channels groups copies v u hu).elim
      (fun h => h.le.trans ((by decide : 5≤9).trans h9)) (fun h => h.le.trans h9)) large
  have prior := (all_bounded S start w h9 (le_max_right ..) large base initial).1 T
  have full := prior.append (Sewn.schema_bounded (2*shape.edges+6*live) w h9 large)
  have fixar (z : FinalTies.Row (shape.edges+4*live) live) : (L.tags z).length ≤ cap := by
    change (List.ofFn Layer.kind).length ≤ cap
    simpa only [List.length_ofFn] using h9
  exact ⟨volume,⟨range,keySize,logs,large,cellsSmall,sitesSmall⟩,full.width,fun _ => le_rfl,full.fields,fixar,
    signedPacket_depths F L boxes full.fields fixar priv rep
      ((Nat.le_add_right (256*sourceVolume F L boxes rep) (2*rows)).trans_lt ((Nat.le_succ _).trans_lt range))⟩

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
