import OAI.Computability.BorderVNP.PackedSubdivisionIncoming
import OAI.Computability.BorderVNP.PackedSubdivisionPrivatePrograms
import OAI.Computability.BorderVNP.CoverLorentzSubdivisionRecords

/-! # Regional load of the actual private programs installed by subdivision

The geometric subdivision count reserves the prior program at every retained site
and one empty box at every relay. This bound also pays for the public equality rows
and the private work tapes used to implement these boxes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Cover Crossing Shortening InheritedBank CellAddresses
open scoped Classical

variable {D m n np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (routes : N.WireRoutes) (oldID : N.Edge ↪ Fin m)
    (newID : (N.subdivide routes).Edge ↪ Fin n) (portID : P ↪ Fin np)
local notation "G" => N.subdivide routes

set_option maxRecDepth 4096 in
/-- One serialized equality, its guard, and the two packet count prefixes. The
relay has neither private choices nor factor visits in its intrinsic program. -/
theorem relay_charges (j : (e : N.Edge) × Fin (routes.interior e)) :
    (relaySite N routes newID portID j).staticNodes = 1036 ∧
    (relaySite N routes newID portID j).expandedLoad = 0 := ⟨rfl,rfl⟩

private theorem input_rows (ex : Bool) (prior payload : N.Site → ℕ) (v : N.Site) :
    Fintype.card (Incident N v) + Fintype.card (Attached N v) ≤
      localRecords N ex prior payload (fun u => u = v) := by
  let equiv : Incident N v ≃ {c : N.Edge // True ∧ (N.src c = v ∨ N.dst c = v)} :=
    Equiv.subtypeEquivRight fun _ => ⟨fun h => ⟨trivial,h⟩,And.right⟩
  rw [Fintype.card_congr equiv]
  have h := tieRows_le N ex prior payload (fun _ => True) v
  unfold tieRows at h
  convert! h using 1
  congr! 2

/-- The raw physical subdivision charge at an old site equals that of the
original site, counting both endpoint records of a loop. -/
theorem raw_records_original (ex : Bool) (prior payload : N.Site → ℕ) (v : N.Site) :
    localRecords G ex (Sum.elim prior (fun _ => 0)) (Sum.elim payload (fun _ => 0)) (fun u => u = .inl v) =
      localRecords N ex prior payload (fun u => u = v) := by
  let test : (G).Site → Prop := Sum.elim (fun u => u = v) (fun _ => False)
  have eq : test = fun u => u = .inl v := by
    funext u
    apply propext
    rcases u with u | j
    · exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
    · exact ⟨False.elim,fun h => by cases h⟩
  rw [←eq]
  simpa [test] using subdivision_records_eq N routes ex prior payload test

/-- Uniform charge on any tile region of the actual installed endpoint and relay
programs. The constant covers the equality packet and guard and, in expanded
mode, the forced old incidence suffix. -/
theorem privatePrograms_load_le (old : Site.Programs N) (prior payload : N.Site → ℕ)
    (cap : ∀ v, (old v).program.staticNodes ≤ prior v ∧ (old v).program.expandedLoad ≤ payload v)
    (ex : Bool) (test : (G).Site → Prop) :
    let next := subdividePrivatePrograms N routes oldID newID portID old
    localRecords G ex (fun v => (next v).program.staticNodes) (fun v => (next v).program.expandedLoad) test ≤
      1040 * localRecords G ex (Sum.elim prior (fun _ => 0)) (Sum.elim payload (fun _ => 0)) test := by
  intro next
  let hist : (G).Site → ℕ := Sum.elim prior (fun _ => 0)
  let data : (G).Site → ℕ := Sum.elim payload (fun _ => 0)
  let pub := fun v => (next v).program.staticNodes
  let work := fun v => (next v).program.expandedLoad
  apply localRecords_of_singletons G ex hist data pub work
  intro v
  let M := localRecords G ex hist data (fun u => u = v)
  have hM : 1 ≤ M := one_le_siteRecords G ex hist data v
  have hx := exchange_site_records G ex hist data pub work v
  change _ + boxCost ex (hist v) (data v) = M + boxCost ex (pub v) (work v) at hx
  change _ ≤ 1040 * M
  rcases v with v | j
  · have hc := original_program_charges N routes v oldID newID portID (old v).program
    have hs : pub (.inl v) ≤ prior v + 1034 * (Fintype.card (Incident N v) + Fintype.card (Attached N v)) :=
      hc.1.trans (Nat.add_le_add_right (cap v).1 _)
    have he : work (.inl v) ≤ payload v + incoming N v := by
      change (originalProgram N routes v oldID newID portID (old v).program).expandedLoad ≤ _
      rw [hc.2, (old v).size]
      exact Nat.add_le_add_right (cap v).2 _
    have hm := raw_records_original N routes ex prior payload v
    change M = _ at hm
    have hr := (input_rows N ex prior payload v).trans hm.symm.le
    cases ex with
    | false =>
      change _ + (prior v + 1) = M + (pub (.inl v) + 1) at hx
      omega
    | true =>
      have hin : incoming N v ≤ M := (wireCapacity_le N id v prior payload).trans hm.symm.le
      change _ + (prior v + (1 + payload v)) = M + (pub (.inl v) + (1 + work (.inl v))) at hx
      omega
  · have hs : pub (.inr j) = 1036 := (relay_charges N routes newID portID j).1
    have he : work (.inr j) = 0 := (relay_charges N routes newID portID j).2
    cases ex with
    | false =>
      change _ + 1 = M + (pub (.inr j) + 1) at hx
      omega
    | true =>
      change _ + 1 = M + (pub (.inr j) + (1 + work (.inr j))) at hx
      omega

end Packing.Inherited.Subdivision

end BorderVNP
end Computability
end OAI
