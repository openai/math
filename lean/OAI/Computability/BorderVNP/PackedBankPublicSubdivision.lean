import OAI.Computability.BorderVNP.PackedBankPublicNodes
import OAI.Computability.BorderVNP.PackedSubdivisionCharges
import OAI.Computability.BorderVNP.ShortenEpochRoundRecordTree

/-! # Public records on a realized wire subdivision

Each retained program appends the equalities for its nonempty input words.
Each inserted relay contributes its own equality packet. The public tile
estimate counts these records through the placement of the physical leaf.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Cover Crossing Shortening Epoch.Round InheritedBank
open scoped Classical
open private input_rows from OAI.Computability.BorderVNP.PackedSubdivisionCharges

variable {D m n np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (routes : N.WireRoutes) (oldID : N.Edge ↪ Fin m)
    (newID : (N.subdivide routes).Edge ↪ Fin n) (portID : P ↪ Fin np)
local notation "G" => N.subdivide routes

/-- Charge the serialized public part of each installed lineage to its own site. -/
def publicProgramData {Q : Type} [Fintype Q] {widths : Q → ℕ} {layout : Network D Q widths}
    (programs : Site.Programs layout) : RecordData layout :=
  ⟨fun v => (programs v).program.publicNodes,fun v => (programs v).program.expandedLoad⟩

/-- Public charge of the new whole-word endpoint rows, in the order used by the installed program. -/
theorem original_publicNodes (v : N.Site) (s : Site) :
    (originalProgram N routes v oldID newID portID s).publicNodes =
      s.publicNodes + 1034 * (cuts N routes v oldID newID portID).length :=
  s.publicNodes_retain ..

/-- Public word fields and guard nodes of the relay's single compressed equality. -/
theorem relay_publicNodes (j : (e : N.Edge) × Fin (routes.interior e)) :
    (relaySite N routes newID portID j).publicNodes = 1035 := by
  simp [Site.publicNodes, relaySite, Site.rows, relayRecord, CellSparse.Packet.fieldList,
    CellSparse.Packet.record, CellSparse.Packet.port, CellSparse.Directory.recordNodes, CellSparse.Record.guardMassBound]

private theorem programs_load_le (old : Site.Programs N) (prior payload : N.Site → ℕ)
    (cap : ∀ v, (old v).program.publicNodes ≤ prior v) (ex : Bool)
    (work : ex = true → ∀ v, (old v).program.expandedLoad ≤ payload v) (nextPayload : (G).Site → ℕ)
    (used : ex = true → ∀ v, nextPayload v ≤
      (subdividePrivatePrograms N routes oldID newID portID old v).program.expandedLoad) (test : (G).Site → Prop) :
    let next := subdividePrivatePrograms N routes oldID newID portID old
    localRecords G ex (fun v => (next v).program.publicNodes) nextPayload test ≤
      1040 * localRecords G ex (Sum.elim prior (fun _ => 0)) (Sum.elim payload (fun _ => 0)) test := by
  intro next
  let hist : (G).Site → ℕ := Sum.elim prior (fun _ => 0)
  let data : (G).Site → ℕ := Sum.elim payload (fun _ => 0)
  let pub := fun v => (next v).program.publicNodes
  apply localRecords_of_singletons G ex hist data pub nextPayload
  intro z
  let M := localRecords G ex hist data (fun u => u = z)
  have exchange := exchange_site_records G ex hist data pub nextPayload z
  change _ + boxCost ex (hist z) (data z) = M + boxCost ex (pub z) (nextPayload z) at exchange
  change _ ≤ 1040 * M
  cases z with
  | inl v =>
    have raw := raw_records_original N routes ex prior payload v
    change M = _ at raw
    have rows := (cuts_count N routes v oldID newID portID).trans
      ((input_rows N ex prior payload v).trans raw.symm.le)
    have cost : pub (.inl v) ≤ prior v + 1034*M :=
      (original_publicNodes N routes oldID newID portID v (old v).program).le.trans
        (Nat.add_le_add (cap v) (Nat.mul_le_mul_left _ rows))
    cases ex with
    | false =>
      change _ + (prior v + 1) = M + (pub (.inl v) + 1) at exchange
      omega
    | true =>
      have size := (original_program_charges N routes v oldID newID portID (old v).program).2
      rw [(old v).size] at size
      have extra : nextPayload (.inl v) ≤ (old v).program.expandedLoad + incoming N v :=
        (used rfl (.inl v)).trans size.le
      have inc : incoming N v ≤ M := (CellAddresses.wireCapacity_le N id v prior payload).trans raw.symm.le
      have paid := work rfl v
      change _ + (prior v + (1 + payload v)) = M + (pub (.inl v) + (1 + nextPayload (.inl v))) at exchange
      omega
  | inr j =>
    have unit : 1 ≤ M := one_le_siteRecords G ex hist data (.inr j)
    have cost : pub (.inr j) = 1035 := relay_publicNodes N routes newID portID j
    cases ex with
    | false =>
      change _ + 1 = M + (pub (.inr j) + 1) at exchange
      omega
    | true =>
      have extra : nextPayload (.inr j) ≤ 0 := (used rfl (.inr j)).trans (relay_charges N routes newID portID j).2.le
      change _ + 1 = M + (pub (.inr j) + (1 + nextPayload (.inr j))) at exchange
      omega

/-- A regional public bound on the actual installed programs, assuming a public bound
on the earlier programs. The same estimate applies for every choice of private tables. -/
theorem publicPrograms_load_le (old : Site.Programs N) (prior payload : N.Site → ℕ)
    (cap : ∀ v, (old v).program.publicNodes ≤ prior v) (nextPayload : (G).Site → ℕ) (test : (G).Site → Prop) :
    let next := subdividePrivatePrograms N routes oldID newID portID old
    localRecords G false (fun v => (next v).program.publicNodes) nextPayload test ≤
      1040 * localRecords G false (Sum.elim prior (fun _ => 0)) (Sum.elim payload (fun _ => 0)) test :=
  programs_load_le N routes oldID newID portID old prior payload cap false (by simp) nextPayload (by simp) test

/-- Both record modes on the actual subdivision charge the old descriptors. Expanded
records additionally charge the staged incidence suffix and the old private visits. -/
theorem bankPrograms_load_le (old : Site.Programs N) (prior payload : N.Site → ℕ)
    (cap : ∀ v, (old v).program.publicNodes ≤ prior v) (ex : Bool)
    (work : ex = true → ∀ v, (old v).program.expandedLoad ≤ payload v) (test : (G).Site → Prop) :
    let next := subdividePrivatePrograms N routes oldID newID portID old
    localRecords G ex (fun v => (next v).program.publicNodes) (fun v => (next v).program.expandedLoad) test ≤
      1040 * localRecords G ex (Sum.elim prior (fun _ => 0)) (Sum.elim payload (fun _ => 0)) test :=
  programs_load_le N routes oldID newID portID old prior payload cap ex work _ (fun _ _ => le_rfl) test

end Packing.Inherited.Subdivision

namespace Epoch.Round.InitialSites

open Cover Crossing Shortening Packing.Inherited Packing.Inherited.Subdivision
open scoped Classical

variable {D d m n np : ℕ} {P I : Type} [Fintype P] [Fintype I] {R : Type*} [CommSemiring R]
    {bits : P → ℕ} {L δ : ℝ} {hδ : 0 < δ} {p : PlacedPack D P bits R I d} (s : InitialSites p L hδ)
    (oldID : s.pack.layout.Edge ↪ Fin m)
    (newID : (s.pack.layout.subdivide (s.routes.routes δ)).Edge ↪ Fin n) (portID : P ↪ Fin np)

/-- Install the actual old and relay programs at the sites of the realized physical leaf. -/
noncomputable def installedPublicPrograms (old : Site.Programs s.pack.layout) : Site.Programs p.pack.layout :=
  cast (congrArg (fun q : PlacedPack D P bits R I d => Site.Programs q.pack.layout) s.realizes.symm)
    (subdividePrivatePrograms s.pack.layout (s.routes.routes δ) oldID newID portID old)

/-- Both local record modes count the actual installed public words. Expanded mode also
accounts for the forced old incidence suffix at each retained site. -/
theorem installedBankPrograms_within (old : Site.Programs s.pack.layout) (data : RecordData s.pack.layout)
    (cap : ∀ v, (old v).program.publicNodes ≤ data.prior v) (ex : Bool)
    (work : ex = true → ∀ v, (old v).program.expandedLoad ≤ data.payload v) (M : ℕ)
    (hm : ∀ t, localRecords s.pack.layout ex data.prior data.payload
      (fun v => reduceMove d (s.routes.origin v) = t) ≤ M) :
    RecordsWithin p (publicProgramData (s.installedPublicPrograms oldID newID portID old)) ex
      (1040*((1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L δ)))*(1+M))) := by
  rcases s with ⟨input,r,rfl⟩
  intro tile
  have region := bankPrograms_load_le input.layout (r.routes δ) oldID newID portID old data.prior data.payload cap ex work
    (fun v => productAddress d (r.physical δ v) = tile)
  have raw := (r.initial_tensor_records (h := δ) data.prior data.payload).2 ex M hm tile
  change 1 + localRecords (input.layout.subdivide (r.routes δ)) ex _ _ _ ≤ _ at raw ⊢
  have scale (k : ℕ) : 1040 + 1040*k = 1040*(1+k) := by omega
  exact (Nat.add_le_add (by decide : 1 ≤ 1040) region).trans
    ((scale _).le.trans (Nat.mul_le_mul_left 1040 raw))

/-- Each tile of the realized leaf satisfies the subdivision multiplier for its installed
public words, including every new endpoint tie and every relay equality. -/
theorem installedPublicPrograms_within (old : Site.Programs s.pack.layout) (data : RecordData s.pack.layout)
    (cap : ∀ v, (old v).program.publicNodes ≤ data.prior v) (M : ℕ)
    (hm : ∀ t, localRecords s.pack.layout false data.prior data.payload
      (fun v => reduceMove d (s.routes.origin v) = t) ≤ M) :
    RecordsWithin p (publicProgramData (s.installedPublicPrograms oldID newID portID old)) false
      (1040*((1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L δ)))*(1+M))) :=
  s.installedBankPrograms_within oldID newID portID old data cap false (by simp) M hm

/-- A cap at the input's certified route depth transfers across the exact pack and route
identifications and bounds the programs installed on the realized leaf. -/
theorem installedPublicPrograms_reindex_within {a : ℕ} {input : Pack D P bits R} (route : SiteRoutes input I a L)
    (hd : d = a) (hp : s.pack = input) (hr : HEq s.routes route)
    (old : Site.Programs input.layout) (data : RecordData input.layout)
    (cap : ∀ v, (old v).program.publicNodes ≤ data.prior v) (M : ℕ)
    (hm : ∀ t, localRecords input.layout false data.prior data.payload
      (fun v => reduceMove a (route.origin v) = t) ≤ M) :
    let source := cast (congrArg (fun q : Pack D P bits R => Site.Programs q.layout) hp.symm) old
    RecordsWithin p (publicProgramData (s.installedPublicPrograms oldID newID portID source)) false
      (1040*((1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L δ)))*(1+M))) := by
  subst a
  subst input
  obtain rfl := eq_of_heq hr
  exact s.installedPublicPrograms_within oldID newID portID old data cap M hm

end Epoch.Round.InitialSites

end BorderVNP
end Computability
end OAI
