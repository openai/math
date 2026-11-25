import OAI.Computability.BorderVNP.PackedInheritedWorkPrep

/-! # Width of the actual subdivision banks at a compiled epoch input

A retained bank stores the old site's entire program followed by the new incoming words.
At a relay the new incoming words are also part of the installed bank. The tracked
child capacity therefore pays for all three numerical guards of the frozen prep writer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

open Diagonal.ExternalSew Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive
open Packing Packing.PhysicalEpochs Packing.Inherited Shortening.PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

private theorem raw_room {D d j np w : ℕ} {P K : Type} [Field K] [fin : Fintype P]
    {bits : P → ℕ} (outFin : Fintype P) {L δ : ℝ} {hδ : 0 < δ} {s : Shape}
    (z : PlacedPack D P bits K (Cube D) j) (init : InitialSites z L hδ)
    (p : Pack D P bits K) (r : SiteRoutes p (Cube D) d L)
    (hl : j = d) (hp : init.pack = p) (hr : HEq init.routes r)
    (row : Rows s p.layout) (old : @Site.Programs D P fin bits p.layout) (ports : P ↪ Fin np)
    (fit : let orig := congrArg Pack.layout hp.symm
      let saved := congrArg (fun q => q.pack.layout) init.realizes.symm
      let raw := RowTrace.sameRows orig row
      let new := raw.siteRoutes init.routes δ
      let prior := @samePrivatePrograms D P fin bits _ _ orig old
      let sub := @Subdivision.subdividePrivatePrograms D _ _ np P outFin bits init.pack.layout
        (init.routes.routes δ) raw.edge new.edge ports (changePrivateInstance (fin := fin) (fin' := outFin) _ prior)
      let actual := @samePrivatePrograms D P outFin bits _ _ saved sub
      ∀ v, (actual v).program.size < 2^w) :
    (∀ v, @incoming D P fin bits p.layout v < 2^w) ∧ (∀ v, @incoming D P fin bits (r.subdivided δ).layout v < 2^w) ∧
      ∀ v, (old v).program.size + @incoming D P fin bits (r.subdivided δ).layout (.inl v) < 2^w := by
  obtain rfl : outFin = fin := Subsingleton.elim _ _
  subst d; subst p
  obtain rfl := eq_of_heq hr
  rcases init with ⟨p,r,rfl⟩
  let new := row.siteRoutes r δ
  let sub := Subdivision.subdividePrivatePrograms p.layout (r.routes δ) row.edge new.edge ports old
  have bound (v) : (sub v).program.size < 2^w := fit v
  have retained (v) : (old v).program.size + incoming (r.subdivided δ).layout (.inl v) < 2^w :=
    bound (.inl v)
  refine ⟨?_,?_,retained⟩
  · intro v
    calc incoming p.layout v = (old v).program.incoming := (old v).size.symm
         _ ≤ (old v).program.size := Nat.le_add_left _ _
         _ < 2^w := (Nat.le_add_right _ _).trans_lt (retained v)
  · intro v
    calc incoming (r.subdivided δ).layout v = (sub v).program.incoming := (sub v).size.symm
         _ ≤ (sub v).program.size := Nat.le_add_left _ _
         _ < 2^w := bound v

variable {D m start T t w : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {budget V E cap : ℕ → ℕ}
    {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}
    (A : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)

set_option maxHeartbeats 1600000 in
/-- The real child tile capacity and the actual leaf word bound imply all three guards on
the raw route consumed by the selected prep writer, before it is renamed to its saved layout. -/
theorem prep_room (rows : A.epoch.F.SiteRows)
    (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)
    (old : ∀ i, Site.Programs (c i).val.pack.layout) {B : ℕ}
    (childCap : ∀ i, SiteCap (c i).val.route (Subdivision.publicProgramData (old i)) true B)
    (leafFit : 1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) ×
      Fin (hopCount S.budget S.radius)))*B < 2^w) (i : Fin (fan S)) :
    (∀ v, incoming (c i).val.pack.layout v < 2^w) ∧
      (∀ v, incoming ((routes deep ht c i).subdivided S.radius).layout v < 2^w) ∧
      ∀ v, (old i v).program.size+incoming ((routes deep ht c i).subdivided S.radius).layout (.inl v) < 2^w := by
  let run := (A.returned c).run
  exact raw_room (P := Port (fan S) P t) (fin := portFintype (P := P) (k := fan S) (b := t))
    (portFintype (P := Port (fan S) P t) (k := S.fanIn) (b := 0))
    (run.flat i).val.placed (run.initialSites i) (c i).val.pack (routes deep ht c i)
    (S.start_level (offset S start t)) (run.originalPack i) (run.originalRoutes i)
    (c i).val.rows (old i) (rows.ports 0) (A.widthPre_room rows c old childCap leafFit i)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

end BorderVNP
end Computability
end OAI
