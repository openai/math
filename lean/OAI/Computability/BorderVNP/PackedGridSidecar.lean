import OAI.Computability.BorderVNP.PackedGridTrueReports

/-! # Actual physical sidecar ordinals enumerate the owned exponent slots once -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Diagonal.CellEntries TallySidecar

/-- A fixed ordered list with distinct keys and the exact image of a set of
owned source slots indexes those slots bijectively. -/
noncomputable def ordinalEquiv {S K : Type} (ps : List Position) (key : Position → K)
    (name : S ↪ K) (unique : (ps.map key).Nodup)
    (live : ∀ k, k ∈ ps.map key ↔ ∃ s, name s = k) : Fin ps.length ≃ S := by
  have h (i : Fin ps.length) : ∃ s, name s = key (ps.get i) :=
    (live _).mp (List.mem_map.mpr ⟨_,List.get_mem ..,rfl⟩)
  let f (i : Fin ps.length) := (h i).choose
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    have hk : key (ps.get i) = key (ps.get j) :=
      (h i).choose_spec.symm.trans ((congrArg name hij).trans (h j).choose_spec)
    have ht : Function.Injective (ps.map key).get := List.nodup_iff_injective_get.mp unique
    have he := ht (a₁ := ⟨i.val,by simp⟩) (a₂ := ⟨j.val,by simp⟩) (by
      simpa only [List.get_eq_getElem,List.getElem_map] using hk)
    exact Fin.ext (congrArg (@Fin.val (ps.map key).length) he)
  · intro s
    obtain ⟨p,hp,hps⟩ := List.mem_map.mp ((live (name s)).mpr ⟨s,rfl⟩)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
    exact ⟨i,name.injective ((h i).choose_spec.trans ((congrArg key hi).trans hps))⟩

/-- Decoding each live row recovers exactly its recorded source key. -/
theorem ordinalEquiv_key {S K : Type} (ps : List Position) (key : Position → K) (name : S ↪ K)
    (unique : (ps.map key).Nodup) (live : ∀ k, k ∈ ps.map key ↔ ∃ s, name s = k) (i : Fin ps.length) :
    name (ordinalEquiv ps key name unique live i) = key (ps.get i) :=
  ((live _).mp (List.mem_map.mpr ⟨_,List.get_mem ps i,rfl⟩)).choose_spec

/-- The staged relative address of position i is its compact ordinal plus the
fixed report suffix start. -/
theorem position_lane (next : ℕ) (fs : List CellSparse.Factor) (i : Fin (positions next fs).length) :
    ((positions next fs).get i).stagedReportRel = next+i.val := by
  have h := congrArg (fun xs : List ℕ => xs[i.val]?) (positions_ranks next fs)
  have h1 : i.val < ((positions next fs).map Position.stagedReportRel).length := by simpa using i.isLt
  have h2 : i.val < (List.range' next (count fs)).length := by simpa using i.isLt
  simpa only [List.getElem?_eq_getElem h1,List.getElem?_eq_getElem h2,List.getElem_map,List.getElem_range',
    Nat.one_mul,Option.some.injEq,List.get_eq_getElem] using h

end Packing.BottomReports

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse BottomReports GridBoxes Diagonal.CellEntries GridPlacement Cover TeamContraction TallySidecar
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- The stored source name and exponent bit place, in the same order as the
formal weighted input of the actual parse verifier. -/
def sidecarReport (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) (j : WeightSites n g r d) : Port :=
  sourceTag (code j.1) j.2.val

variable (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p : ℕ} (siteID : (W.routedFine position).Site ↪ Fin s) (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p) (c : Fin q → Deck (depth+2)) (next : ℕ)

/-- Real named exponent slots whose verifier vertices were assigned to this cell. -/
abbrev OwnedSlot := {j : WeightSites n g r d // cell position W.route (W.routedPowerSite position j) = c}

/-- Positions in the actual sidecar emitted from the ordered sparse bottom factors. -/
noncomputable abbrev sidecarPositions :=
  positions next (factors (W.routedFine position) (cell position W.route) c siteID edgeID portID
    (fun v => W.routedRules position (sidecarReport code) v.val))

private abbrev labelKey (p : Position) := (p.parameter,p.place)

private def ownedKey : W.OwnedSlot position c ↪ ℕ × ℕ where
  toFun j := (code j.val.1,j.val.2.val)
  inj' := by intro i j he; exact Subtype.ext (Prod.ext (code.injective (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he)))

private theorem sidecarKeys :
    (W.sidecarPositions position code siteID edgeID portID c next).map labelKey =
      (siteList (W.routedFine position) (cell position W.route) c siteID).filterMap
        (fun v => (ruleTag (W.routedRules position (sidecarReport code) v.val)).map (fun p => (p.base,p.copyStride))) :=
  (grid_labels (W.routedFine position) (cell position W.route) c siteID edgeID portID
    (fun v => W.routedRules position (sidecarReport code) v.val) next).trans List.map_filterMap

private theorem rule_key (v : (W.routedFine position).Site) (k : ℕ × ℕ) :
    (ruleTag (W.routedRules position (sidecarReport code) v)).map (fun p => (p.base,p.copyStride)) = some k ↔
      ∃ j, W.routedPowerSite position j = v ∧ (code j.1,j.2.val) = k := by
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨p,hp,hk⟩
    obtain ⟨j,hv,rfl⟩ := (W.routed_ruleTag_iff position (sidecarReport code) v p).mp hp
    exact ⟨j,hv,hk⟩
  · rintro ⟨j,hv,rfl⟩
    exact ⟨sidecarReport code j,(W.routed_ruleTag_iff position (sidecarReport code) v _).mpr ⟨j,hv,rfl⟩,rfl⟩

private theorem keyProperties :
    ((W.sidecarPositions position code siteID edgeID portID c next).map labelKey).Nodup ∧
      ∀ k, k ∈ (W.sidecarPositions position code siteID edgeID portID c next).map labelKey ↔
        ∃ j : W.OwnedSlot position c, W.ownedKey position code c j = k := by
  rw [sidecarKeys]
  constructor
  · apply List.Nodup.filterMap
    · intro i j key hi hj
      obtain ⟨s,hs,hsk⟩ := (W.rule_key position code i.val key).mp hi
      obtain ⟨u,hu,huk⟩ := (W.rule_key position code j.val key).mp hj
      have eq : s = u := Prod.ext (code.injective (congrArg Prod.fst (hsk.trans huk.symm)))
        (Fin.ext (congrArg Prod.snd (hsk.trans huk.symm)))
      exact Subtype.ext (hs.symm.trans ((congrArg (W.routedPowerSite position) eq).trans hu))
    · unfold siteList
      apply List.nodup_ofFn_ofInjective
      exact Equiv.injective _
  · intro key
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨v,_,hv⟩
      obtain ⟨j,hj,hk⟩ := (W.rule_key position code v.val key).mp hv
      exact ⟨⟨j,(congrArg (cell position W.route) hj).trans v.property⟩,hk⟩
    · rintro ⟨j,hk⟩
      let v := (⟨W.routedPowerSite position j.val,j.property⟩ : {v // cell position W.route v = c})
      exact ⟨v,mem_siteList ..,(W.rule_key position code v.val key).mpr ⟨j.val,rfl,hk⟩⟩

/-- Bijective decoding of the actual one-copy sidecar's ordinal, retaining the
true physical cell and identifying the named formal power slot. -/
noncomputable def sidecarEquiv :
    Fin (W.sidecarPositions position code siteID edgeID portID c next).length ≃ W.OwnedSlot position c :=
  let properties := W.keyProperties position code siteID edgeID portID c next
  ordinalEquiv _ labelKey (W.ownedKey position code c) properties.1 properties.2

/-- Parameter, bit place, and staged report lane of the actual indexed sidecar row. -/
theorem sidecarEquiv_fields (i : Fin (W.sidecarPositions position code siteID edgeID portID c next).length) :
    let j := W.sidecarEquiv position code siteID edgeID portID c next i
    let p := (W.sidecarPositions position code siteID edgeID portID c next).get i
    p.parameter = code j.val.1 ∧ p.place = j.val.2.val ∧ p.stagedReportRel = next+i.val := by
  intro j p
  have hh := ordinalEquiv_key _ labelKey (W.ownedKey position code c)
    (W.keyProperties position code siteID edgeID portID c next).1 (W.keyProperties position code siteID edgeID portID c next).2 i
  exact ⟨(congrArg Prod.fst hh).symm,(congrArg Prod.snd hh).symm,position_lane next _ i⟩

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
