import OAI.Computability.BorderVNP.PackedFrozenSchemaLeaves
import OAI.Computability.BorderVNP.PackedFrozenSelectedMeasures

/-! # Complete rosters and field-size bounds on the true selected tape formats

Every source row type enumerates its complete fixed rectangle. The template's
nine-field bindings and finite main packets keep a uniform scalar-count cap,
and every stored field retains its producing stage's bit width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Shortening

/-- Physical roster completeness and the two bounds required by the final packet compiler. -/
structure Format.Bounded (S : Format) (cap W : ℕ) : Prop where
  /-- The physical roster contains as many entries as there are reserved row slots. -/
  roster : S.schema.rows.length = Fintype.card S.Rows
  /-- Each row's scalar tag vector fits the fixed relocation and packet-row capacity. -/
  fields : ∀ r, (S.schema.tags r).length ≤ cap
  /-- Its original scalar operands can be widened to the final word width. -/
  width : ∀ r, S.schema.width r ≤ W

variable {cap W : ℕ}

/-- Concatenating two real sources preserves completeness, field sizes, and widths. -/
theorem Format.Bounded.append {S T : Format} (hS : S.Bounded cap W) (hT : T.Bounded cap W) :
    (S.append T).Bounded cap W := by
  constructor
  · exact (S.schema.append_length T.schema).trans ((congrArg₂ (·+·) hS.roster hT.roster).trans
      (Measure.slots.append S T).symm)
  · rintro (r|t)
    · exact hS.fields r
    · exact hT.fields t
  · rintro (r|t)
    · exact hS.width r
    · exact hT.width t

/-- Parallel copies duplicate the whole roster while keeping each row's own word widths. -/
theorem Format.Bounded.parallel {S : Format} (hS : S.Bounded cap W) (k : ℕ) :
    (S.parallel k).Bounded cap W := by
  exact ⟨(S.schema.parallel_length k).trans ((congrArg (k*·) hS.roster).trans (Measure.slots.parallel S k).symm),
    fun r => hS.fields r.2,fun r => hS.width r.2⟩

/-- Every occupied bottom record or reserved hole has exactly its original scalar layout. -/
theorem Format.bounded_bottom {V : Type} [Fintype V] (rs : V → List CellSparse.Record) (holes w : ℕ)
    (tags : ∀ v, ∀ r ∈ rs v, (marked r).length ≤ cap) (width : w ≤ W) :
    (Format.bottom rs holes w).Bounded cap W :=
  ⟨bottom_length rs holes w,bottom_tags rs holes w cap tags,fun _ => width⟩

/-- Every new original endpoint or interior relay of the physical subdivision has nine scalar fields. -/
theorem Format.bounded_subdivision (m np extra w : ℕ) (nine : 9 ≤ cap) (hw : w ≤ W) :
    (Format.subdivision m np extra w).Bounded cap W := by
  refine ⟨subdivision_length w m np extra,fun r => ?_,fun _ => hw⟩
  change (List.ofFn Layer.kind).length ≤ _
  simpa only [List.length_ofFn] using nine

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The entire three-block update fits the stated cap even on malformed or rejected branch pins. -/
theorem bounded_fresh (A : Type) [Fintype A] (old np w : ℕ) (nine : 9 ≤ cap)
    (main : birthTagBound e (0,false) ≤ cap) (hw : w ≤ W) : (freshFormat e A old np w).Bounded cap W := by
  let l := Format.ofSchema (LayerRows.schema old D np w)
  let b := Format.ofSchema (Birth.schema e (0,false) A w)
  let h := Format.ofSchema (HookTape.schema old D w)
  have hl : l.Bounded cap W := by
    refine ⟨layer_length w old D np,fun _ => ?_,fun _ => hw⟩
    change (List.ofFn Layer.kind).length ≤ _
    simpa only [List.length_ofFn] using nine
  have hb : b.Bounded cap W := ⟨birth_length w e (0,false) A,
    fun r => (birth_tags w e (0,false) A r).trans main,fun _ => hw⟩
  have hh : h.Bounded cap W := ⟨hook_length w old D,fun _ => nine,fun _ => hw⟩
  exact hl.append (hb.append hh)

/-- Completeness of the original child tape and the fixed template caps suffice at the next round. -/
theorem Format.Bounded.round {S : Format} (h : S.Bounded cap W) (A : Type) [Fintype A] (k old np w : ℕ)
    (nine : 9 ≤ cap) (main : birthTagBound e (0,false) ≤ cap) (hw : w ≤ W) :
    (Format.round e A k old np w S).Bounded cap W :=
  (h.parallel k).append (bounded_fresh e A old np w nine main hw)

end Packing.Inherited.FrozenTape

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Cover Epoch Shortening Shortening.PublicCapacity PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}
    (S : Normalized.SiteSchedule e) (start w : ℕ)
variable {cap W : ℕ} (nine : 9 ≤ cap) (main : birthTagBound e (0,false) ≤ cap) (hw : w ≤ W)

include nine main hw

/-- Preservation of exact rosters, tag cap and source width throughout one attained inner path. -/
theorem stage_from_epoch_bounded (base : Format) (t : ℕ) (prior : (epoch S start w base t).Bounded cap W)
    (j : ℕ) (hj : j ≤ S.rounds) : (stage S start w base t j).Bounded cap W := by
  induction j with
  | zero =>
    rw [stage_zero]
    exact prior.append (Format.bounded_subdivision _ _ _ w nine hw)
  | succ j ih =>
    rw [stage_next S start w base t ⟨j,hj⟩,innerRound]
    let A := Seeds S.source S.last (S.high (EnrichedOuter.offset S start t)) ⟨j,hj⟩
    let m := S.fanIn*(before S start t j).edges
    let n := Parallel.nestedCapacity S.fanIn (portSlots S start t 0) (j+1)
    have h := (ih (Nat.le_of_succ_le hj)).round e A S.fanIn m n w nine main hw
    apply Eq.mp _ h
    apply congrArg (fun T : Format => T.Bounded cap W)
    exact congrArg (fun fin => @Format.round _ _ _ _ _ e A fin S.fanIn m n w (stage S start w base t j))
      (Subsingleton.elim _ _)

/-- Roster length and per-row physical field bounds on every boundary and every inner stage. -/
theorem all_bounded (base : Format) (initial : base.Bounded cap W) :
    (∀ t, (epoch S start w base t).Bounded cap W) ∧
      ∀ t j, j ≤ S.rounds → (stage S start w base t j).Bounded cap W := by
  have outer (t : ℕ) : (epoch S start w base t).Bounded cap W := by
    induction t with
    | zero => exact initial
    | succ t ih =>
      rw [epoch_next]
      exact stage_from_epoch_bounded S start w nine main hw base t ih S.rounds le_rfl
  exact ⟨outer,fun t j hj => stage_from_epoch_bounded S start w nine main hw base t (outer t) j hj⟩

/-- The list traversed by the actual public geometry compiler has the exact cardinality charged
in the carry-cost proof, for every attained inner step of every complete epoch. -/
theorem stage_roster (base : Format) (initial : base.Bounded cap W) {T t : ℕ}
    (deep : S.floor+1+S.drop*T ≤ start) (ht : t<T) (j : ℕ) (hj : j ≤ S.rounds) :
    (stage S start w base t j).schema.rows.length = priorSlots S start (Fintype.card base.Rows) t j :=
  ((all_bounded S start w nine main hw base initial).2 t j hj).roster.trans
    (stage_slots S start w base deep ht j hj)

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
