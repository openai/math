import OAI.Hierarchy.DescentFallbackMixedQueryBound

namespace OAI
/-! The public operand table cannot issue a serial beyond the full old-item roster. -/
namespace Hierarchy.DescentFallbackOperandBranch.Config
open DescentFallbackItemSelect DescentFallbackOperandQuery DescentPrivateTreeTemplate
open DescentResetLocalRoster DescentHostDirectory DescentPacking.PackedMatch.Local
noncomputable section
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (C : Config)

/-- The final offered word always fits the finite row multiplied by its batch count. -/
theorem serial_of_visible {K start step b : ℕ} (live : Finset (Fin K))
    (allowed : step< min 2 (live.card*b-start)) : (start+step)/b≤K :=by
  have within:=allowed.trans_le (Nat.min_le_right ..)
  have total : start+step<live.card*b:=by omega
  by_cases pos : 0<b
  · exact ((Nat.div_lt_iff_lt_mul pos).mpr total).le.trans (by simpa using live.card_le_univ)
  · have no:b=0:=by omega
    simp [no]

theorem make_serial (side : Bool) (cap height : ℕ) (path : List Bool)
    (root : code C.residual×Option (Fin (2^n))) (items : Fin C.count→Item) (node arg : ℕ)
    {out : ℕ×ℕ×ℕ×Bool} (got : C.make side cap height path root items node arg=some out) :
    (if out.2.2.2 then out.2.1/C.batches else 0)≤C.count :=by
  unfold make at got
  obtain ⟨j,_,row⟩:=Option.bind_eq_some_iff.mp got
  obtain ⟨leaf,_,output⟩:=Option.bind_eq_some_iff.mp row
  dsimp only at output
  split at output
  · rename_i incoming
    split at output
    · obtain ⟨j',_,found⟩:=Option.bind_eq_some_iff.mp output
      cases found
      exact Nat.zero_le _
    · cases output
      exact serial_of_visible (rows C.maxDepth path items) incoming
  · by_cases terminal : path.length=height <;> simp only [terminal, ↓reduceIte] at output
    all_goals
      split at output
      · cases output
      · rename_i accept
        cases output
        exact serial_of_visible _ (Nat.lt_of_not_ge accept)

theorem mixed_serial (node arg : ℕ) (x : C.Data n)
    {out : ℕ×ℕ×ℕ×Bool} (got : C.mixed board node arg x=some out) :
    (if out.2.2.2 then out.2.1/C.batches else 0)≤C.count:=by
  unfold mixed at got
  dsimp only at got
  repeat' first
    | contradiction
    | exact C.relay_serial x _ node arg got
    | exact C.make_serial _ _ _ _ _ _ _ _ got
    | split at got
end
end Hierarchy.DescentFallbackOperandBranch.Config

namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentSIMDLookup DescentFallbackOperandBranch DescentFallbackOperandQuery DescentResetLocalRoster
open DescentPacking.PackedMatch.Local DescentHostDirectory DescentFallbackItemSelect DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (C : Config)

theorem tap_serial (x : C.Data n) (side : Bool) (key : code C.residual)
    (mouth : DescentRotorOperandQueryROM.Shape.Mouth n)
    {out : ℕ×ℕ×ℕ×Bool} (got : C.tap x side key mouth=some out) :
    (if out.2.2.2 then out.2.1/C.batches else 0)≤C.oldConfig.count:=by
  unfold tap at got
  obtain ⟨prior,_,hit⟩:=Option.bind_eq_some_iff.mp got
  dsimp only at hit
  split at hit
  · cases hit
  · rename_i allowed
    split at hit
    · cases hit
      exact DescentFallbackOperandBranch.Config.serial_of_visible (C.portRows x side key mouth) (Nat.lt_of_not_ge allowed)
    · obtain ⟨j,_,found⟩:=Option.bind_eq_some_iff.mp hit
      cases found
      exact Nat.zero_le _

theorem column_serial_le (x : C.Data n) (j : Fin C.oldConfig.mouths)
    (b : ℕ) (batch : C.batches=C.split) :
    (C.column board b (some 2) j x).val≤C.donors*(2*C.oldCap):=by
  let p:=(finProdFinEquiv.symm j : Fin C.args×Fin C.nodes)
  unfold column
  change (match C.mixed board p.2.val p.1.val x with
    | none=>(0:Cell b)
    | some (k,z,t,tag)=>((if tag then z/C.split else 0:ℕ):Cell b)).val≤_
  cases got : C.mixed board p.2.val p.1.val x with
  | none => exact Nat.zero_le _
  | some out =>
    rcases out with ⟨k,z,t,tag⟩
    apply (Nat.mod_le ..).trans
    rw [←batch]
    unfold mixed at got
    split at got
    · cases got
    · split at got <;> first
        | exact C.tap_serial x _ _ _ got
        | exact C.oldConfig.mixed_serial board _ _ _ got
end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
