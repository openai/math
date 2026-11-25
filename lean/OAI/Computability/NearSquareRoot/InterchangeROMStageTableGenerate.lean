import OAI.Computability.NearSquareRoot.InterchangeROMStageTableTerms

/-! # Numerical matrix files for the five interchangeable stage gates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageTable
open InterchangeROMStage

theorem primrec_gateMatrix : Primrec₂ gateMatrix := by
  let z := fun v : Parameters × Frame.Table => (v.1.2.2.1)
  have hz : Primrec z := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have input : Primrec (fun v : Parameters × Frame.Table => expandRoles v.2.2.1 v.1.2.2.1) :=
    primrec_expandRoles.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hz
  have output : Primrec (fun v : Parameters × Frame.Table => expandRoles v.2.2.2 v.1.2.2.1) :=
    primrec_expandRoles.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hz
  have raw : Primrec fun v : Parameters × Frame.Table =>
      matrix (decode v.1) v.2.1 (expandRoles v.2.2.1 v.1.2.2.1) (expandRoles v.2.2.2 v.1.2.2.1) := by
    let make (v : (Parameters × Frame.Table) × Ground) := terms (decode v.1.1) v.1.2.1 v.2
    let feed (v : (Parameters × Frame.Table) × Ground) : Parameters × ℕ × Ground :=
      (v.1.1,v.1.2.1,v.2)
    have hfeed : Primrec feed := (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
    let selected (z : Parameters × ℕ × Ground) := terms (decode z.1) z.2.1 z.2.2
    have hm := Primrec.comp (f:=selected) (g:=feed) primrec_terms hfeed
    let coeff (v : List Term × Ground) := coefficient v.1 v.2
    let entry (v : ((Parameters × Frame.Table) × Ground) × Ground) := (make v.1,v.2)
    have hentry : Primrec entry := (hm.comp (Primrec.fst (α:=(Parameters × Frame.Table) × Ground) (β:=Ground))).pair Primrec.snd
    have entryCost := Primrec.comp (f:=coeff) (g:=entry) primrec_coefficient hentry
    have row : Primrec (fun z : (Parameters × Frame.Table) × Ground =>
        (expandRoles z.1.2.2.1 z.1.1.2.2.1).map (coefficient (make z))) :=
      Primrec.list_map (input.comp Primrec.fst) entryCost.to₂
    exact Primrec.list_map output row.to₂
  have norm : Primrec (fun z : ((Parameters × Frame.Table) × List ℕ) × ℕ => z.2 % z.1.1.1.2.1) :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.fst.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  exact Primrec.list_map raw (Primrec.list_map Primrec.snd norm.to₂).to₂

end InterchangeROMStageTable

end NearSquareRoot
end Computability
end OAI
