import OAI.Computability.BorderVNP.DiagonalPhysicalPinStart
import OAI.Computability.BorderVNP.DiagonalNativeProfilePrefix

/-! # Parsing physical exterior and substituted-index fields before the private validation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator Routing ProcessorSlots JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve axes groups cap dim tally : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (live : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1))
    (hw : 0<w) (size : ∀ i, (args i).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ i, (G.transferFrame i (args i).header (args i).dst).Fits w (base i))
    (width : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)

local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally
local notation "X" => {ext : Exterior R r link → Bool // PositiveExterior G args live w ext}
local notation "headers" => positiveExteriorFieldsEquiv G args live L fixed hw size base fit width
variable {box lanes selectors symbols : ℕ} {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    (S : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext} → Fin (R+1) → PinStart gen n w)
    (ib hb sb : Fin (R+1) → ℕ)
    (pinWidth : ∀ x u, (S x u).guessWidth=(G.pinLayout u (ib u) (hb u) (sb u)).guessWidth)

/-- Actual per-team native preparations at one specified substituted raw
word. The prepared local pins are numbered in the physically booted width. -/
abbrev pinnedPreps (id : TableEntry axes box lanes selectors symbols → ℕ) (x : X) (i : Fin d → Bool) :=
  (u : Fin (R+1)) → SignedPreps id (S x u).pub (S x u).routines gen n (S x u).bank (S x u).memory (S x u).pins
    ((Equiv.arrowCongr (finCongr (pinWidth x u).symm) (Equiv.refl Bool)) ((G.jointGuess ib hb sb).symm i u))

/-- Recover one substituted raw word and one full parsed public header from every
joint pre-call history. Its other external bits and every native preparation are retained. -/
noncomputable def parsedPrefixEquiv :
    ((x : X) × ((u : Fin (R+1)) → (S x u).Prefix id)) ≃
      Σ i : Fin d → Bool, Σ p : Fields, Σ ext : HeaderExterior L p.bits,
        pinnedPreps G args live S ib hb sb pinWidth id ((headers).symm ⟨p,ext⟩) i := by
  let E := headers
  let split (i : Fin d → Bool) :=
    (Equiv.sigmaCongrLeft' (β:=fun x : X => pinnedPreps G args live S ib hb sb pinWidth id x i) E).trans
      (Equiv.sigmaAssoc fun p ext => pinnedPreps G args live S ib hb sb pinWidth id (E.symm ⟨p,ext⟩) i)
  let sectionMap (x : X) := G.jointPrefixes ib hb sb fun u digits =>
    SignedPreps id (S x u).pub (S x u).routines gen n (S x u).bank (S x u).memory (S x u).pins
      ((Equiv.arrowCongr (finCongr (pinWidth x u).symm) (Equiv.refl Bool)) digits)
  let retitle (x : X) := Equiv.piCongrRight fun u => (Equiv.sigmaCongrLeft
    (β:=SignedPreps id (S x u).pub (S x u).routines gen n (S x u).bank (S x u).memory (S x u).pins)
    (Equiv.arrowCongr (finCongr (pinWidth x u).symm) (Equiv.refl Bool))).symm
  let swap : (Σ x : X, Σ i : Fin d → Bool, pinnedPreps G args live S ib hb sb pinWidth id x i) ≃
      (Σ i : Fin d → Bool, Σ x : X, pinnedPreps G args live S ib hb sb pinWidth id x i) :=
    ⟨fun a => ⟨a.2.1,a.1,a.2.2⟩,fun a => ⟨a.2.1,a.1,a.2.2⟩,fun _ => rfl,fun _ => rfl⟩
  exact ((Equiv.sigmaCongrRight fun x => (retitle x).trans (sectionMap x)).trans swap).trans (Equiv.sigmaCongrRight split)

end TeamContraction

namespace TeamContraction.JointHeader.PositiveFields

open Cube.Physical
variable {reserve axes groups cap teams dim tally : ℕ} {Hist : Type}
    (code : Hist ↪ (Fin reserve → Bool))
local notation "Fields" => PositiveFields reserve axes groups cap teams dim tally
local notation "Cube" => Broadcast axes groups cap
local notation "Claim" => (Fin (teams*dim*tally) → Bool)

/-- A successful physical preparation fixes its genuine geometry history;
the cube declaration and subtotal digits are retained verbatim. -/
noncomputable def historyFieldsEquiv (F : Fields → Type) (recognized : ∀ p, F p → ∃ q, code q=p.profile) :
    (Σ p : Fields, F p) ≃ (Σ q : Hist, Σ cube : Cube, Σ claim : Claim, F ⟨code q,cube,claim⟩) := by
  let source := Σ q : Hist, Σ cube : Cube, Σ claim : Claim, F ⟨code q,cube,claim⟩
  let restore (a : source) : Σ p : Fields, F p := ⟨⟨code a.1,a.2.1,a.2.2.1⟩,a.2.2.2⟩
  refine (Equiv.ofBijective restore ⟨?_,?_⟩).symm
  · rintro ⟨q,c,d,x⟩ ⟨q',c',d',y⟩ same
    obtain ⟨fields,vals⟩ := Sigma.mk.inj same
    obtain rfl : q=q' := code.injective (congrArg PositiveFields.profile fields)
    obtain rfl : c=c' := congrArg PositiveFields.cube fields
    obtain rfl : d=d' := congrArg PositiveFields.subtotals fields
    obtain rfl := eq_of_heq vals
    rfl
  · rintro ⟨⟨p,c,d⟩,x⟩
    obtain ⟨q,eq⟩ := recognized ⟨p,c,d⟩ x
    change code q=p at eq
    subst p
    exact ⟨⟨q,c,d,x⟩,rfl⟩

end TeamContraction.JointHeader.PositiveFields

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator Routing ProcessorSlots JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve axes groups cap dim tally : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (live : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1))
    (hw : 0<w) (size : ∀ i, (args i).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ i, (G.transferFrame i (args i).header (args i).dst).Fits w (base i))
    (width : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)

local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally
local notation "Cube" => Physical.Broadcast axes groups cap
local notation "Claim" => (Fin ((R+1)*dim*tally) → Bool)
local notation "headers" => positiveExteriorFieldsEquiv G args live L fixed hw size base fit width
variable {box lanes selectors symbols : ℕ} {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    (S : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext} → Fin (R+1) → PinStart gen n w)
    (ib hb sb : Fin (R+1) → ℕ)
    (pinWidth : ∀ x u, (S x u).guessWidth=(G.pinLayout u (ib u) (hb u) (sb u)).guessWidth)

local notation3 (prettyPrint := false) "runs(" i "," p ")" => ((ext : HeaderExterior L (PositiveFields.bits p)) ×
  pinnedPreps G args live S ib hb sb pinWidth id ((headers).symm ⟨p,ext⟩) i)

private def swapFields {A B : Type} (F : A → B → Type) :
    (Σ a : A, Σ b : B,F a b) ≃ (Σ b : B, Σ a : A,F a b) :=
  ⟨fun x => ⟨x.2.1,x.1,x.2.2⟩,fun x => ⟨x.2.1,x.1,x.2.2⟩,fun _ => rfl,fun _ => rfl⟩

/-- Compose the actual substituted pin and parsed exterior with the genuine
profile checker and the pre-call route/report reconstruction at each fixed
profile and subtotal bank. All candidate subtotal words remain in this
unfiltered prefix domain. -/
noncomputable def jointPreparedFields {Hist : Type} {Route : Hist → Type}
    {Report : (i : Fin d → Bool) → (q : Hist) → Route q → Type}
    (code : Hist ↪ (Fin reserve → Bool))
    (valid : ∀ i (p : Fields), runs(i,p) → ∃ q, code q=p.profile)
    (routed : ∀ i q (claim : Claim), (Σ c : Cube,runs(i,(⟨code q,c,claim⟩ : Fields))) ≃
      Σ v : Route q,Report i q v) :
    ((x : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext}) × ((u : Fin (R+1)) → (S x u).Prefix id)) ≃ PreparedFields (Fin d → Bool) Hist Claim Route Report := by
  let parse := parsedPrefixEquiv (id:=id) G args live L fixed hw size base fit width S ib hb sb pinWidth
  refine parse.trans (Equiv.sigmaCongrRight fun i => ?_)
  let profile := PositiveFields.historyFieldsEquiv code (fun p : Fields => runs(i,p)) (valid i)
  refine profile.trans (Equiv.sigmaCongrRight fun q => ?_)
  let swap := swapFields (fun (c : Cube) (claim : Claim) => runs(i,(⟨code q,c,claim⟩ : Fields)))
  exact ((swap.trans (Equiv.sigmaCongrRight (routed i q))).trans (swapFields (fun (_ : Claim) v => Report i q v))).trans
    (Equiv.sigmaCongrRight fun v => Equiv.sigmaEquivProd Claim (Report i q v))

end TeamContraction

end BorderVNP
end Computability
end OAI
