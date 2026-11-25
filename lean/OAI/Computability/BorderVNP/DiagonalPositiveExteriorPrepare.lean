import OAI.Computability.BorderVNP.DiagonalPositiveExteriorRoutes
import OAI.Computability.BorderVNP.RoutingISASignedPrepJoint

/-! # The exterior and route cut on the original signed preparation program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.Scatter Cube.Tally

variable {R r t d link inner n w : ℕ} {Edge : Type}
variable (G : Wiring R r t d link inner n Edge) (L : WireLayout (R+1) r link)
variable (tab : TableLayout) (row : ℕ → TableRow) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
variable (guess : Fin (R+1) → ℕ → Bool) (g : SharedRows.Layout)
variable {axes groups blocks K h b symbols : ℕ} (decl : LengthDeclaration axes groups)
variable (fixed : Block (R+1)) (header : List Bool) (len : header.length = L.header)
variable (id : TableEntry axes b h K symbols → ℕ)

local notation "Input" => signedInputs id (TeamRows.ownedGroups axes b h K symbols)
local notation "Prepared" => prepareExpansion epochPlacement (scheduleGroups axes (selectorWidth axes K h)) Input
local notation "Domain" => HeaderExterior L header
set_option quotPrecheck false in
local notation "Raw" => {z : Symbols groups → List Bool // ∀ p, (z p).length = SharedRows.reserved blocks K h decl p}

/-- At a fixed source header, the complete joint signed preparation on every
physical exterior is equivalent to its shared row words and the remaining native
input builders on the unique routed exterior. All chronological branch and
post-route memory dependencies of the original signed program are retained. -/
noncomputable def exteriorPreparedEquiv {pin : Fin d → Bool} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {dst ib hb sb : Fin (R+1) → ℕ} {src : HeaderExterior L header → Fin (R+1) → ℕ → ℕ}
    {group : Fin groups → Fin (R+1)} {anchor : Fin (R+1)}
    (pub : Domain → Fin (R+1) → Arg → Word w) (mac : Domain → Fin (R+1) → TeamOpcode.Macros w 8)
    (bank : Domain → Fin (R+1) → Bank w) (mem : Domain → Fin (R+1) → Memory w)
    (schedule : ∀ x u, Returns (SignedPrep.schedule axes K h) (pub x u) (mac x u) (bank x u) (mem x u))
    (empty : ∀ x u, (schedule x u).val.1.flatMap TeamRAM.Event.choices = [])
    (initialized : ∀ x : Domain, SharedRoutePrepared G pin x.val L D pp lp owner origin stride tab row (pub x)
      (fun u => (schedule x u).val.2.2) dst ib hb sb guess)
    (copies : ∀ x : Domain, ReturnedHeaders G pin x.val L w)
    (emitted : ∀ x u, g.Emitted (src x u) (readings (schedule x u).val.2.2)) (fitted : ∀ x u, g.Fits w (src x u))
    (records : tab.records = g.records) (count : tab.count = g.dataCount+g.groups.choose 2)
    (dataCount : (D.directory pp lp).length = g.dataCount) (room : g.banks+g.stride*g.groups^2 ≤ 2^w)
    (frame : ∀ x, SymbolFrame g (src x anchor) blocks K h decl group) :
    let E := exteriorNativeRoutesEquiv G L tab row D pp lp guess g decl fixed header len pub mac
      (fun x u => (schedule x u).val.2.1) (fun x u => (schedule x u).val.2.2) initialized copies
      emitted fitted records count dataCount room frame
    (Σ x : Domain, ∀ u, Returns Prepared (pub x u) (mac x u) (bank x u) (mem x u)) ≃
      Σ z : Raw, let replay := E.symm z
        ∀ u, Returns Input (pub replay.1 u) (mac replay.1 u) (replay.2 u).val.2.1 (replay.2 u).val.2.2 := by
  intro E
  let routes (x : Domain) := ∀ u, Returns route (pub x u) (mac x u) (schedule x u).val.2.1 (schedule x u).val.2.2
  let rest (x : Domain) (z : routes x) := ∀ u, Returns Input (pub x u) (mac x u) (z u).val.2.1 (z u).val.2.2
  let cut := Equiv.sigmaCongrRight fun x : Domain => SignedPrep.jointRouteCut id (schedule x) (empty x)
  exact cut.trans ((Equiv.sigmaAssoc rest).symm.trans (Equiv.sigmaCongrLeft' E))

end TeamContraction

end BorderVNP
end Computability
end OAI
