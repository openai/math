import OAI.Hierarchy.TaggedWireChordTurns
import OAI.Hierarchy.TaggedWireReportMatrix

namespace OAI
/-! # Reading the paid terminal report into the physical equality gates -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph

theorem rebase_apply {K : ℕ} {F : Type*} {A B U V : Widths K} (old : A=B) (new : U=V)
    (M : SiteMatrix (State A) (State U) F) (s : Fin K) (x : State B s) (y : State V s) :
    rebase old new M s x y=M s (cast (congrArg (fun t=>State t s) old.symm) x)
      (cast (congrArg (fun t=>State t s) new.symm) y) := by
  subst B
  subst V
  rfl

end Hierarchy.WireTelescope
namespace Hierarchy.ProbeStage.CoreBoard.MatrixReceipt
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing AdaptiveProbe WireTelescope ProtocolRAMEmit
open scoped Classical BigOperators

variable {S : PurchaseSampler} {F : Type*} [Field F] {h k d w edges r M den : ℕ} {b : Fin k→ℕ}
    {D : TaggedPrune.Layout h w b} {π : Equiv.Perm (Tagged.Row h)} {place : Site h d k→Fin (D.last+1)}
    {B : Mount (S:=S) π place edges} {fixed : Fin edges→ℕ}
    {stock : Commodity (Fin (2^h)) (Stages h d) k→ℕ} {reserved used : Columns h d×Fin k→ℕ}
    {rows : Fin edges→ProtocolRAMEmit.Row} {G : Geometry D M den rows}
    (H : MatrixReceipt B fixed stock reserved used G) (inj : Function.Injective place) (pad : Chord (D.last+1))
    (enum : Fin r≃RouteOccurrence B.ordinary B.centers)

local notation "L" => B.matrixLayout inj pad
local notation "counts" => SettledMatrix.Layout.bits fixed stock reserved used

def checkNetwork (F : Type*) [Field F] (s : Fin (D.last+1)) :=
  routerNetwork (L).family (L).edge (L).routes counts ((L).nativeOrder enum)
    (fun _i=>(L).paths _) F s

/-- Evaluate on the very input and terminal words used in the funded report.
The reported equality matrix has no independently chosen local tables. -/
theorem check_eval (s : Fin (D.last+1))
    (x : State (B.actual.chordWidths fixed+(commodityGraph π place).chordWidths stock+
      (catalystGraph place).chordWidths (fun c=>reserved c-used c)) s)
    (z : State (installedWidths G.links.ends G.links.bits) s) :
    TypedWiring.value (checkNetwork (B:=B) (fixed:=fixed) (stock:=stock) (reserved:=reserved)
      (used:=used) inj pad enum F s)
      (Sum.elim (rowBits (L).family counts (cast (congrArg (fun U=>State U s) (H.old_width inj pad).symm) x))
        (rowBits (L).edge (routeLoad (L).routes counts)
          (cast (congrArg (fun U=>State U s) (H.new_width inj pad).symm) z))) =
      H.matrix inj pad enum s x z := by
  unfold checkNetwork matrix
  rw [rebase_apply]
  exact routerNetwork_eval ..

theorem check_cells :
    (∑ s : Fin (D.last+1),
      let net := checkNetwork (B:=B) (fixed:=fixed) (stock:=stock) (reserved:=reserved) (used:=used) inj pad enum F s
      net.cells+net.internal) =
      ∑ i,counts i*(((L).routes i).length+1) := routerNetwork_cells ..

end Hierarchy.ProbeStage.CoreBoard.MatrixReceipt

end
end OAI
