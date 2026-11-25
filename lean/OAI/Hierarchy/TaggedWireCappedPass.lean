import OAI.Hierarchy.TaggedWireStockOrdinals
import OAI.Hierarchy.TaggedWireChargedPass

namespace OAI
/-! # One signed packet substitution through the actual subsequent cap and spill -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe ProtocolRAM Calendar WireTelescope
open scoped Classical BigOperators

variable {h d k S g edges r : ℕ} {A F : Type*} [Field F] [Fintype A]
    {sampler : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin S}
    (B : Mount (S:=sampler) π place edges) (inj : Function.Injective place) (pad : Chord S)
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
    {I : Type} [Fintype I] (order : Data h d k≃Fin g)
    (K : PortGraph (Fin S) I) (reserve : I→ℕ) (carry : Widths S)
    (archive : A→Widths S) (amount : A→Fin g→ℕ) (T : A→Transfer h d k)
    (active : ∀c i,(T c).active i=amount c (order i)) (pending : ∀c i,(T c).old i=0)

local notation "G" => ordinalGoods π place order
local notation "post" c => carry+archive c+(G).chordWidths (amount c)+K.chordWidths reserve
local notation "staticStock" c => carry+archive c+K.chordWidths reserve

include active pending in
omit [Fintype A] in
private theorem cap_input (c : A) :
    input (π:=π) (place:=place) (staticStock c) (T c)=post c := by
  have one : (T c).old=fun _=>0:=funext (pending c)
  have two : (T c).active=amount c ∘ order:=funext (active c)
  unfold input
  rw [one,two,chordWidths_empty,←ordinalGoods_width π place order (amount c)]
  abel

def cappedPass {start : Widths S} (packets : ∀c,SiteMatrix (State start) (State (post c)) F) (c : A) :
    SiteMatrix (State start) (State (output B (staticStock c) (T c))) F :=
  SiteMatrix.compose (packets c) (rebase (cap_input order K reserve carry archive amount T active pending c) rfl
    (matrix B inj pad enum (staticStock c) (T c)))

theorem cappedPass_action {start : Widths S} (packets : ∀c,SiteMatrix (State start) (State (post c)) F)
    (signed : ∀x,(raw F start).coeff x=∑c,SiteMatrix.act (packets c) (raw F (post c)).coeff x)
    (x : ∀s,State start s) :
    (raw F start).coeff x=∑c,SiteMatrix.act
      (cappedPass B inj pad enum order K reserve carry archive amount T active pending packets c)
      (raw F (output B (staticStock c) (T c))).coeff x := by
  refine (signed x).trans (Finset.sum_congr rfl ?_)
  intro c _
  let actual := matrix (F := F) B inj pad enum (staticStock c) (T c)
  let same := cap_input (π := π) (place := place) order K reserve carry archive amount T active pending c
  let step : SiteMatrix (State (post c)) (State (output B (staticStock c) (T c))) F :=
    rebase same rfl actual
  have coeff : (raw F (post c)).coeff =
      SiteMatrix.act step (raw F (output B (staticStock c) (T c))).coeff :=
    funext (rebase_action same rfl actual (action B inj pad enum (staticStock c) (T c)))
  exact (congrArg (fun f => SiteMatrix.act (packets c) f x) coeff).trans
    (SiteMatrix.act_compose (packets c) step (raw F (output B (staticStock c) (T c))).coeff x)

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer

end
end OAI
