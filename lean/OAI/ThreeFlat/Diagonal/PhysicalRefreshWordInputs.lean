import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly
import OAI.ThreeFlat.Diagonal.PhysicalStageRefresh
import OAI.ThreeFlat.Diagonal.RefreshStageAssembly
import OAI.ThreeFlat.Diagonal.CompressorHalfPorts

namespace OAI
/-! # Ordered physical refresh words and the origin of each inherited bit -/

namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction
open scoped Classical BigOperators
noncomputable section

set_option pp.maxSteps 1200
set_option maxHeartbeats 130000

/-- Outgoing slots precede incoming slots at the vertex in the state's own chart. -/
def State.halfWords {d l : ℕ} (A : State d l) (Pins : Type) : A.Words Pins where
  count _ := 2*d
  order v := (Native.ShrinkStage.Halves.portOrder A.graph A.chart (A.chart.symm v)).trans
    (Equiv.cast (congrArg A.shape.graph.Port (A.chart.apply_symm_apply v)))
  ext _ := 0
  pin _ _ := Fin.elim0

private theorem portCast_val {d l : ℕ} (X : State d l) {z z' : X.Site} (h : z=z') (p : X.shape.graph.Port z) :
    (cast (congrArg X.shape.graph.Port h) p).val=p.val := by cases h;rfl

theorem State.halfWords_ordered {d l : ℕ} (X : State d l) (Pins : Type) : X.OrderedHalves (X.halfWords Pins) := by
  refine ⟨fun _=>rfl,?_⟩
  intro z i
  change (cast (congrArg X.shape.graph.Port (X.chart.apply_symm_apply z))
    (Native.ShrinkStage.Halves.portOrder X.graph X.chart (X.chart.symm z) i)).val.1=_
  have hv := portCast_val X (X.chart.apply_symm_apply z)
    (Native.ShrinkStage.Halves.portOrder X.graph X.chart (X.chart.symm z) i)
  exact (congrArg Prod.fst hv).trans (congrArg Prod.fst
    (Native.ShrinkStage.Halves.portOrder_value X.graph X.chart (X.chart.symm z) i))

variable {F Pins : Type} [Field F] {m lanes hbits rem h pad : ℕ} {c : Fin m→Fin m→ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State m lanes)
  (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
  (hm : 2 ≤ m) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Bound (transition c h) ℝ γ)

set_option quotPrecheck false

local notation "physMove" => refreshMove T A u port hm hh sym rows zero conn
local notation "inIso" => StageAddress.refreshInputIso A.graph A.chart u port A.width

attribute [local irreducible] CompressorRefresh.graph RefreshTies.freshWidth

section
variable (L : A.Words Pins) (idx : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count)

def refreshWords : ((physMove).next idx).Words Pins :=
  ((inIso).pushWord L).inherited (((physMove).next idx).halfWords Pins) id (fun _ => 1) RefreshTies.singleChild

set_option maxHeartbeats 180000 in
theorem refreshWords_ordered : ((physMove).next idx).OrderedHalves
    (refreshWords T A u port hm hh sym rows zero conn L idx) := by
  have o := ((physMove).next idx).halfWords_ordered Pins
  exact ⟨o.count,o.edge⟩

abbrev OriginFor {d l D n : ℕ} {A : State d l} (move : Move F A D n)
    (i : Fin move.rules.count) (source : A.Words Pins) (target : (move.next i).Words Pins) :=
  ∀ z, Fin (target.ext z) → Σ s : {a // move.parent i a=z}, Fin (source.ext s.val)

abbrev StageFor {d l D n : ℕ} {A : State d l} (move : Move F A D n)
    (i : Fin move.rules.count) (source : A.Words Pins) (target : (move.next i).Words Pins) :=
  Stage move.rules i source.ports.form ((move.target_eq i).symm ▸ target.ports.form)

def fromChild {B U : Type} (chart : B ≃ U) (owner : B → U)
    (parent : ∀ b, owner b = chart b) (ext : B → ℕ) (z : U)
    (j : Fin (∑ i : Fin 1, ext (chart.symm (RefreshTies.singleChild z i).val))) :
    Σ s : {b // owner b=z}, Fin (ext s.val) := by
  let piece : (i : Fin 1) × Fin (ext (chart.symm (RefreshTies.singleChild z i).val)) :=
    finSigmaFinEquiv.symm j
  let child := RefreshTies.singleChild z piece.1
  exact ⟨⟨chart.symm child.val,(parent _).trans ((chart.apply_symm_apply child.val).trans child.property)⟩,piece.2⟩

theorem fromChild_order {B U : Type} (chart : B ≃ U) (owner : B → U)
    (parent : ∀ b, owner b = chart b) (ext : B → ℕ) (z : U)
    (count : ℕ) (pick : Fin count → B) (one : count=1) (picked : ∀ k,pick k=chart.symm z) :
    let size := ∑ i : Fin 1, ext (chart.symm (RefreshTies.singleChild z i).val)
    ∃ eqn : size=∑ i,ext (pick i), ∀ j : Fin size,
      let p : (k : Fin count) × Fin (ext (pick k)) := finSigmaFinEquiv.symm (j.cast eqn)
      ((fromChild chart owner parent ext z j).1.val,(fromChild chart owner parent ext z j).2.val)=
        (pick p.1,p.2.val) := by
  subst count
  have choose : pick = (fun k : Fin 1 => chart.symm (RefreshTies.singleChild z k).val) := by
    funext k
    exact picked k
  subst pick
  exact ⟨rfl,fun _ => rfl⟩

private theorem castAtSite {U : Type} (h : U=U) (z : U) : cast h z=z := rfl

open private refreshRules from OAI.ThreeFlat.Diagonal.PhysicalStageRefresh in
private theorem refreshRulesOwner (s : A.Site) : (physMove).rules.owner idx s = (inIso).site s := by
  dsimp only [refreshMove,refreshRules,HistoryRelabel.Iso.rewrite,RefreshMotif.Table.step,
    RefreshTies.histogramStep,RefreshTies.slotRewrite,RefreshTies.refreshRewrite,Function.comp_apply,id_eq]; rfl

set_option maxHeartbeats 270000 in
theorem refreshParent (s : A.Site) : (physMove).parent idx s = (inIso).site s := by
  unfold Move.parent
  exact (@castAtSite ((A.Base × BitWord rem) × Fin m)
    (congrArg Shape.Site ((physMove).target_eq idx)) ((physMove).rules.owner idx s)).trans
    (refreshRulesOwner T A u port hm hh sym rows zero conn idx s)

def refreshOrigin : OriginFor (physMove) idx L
    (refreshWords T A u port hm hh sym rows zero conn L idx) :=
  fromChild (inIso).site ((physMove).parent idx)
    (refreshParent T A u port hm hh sym rows zero conn idx) L.ext

end

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
