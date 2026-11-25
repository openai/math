import OAI.ThreeFlat.Diagonal.PhysicalRefreshWordStage
import OAI.ThreeFlat.Diagonal.PhysicalStageBinary

namespace OAI
/-! # Word assembly for a single physical refresh -/

namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction
open scoped Classical BigOperators
noncomputable section

set_option pp.maxSteps 1200
set_option maxHeartbeats 130000

variable {F Pins : Type} [Field F] {m lanes hbits rem h pad : ℕ} {c : Fin m→Fin m→ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State m lanes)
  (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
  (hm : 2 ≤ m) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Bound (transition c h) ℝ γ)

set_option quotPrecheck false

local notation "physMove" => refreshMove T A u port hm hh sym rows zero conn
local notation "inIso" => StageAddress.refreshInputIso A.graph A.chart u port A.width

private theorem inverseSiteCast {U : Type} (same : U = U) (v : U) :
    (Equiv.cast same).symm v = v := rfl

private abbrev WordRead {d l D n : ℕ} {X : State d l} (move : Move F X D n)
    (i : Fin move.rules.count) (source : X.Words Pins) (target : (move.next i).Words Pins)
    (origin : OriginFor move i source target) : Prop :=
  ∀ z j pin, target.pin z pin j = source.pin (origin z j).1.val pin (origin z j).2

private abbrev WordOrder {d l D n : ℕ} {X : State d l} (move : Move F X D n)
    (i : Fin move.rules.count) (source : X.Words Pins) (target : (move.next i).Words Pins)
    (stage : StageFor move i source target) (origin : OriginFor move i source target) : Prop :=
  ∀ v,
    let z := (Equiv.cast (congrArg Shape.Site (move.target_eq i))).symm v
    let size := fun k : Fin (stage.count z) => source.ext (stage.child z k).val
    ∃ eqn : target.ext v = ∑ k, size k, ∀ j : Fin (target.ext v),
      let piece : Σ k, Fin (size k) := finSigmaFinEquiv.symm (j.cast eqn)
      ((origin v j).1.val, (origin v j).2.val) = ((stage.child z piece.1).val, piece.2.val)

/-- Assemble the issued stage from its words, owner coordinates and the native
equalities for reading and ordering the concatenated child inputs. -/
private def assembleWords {d l D n : ℕ} {X : State d l} (move : Move F X D n)
    (i : Fin move.rules.count) (source : X.Words Pins) (target : (move.next i).Words Pins)
    (stage : StageFor move i source target) (halves : (move.next i).OrderedHalves target)
    (origin : OriginFor move i source target) (read : WordRead move i source target origin)
    (order : WordOrder move i source target stage origin) : move.WordStep Pins source i :=
  ⟨target, stage, halves, origin, read, order⟩

set_option maxHeartbeats 95000 in
private theorem refreshWordRead (L : A.Words Pins) (idx : Fin (physMove).rules.count) :
    WordRead (physMove) idx L (refreshWords T A u port hm hh sym rows zero conn L idx)
      (refreshOrigin T A u port hm hh sym rows zero conn L idx) :=
  fun _ _ _ => rfl

/-- The stage records the original parent in the chart used for the new words. -/
private theorem originStageChild (L : A.Words Pins) (idx : Fin (physMove).rules.count)
    (v : ((physMove).next idx).Site)
    (k : Fin ((refreshWordStage T A u port hm hh sym rows zero conn L idx).count
      ((Equiv.cast (congrArg Shape.Site ((physMove).target_eq idx))).symm v))) :
    ((refreshWordStage T A u port hm hh sym rows zero conn L idx).child
      ((Equiv.cast (congrArg Shape.Site ((physMove).target_eq idx))).symm v) k).val =
      (inIso).site.symm v :=
  (refreshWordChild T A u port hm hh sym rows zero conn L idx _ k).trans
    (congrArg (inIso).site.symm
      (@inverseSiteCast ((A.Base × BitWord rem) × Fin m)
        (congrArg Shape.Site ((physMove).target_eq idx)) v))

/-- Read the flat pin ordinal through its one actual physical predecessor. -/
private theorem refreshWordOriginOrder (L : A.Words Pins) (idx : Fin (physMove).rules.count) :
    WordOrder (physMove) idx L (refreshWords T A u port hm hh sym rows zero conn L idx)
      (refreshWordStage T A u port hm hh sym rows zero conn L idx)
      (refreshOrigin T A u port hm hh sym rows zero conn L idx) := by
  intro v
  exact fromChild_order (inIso).site ((physMove).parent idx)
    (refreshParent T A u port hm hh sym rows zero conn idx) L.ext v
    _ (fun k => ((refreshWordStage T A u port hm hh sym rows zero conn L idx).child
      ((Equiv.cast (congrArg Shape.Site ((physMove).target_eq idx))).symm v) k).val)
    (refreshWordCount T A u port hm hh sym rows zero conn L idx _)
    (originStageChild T A u port hm hh sym rows zero conn L idx v)

set_option maxRecDepth 2800 in
set_option maxHeartbeats 150000 in
def refreshMove_assembler : (physMove).Assembler Pins :=
  fun L idx => assembleWords (F := F) (Pins := Pins) (X := A) (physMove) idx L
    (refreshWords T A u port hm hh sym rows zero conn L idx)
    (refreshWordStage T A u port hm hh sym rows zero conn L idx)
    (refreshWords_ordered T A u port hm hh sym rows zero conn L idx)
    (refreshOrigin T A u port hm hh sym rows zero conn L idx)
    (refreshWordRead T A u port hm hh sym rows zero conn L idx)
    (refreshWordOriginOrder T A u port hm hh sym rows zero conn L idx)

theorem refreshMove_stageCount (L : A.Words Pins)
    (idx : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count)
    (z : ((physMove).rules.target idx).Site) :
    (refreshMove_assembler T A u port hm hh sym rows zero conn L idx).stage.count z=1 :=
  refreshWordCount T A u port hm hh sym rows zero conn L idx z

theorem refreshMove_stageChild (L : A.Words Pins)
    (idx : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count)
    (z : ((physMove).rules.target idx).Site)
    (k : Fin ((refreshMove_assembler T A u port hm hh sym rows zero conn L idx).stage.count z)) :
    ((refreshMove_assembler T A u port hm hh sym rows zero conn L idx).stage.child z k).val =
      (StageAddress.refreshInputIso A.graph A.chart u port A.width).site.symm z :=
  refreshWordChild T A u port hm hh sym rows zero conn L idx z k

def refreshBinary_assembler {s rem h pad : ℕ} {c : Fin (2^s)→Fin (2^s)→ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
    (zero : ∀ i,c i i=0) (conn : Bound (transition c h) ℝ γ) :
    (refreshBinary T A hm hh sym rows zero conn).Assembler Pins :=
  refreshMove_assembler T A (splitWord s rem) (Native.tagOrdinal s).symm hm hh sym rows zero conn

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
