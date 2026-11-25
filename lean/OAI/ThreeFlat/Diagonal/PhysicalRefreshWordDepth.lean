import OAI.ThreeFlat.Diagonal.HistoryAssemblyDepth
import OAI.ThreeFlat.Diagonal.PhysicalShrinkWordDepth
import OAI.ThreeFlat.Diagonal.PhysicalRefreshWords
import OAI.ThreeFlat.Diagonal.PhysicalRefreshWordPrice

namespace OAI
/-! # Depth of each elected root of the numbered refresh move -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression HistoryContraction
open scoped Classical BigOperators
noncomputable section

open private rootWithin from OAI.ThreeFlat.Diagonal.PhysicalShrinkWordDepth

variable {F Pins : Type} [Field F]

open private assembleWords WordRead WordOrder refreshWordRead refreshWordOriginOrder
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshWords

private theorem assembled_within {d l D n : ℕ} {X : State d l} (move : Move F X D n)
    (i : Fin move.rules.count) (source : X.Words Pins) (target : (move.next i).Words Pins)
    (stage : StageFor move i source target) (halves : (move.next i).OrderedHalves target)
    (origin : OriginFor move i source target) (read : WordRead move i source target origin)
    (order : WordOrder move i source target stage origin) (z : (move.rules.target i).Site)
    (bound : Tree.Within 3 (stage.root z)) :
    let step := assembleWords move i source target stage halves origin read order
    Tree.Within 4 (step.stage.root z) :=
  bound.mono (by decide : 3≤4)

section
variable {m lanes hbits rem h pad : ℕ} {c : Fin m→Fin m→ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State m lanes)
  (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
  (hm : 2 ≤ m) (hh : 0 < h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ)

local notation "move" => refreshMove T A u port hm hh sym rows zero conn

set_option maxRecDepth 3200 in
set_option maxHeartbeats 180000 in
private theorem refreshMove_root_within :
    rootWithin (R:=move) (refreshMove_assembler (Pins:=Pins) T A u port hm hh sym rows zero conn) :=
  fun L i z => assembled_within (F:=F) (Pins:=Pins) (X:=A) move i L
    (refreshWords T A u port hm hh sym rows zero conn L i)
    (refreshWordStage T A u port hm hh sym rows zero conn L i)
    (refreshWords_ordered T A u port hm hh sym rows zero conn L i)
    (refreshOrigin T A u port hm hh sym rows zero conn L i)
    (refreshWordRead T A u port hm hh sym rows zero conn L i)
    (refreshWordOriginOrder T A u port hm hh sym rows zero conn L i)
    z (refreshWordStage_within T A u port hm hh sym rows zero conn L i z)
end

set_option maxRecDepth 3200 in
set_option maxHeartbeats 100000 in
theorem refreshBinary_root_within {s r a p : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+a+p) C) (A : State (2^s) (s+r))
    (hm : 2≤2^s) (hh : 0<a) (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=a)
    (zero : ∀ i, c i i=0) (conn : Expander.Bound (Expander.transition c a) ℝ γ) :
    rootWithin (R:=refreshBinary T A hm hh sym rows zero conn)
      (refreshBinary_assembler (Pins:=Pins) T A hm hh sym rows zero conn) :=
  refreshMove_root_within T A (CompressorPacking.splitWord s r) (CompressorPacking.Native.tagOrdinal s).symm
    hm hh sym rows zero conn


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
