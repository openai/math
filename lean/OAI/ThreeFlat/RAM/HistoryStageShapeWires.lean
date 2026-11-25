import OAI.ThreeFlat.RAM.HistoryPortMap
import OAI.ThreeFlat.Diagonal.HistoryWordLayout
import OAI.ThreeFlat.Diagonal.HistoryPostorder

namespace OAI
/-! # Numeric kernel and old-child addresses of an individual ordered stage -/

namespace ThreeFlat.RAM.HistoryStageShapeWires

open Diagonal.HistoryContraction BitLayout
open scoped BigOperators Classical
noncomputable section
variable {F Pins : Type} [CommSemiring F] {S : Shape} {R : Rewrite S F} {t : Fin R.count}
  (L : PortLayout S Pins) {W : Form (R.target t) Pins} (s : Stage R t L.form W) (v : (R.target t).Site)

/-- The half banks and external prefix of a joined cell in its actual source
chart. These equations only observe numerical ordinals of the wires. -/
structure At (external : ℕ) : Prop where
  hidden : s.hidden v=∑ i,L.halfBits (s.child v i).val
  root : ∀ j,sourceAddress (s.rootWire v j)=HistoryPortMap.piecewise j.val
    (s.hidden v) (2+W.width v) (2+external)
  child : ∀ i j,sourceAddress (s.childWire v i j)=HistoryPortMap.piecewise j.val
    (L.ext (s.child v i).val) (2+Tree.before (fun z=>L.ext (s.child v z).val) i)
    (2+W.width v+Tree.before (fun z=>L.halfBits (s.child v z).val) i)

variable (V : PortLayout (R.target t) Pins) (count : (R.target t).Site→ℕ)
  (order : ∀ v,Fin (count v)≃{u // R.owner t u=v}) (root : ∀ v,Tree F (L.hidden count order v+V.halfBits v))
  (ok : ∀ v (pin : Fin (L.hidden count order v+V.halfBits v)→Bool) x y,
    (∀ i a j,pin (L.stageOld V count order v i a j)=L.binary a.1.1 (x i a) j) →
    (∀ a j,pin (L.stageNew V count order v a j)=V.binary a.1.1 (y a) j) →
    (root v).compile.eval pin=R.kernel t v x y)

theorem wordsStage_at (v : (R.target t).Site) :
    At L (L.wordsStage V count order root ok) v ((L.inherit V count order).ext v) :=
  ⟨rfl,HistoryPortMap.kernel_map L (L.inherit V count order) count order v,
    HistoryPortMap.child_map L V count order v⟩

end
end ThreeFlat.RAM.HistoryStageShapeWires

end OAI
