import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly

namespace OAI
/-! # Transporting physical word and pin layouts across equal history shapes -/

namespace ThreeFlat.Diagonal.HistoryContraction.WordLayout
open LinearAlgebra.SpectralBooks
open scoped Classical BigOperators

private theorem label_at {S T : Shape} (e : S=T) (i : S.Edge) :
    S.Label i = T.Label (cast (congrArg Shape.Edge e) i) := by
  cases e
  rfl

theorem width_injective {V E : Type} [Fintype V] [Fintype E] (graph : PortGraph V E)
    {first second : E → ℕ} (same : shape graph first = shape graph second) : first=second := by
  funext i
  have labels : Fin (2^first i) = Fin (2^second i) := label_at same i
  have sizes := Fintype.card_congr (Equiv.cast labels)
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  simpa only [Fintype.card_fin] using sizes

def atWidth {V E Pins : Type} [Fintype V] [Fintype E] {graph : PortGraph V E}
    {second : E → ℕ} (first : E → ℕ) (fresh : WordLayout graph second Pins) :
    WordLayout graph first Pins :=
  ⟨fresh.count,fresh.order,fresh.ext,fresh.pin⟩

theorem inheritedWidth_eq {V E U A Pins : Type} [Fintype V] [Fintype E] [Fintype U] [Fintype A]
    {oldGraph : PortGraph V E} {oldWidth : E → ℕ} (old : WordLayout oldGraph oldWidth Pins)
    {graph : PortGraph U A} {first second : A → ℕ} (same : shape graph first = shape graph second)
    (fresh : WordLayout graph second Pins) (owner : V → U) (num : U → ℕ)
    (child : ∀ j,Fin (num j) ≃ {i // owner i=j}) :
    (same.symm ▸ (old.inherited fresh owner num child).ports.form : Form (shape graph first) Pins) =
      (old.inherited (atWidth first fresh) owner num child).ports.form := by
  have widths := width_injective graph same
  subst second
  rfl

end ThreeFlat.Diagonal.HistoryContraction.WordLayout

namespace ThreeFlat.Diagonal.HistoryContraction

/-- Change the output form while retaining the literal kernel, child order
and decoding map of the stage. Only the destination widths of its wires change type. -/
def Stage.reform {F Pins : Type*} [CommSemiring F] {S : Shape} {R : Rewrite S F}
    {t : Fin R.count} {V : Form S Pins} {a b : Form (R.target t) Pins}
    (stage : Stage R t V a) (same : a=b) : Stage R t V b where
  count := stage.count
  child := stage.child
  hidden := stage.hidden
  decode := stage.decode
  rootWidth := stage.rootWidth
  root := stage.root
  rootWire v k := cast (congrArg (fun f : Form (R.target t) Pins => BitSource (stage.hidden v) (f.width v)) same)
    (stage.rootWire v k)
  childWire v j k := cast (congrArg (fun f : Form (R.target t) Pins => BitSource (stage.hidden v) (f.width v)) same)
    (stage.childWire v j k)
  root_eq := by cases same; exact stage.root_eq
  read_eq := by cases same; exact stage.read_eq

end ThreeFlat.Diagonal.HistoryContraction

end OAI
