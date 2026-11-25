import OAI.ThreeFlat.Diagonal.HistoryAssembly
import OAI.ThreeFlat.Diagonal.HistoryRelabel

namespace OAI
/-! # Carry a physical cell assembly through a change of source chart -/

namespace ThreeFlat.Diagonal.HistoryRelabel

noncomputable section

open HistoryContraction

variable {F : Type} [CommSemiring F] {Pins : Type*} {X Y : Shape} (I : Iso X Y)

/-- Preserve each source cell's existing bit order across the index change. -/
def Iso.form (V : Form Y Pins) : Form X Pins where
  width i := V.width (I.site i)
  read i pin half := V.read (I.site i) pin ((I.half i).symm half)

def Iso.forest {V : Form Y Pins} (N : Forest F V) : Forest F (I.form V) := fun i => N (I.site i)

theorem Iso.form_values (V : Form Y Pins) (N : Forest F V) (pin : Pins) (i : X.Site) (a : X.Half i) :
    (I.form V).values (I.forest N) pin i a = V.values N pin (I.site i) ((I.half i).symm a) := rfl

private theorem widthEq (V : Form Y Pins) {G : Type} (owner : Y.Site → G) (v : G) (a : {j // owner j = v}) :
    V.width (I.site (((I.fiber owner v).symm a).val)) = V.width a.val :=
  congrArg (fun b : {j // owner j = v} => V.width b.val) ((I.fiber owner v).apply_symm_apply a)

private theorem read_at_equal (V : Form Y Pins) {G : Type} (owner : Y.Site → G) (v : G)
    (row : (j : {j // owner j = v}) → Y.Half j.val) (pin : Pins) {x y : {j // owner j = v}}
    (e : x=y) (k : Fin (V.width x.val)) :
    V.read y.val pin (row y) (Fin.cast (congrArg (fun z : {j // owner j = v} => V.width z.val) e) k) =
      V.read x.val pin (row x) k := by
  cases e
  rfl

private theorem rowAt (V : Form Y Pins) {G : Type} (owner : Y.Site → G) (v : G)
    (row : (j : {j // owner j = v}) → Y.Half j.val) (pin : Pins) (a : {j // owner j = v})
    (k : Fin ((I.form V).width (((I.fiber owner v).symm a).val))) :
    V.read a.val pin (row a) (Fin.cast (widthEq I V owner v a) k) =
      (I.form V).read (((I.fiber owner v).symm a).val) pin
        ((I.pushRow owner v).symm row ((I.fiber owner v).symm a)) k := by
  let z := (I.fiber owner v).symm a
  calc
    _ = V.read (I.site z.val) pin (row (I.fiber owner v z)) k :=
      read_at_equal V owner v row pin ((I.fiber owner v).apply_symm_apply a) k
    _ = _ := by
      change V.read (I.site z.val) pin (row (I.fiber owner v z)) k =
        V.read (I.site z.val) pin ((I.half z.val).symm
          ((I.half z.val) (row (I.fiber owner v z)))) k
      exact congrArg (fun h : Y.Half (I.site z.val) => V.read (I.site z.val) pin h k)
        ((I.half z.val).symm_apply_apply
          (show Y.Half (I.site z.val) from row (I.fiber owner v z))).symm

/-- One change of coordinates consumes no fresh descriptor row. It preserves
all child row ordinals, hidden bank offsets, root wiring, and external inputs. -/
def Iso.stage {R : Rewrite Y F} {t : Fin R.count} {V : Form Y Pins} {W : Form (R.target t) Pins}
    (L : Stage R t V W) : Stage (I.rewrite R) t (I.form V) W where
  count := L.count
  child v := (L.child v).trans (I.fiber (R.owner t) v).symm
  hidden := L.hidden
  decode v := (L.decode v).trans (I.pushRow (R.owner t) v).symm
  rootWidth := L.rootWidth
  root := L.root
  rootWire := L.rootWire
  childWire v j k := L.childWire v j (Fin.cast (widthEq I V _ v (L.child v j)) k)
  root_eq := by
    intro v g pin b
    change _ = R.kernel t v ((I.pushRow (R.owner t) v)
      ((I.pushRow (R.owner t) v).symm (L.decode v g))) b
    rw [Equiv.apply_symm_apply]
    exact L.root_eq v g pin b
  read_eq := by
    intro v j g pin b k
    exact (L.read_eq v j g pin b (Fin.cast (widthEq I V _ v _) k)).trans
      (rowAt I V (R.owner t) v (L.decode v g) pin (L.child v j) k)

end

end ThreeFlat.Diagonal.HistoryRelabel

end OAI
