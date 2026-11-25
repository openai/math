import OAI.Computability.NearSquareRoot.CRTTablePrefixProgram
import OAI.Computability.NearSquareRoot.SynchronizedPackedPorts

/-! # Little-endian physical positions of active MSF block-switch ports -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.FieldDirectory
open IntegerMultiplication Code

/-- Bit position in a little-endian record address. Blocks are listed with
the fastest first, while each local word is addressed in MSF order. -/
def position {d : ℕ} (w : Fin d → ℕ) (b : Fin d) (i : Fin (w b)) :=
  (∑ u : Fin b.val, w (Fin.castLE b.isLt.le u)) + (w b - 1 - i.val)

private def lower (q : List Tally × Tally) : Tally :=
  (cutLists (q.2,q.1)).1.flatten

/-- All natural address-bit positions of the selected block, in local MSF order. -/
def ports (q : List Tally × Tally) : List Tally :=
  polyPush (fun p : Tally × Tally => p.1 ++ p.2)
    (lower q,(Iter.lineup (Iter.pick [] q)).reverse)

theorem ports_poly : Poly ports := by
  have early : Easy lower := (easy_cut Easy.exchange).fstCompose.compose Easy.flatten
  have localBits := ((Iter.facile ([] : Tally)).poly.compose Iter.poly_line).rev
  exact (early.poly.pair localBits).compose
    (Poly.push [] [] (show Poly (fun p : Tally × Tally => p.1 ++ p.2) by fun_prop))

private theorem lower_eq {d : ℕ} (w : Fin d → ℕ) (b : Fin d) :
    (lower (List.ofFn fun j => tally (w j),tally b.val)).length =
      ∑ u : Fin b.val, w (Fin.castLE b.isLt.le u) := by
  let xs := List.ofFn fun j => tally (w j)
  have take : xs.take b.val = List.ofFn (fun u : Fin b.val => tally (w (Fin.castLE b.isLt.le u))) := by
    apply List.ext_getElem <;> simp [xs]
  change ((xs.take (tally b.val).length).flatten).length = _
  rw [tally_length,take]
  simp [List.length_flatten,List.map_ofFn,Function.comp_def,List.sum_ofFn]

theorem ports_eq {d : ℕ} (w : Fin d → ℕ) (b : Fin d) :
    ports (List.ofFn fun j => tally (w j),tally b.val) =
      List.ofFn (fun i => tally (position w b i)) := by
  simp only [ports, Iter.entry, Iter.lined,polyPush]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hl := lower_eq w b
    rw [List.getElem_map,List.getElem_reverse,List.getElem_ofFn,List.getElem_ofFn]
    rw [← recover_tally (lower (List.ofFn fun j => tally (w j),tally b.val) ++ _)]
    simp [position,hl]

abbrev Row := List Tally × List Tally

/-- Skip inactive blocks. Each active result gives the target followed by the
other positions needed to reconstruct its local control word. -/
def split (q : Tally × List Tally) : Row :=
  let parts := cutLists q
  let cut := cutLists (tally 1,parts.2)
  bif Iter.small q then (cut.1,parts.1 ++ cut.2) else ([],[])

theorem split_easy : Easy split := by
  let X := Tally × List Tally
  have pieces := easy_cut (Easy.identity (X := X))
  have one := easy_cut ((Easy.const (tally 1)).pair pieces.sndCompose)
  have select := one.fstCompose.pair (easy_append pieces.fstCompose one.sndCompose)
  exact Carry.condition _ _ _ (Iter.small_easy (X := Unit) (Y := Tally)) select (Easy.const ([],[]))

theorem split_active (l : List Tally) (j : ℕ) (hj : j < l.length) :
    split (tally j,l) = ([l[j]],l.take j ++ l.drop (j+1)) := by
  simp [split,Iter.small,hj,cutLists,List.take_one,List.head?_drop,List.drop_drop]

theorem split_inactive (l : List Tally) (j : ℕ) (hj : l.length ≤ j) :
    split (tally j,l) = ([],[]) := by simp [split,Iter.small,Nat.not_lt.mpr hj]

/-- Select arbitrary block numbers in their physical batch order. -/
def batch (q : (List Tally × Tally) × List Tally) : List Row :=
  polyPush split (q.1.2,polyPush ports (q.1.1,q.2))

theorem batch_poly : Poly batch := by
  let X := (List Tally × Tally) × List Tally
  have pp := (show Poly (fun x : X => (x.1.1,x.2)) by fun_prop).compose (Poly.push [] [] ports_poly)
  exact ((show Poly (fun x : X => x.1.2) by fun_prop).pair pp).compose (Poly.push [] [] split_easy.poly)

theorem batch_eq {d : ℕ} (w : Fin d → ℕ) (j : ℕ) (bs : List (Fin d)) :
    batch ((List.ofFn fun b => tally (w b),tally j),bs.map (fun b => tally b.val)) =
      bs.map (fun b => split (tally j,List.ofFn (fun i => tally (position w b i)))) := by
  simp [batch,polyPush,List.map_map,Function.comp_def,ports_eq]

theorem physicalPort {box : List (ℕ × ℕ)} {k L : ℕ} (hb : BoxShape.Valid k L box)
    [∀ i, NeZero (BoxFin.modulus box i)] (hd : 4 ≤ box.length) (v : Fin (2^k))
    (b : Fin (box.length/4)) (i : Fin (BoxFin.physicalWidth (box := box) b)) :
    (BoxFin.packedRecord hb hd v).2 b i =
      v.val.testBit (position (BoxFin.physicalWidth (box := box)) b i) :=
  BoxFin.packedRecord_port hb hd v b i

end Benes.FieldDirectory

end NearSquareRoot
end Computability
end OAI
