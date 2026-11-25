import OAI.Computability.IntegerMultiplication.Packed.Rep

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Strip Dims Loom Adic
-- general alternate weaving
variable {A B : Type} (v : Series A) (w : Series B)
abbrev oddcar (i) := Track (v.cart w) (i+1)
abbrev evencar (i) := v.cart ((Track (w.cart v) i).cart w)
variable {i : ℕ}
variable {G P : Tape} (g : Seal v G) (p : Seal w P)
private def joinS (q : Adopt v (layout G)) (t : Adopt w (layout P)) :
    Seal (v.cart w) (G++P) := (q.split t).thenDo (unite _ _)
-- odd→even by tail recursion
def weaveGrid : (i : ℕ) → Adopt (oddcar v w i) (evencar v w i)
| 0 =>
  let h := step (v.cart w) 0
  let e := ((Adopt.same (v.cart w)).split (park _ (G++P) (joinS v w g p) 0)).thenDo (Adopt.skip _)
  let f := (park _ (P++G) (joinS w v p g) 0).back
  (h.thenDo e).thenDo ((Adopt.same v).split
    ((Adopt.omitL w).back.thenDo (f.split (Adopt.same w))))
| i+1 =>
  -- (Av×Bw) × Odd(i), recurse→ A_i × B_l. then fold w × A_i into new Track
  let d := (Track (w.cart v) i).cart w
  let h := Adopt.rotate v w (v.cart d)
  let k := (Adopt.rotate w v d).back.thenDo
    ((Adopt.rotate (w.cart v) (Track (w.cart v) i) w).back.thenDo
      ((step (w.cart v) i).back.split (Adopt.same _)))
  ((step _ (i+1)).thenDo ((Adopt.same _).split (weaveGrid i))).thenDo
    (h.thenDo ((Adopt.same _).split k))
theorem begins (x : Fin (i+1) → A × B) :
    ((weaveGrid v w g p i).cast x).1=(x 0).1 := by
  cases i <;> rfl
theorem correspond (x : Fin (i+1) → A × B) (j : Fin i) :
    ((weaveGrid v w g p i).cast x).2.1 j = ((x j.castSucc).2, (x j.succ).1) := by
  induction i with
  | zero => exact j.elim0
  | succ i ih =>
    induction j using Fin.cases with
    | zero =>
      change Loom.join ((x 0).2 |> fun u => (u, ((weaveGrid v w g p i).cast (fun j => x j.succ)).1), _) 0=_
      rw [first_j,begins]; rfl
    | succ j =>
      change Loom.join (_,((weaveGrid v w g p i).cast (fun j => x j.succ)).2.1) j.succ=_
      rw [tail_j,ih]
      rfl
theorem tails (x : Fin (i+1) → A × B) :
    ((weaveGrid v w g p i).cast x).2.2 = (x (Fin.last i)).2 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change ((weaveGrid v w g p i).cast (fun j => x j.succ)).2.2=(x (Fin.last _)).2
    rw [ih]
    rfl

variable (H L : ℕ)
abbrev Queue (i : ℕ) := Top H × (Fin i→Seg L H) × Tail L
abbrev lineQ (i : ℕ) := evencar (dart H) (line 2 L) i
def baton (i : ℕ) : Adopt (oddcar (dart H) (line 2 L) i) (lineQ H L i) :=
  weaveGrid _ _ (flag H) (Adopt.same _) i

def package (i:ℕ) : Adopt (lineQ H L i) (line 2 ((i+1)*width H L)) :=
  let v := flag H
  let w := wound 2 (width H L) (segments H L) (furrow H L) i
  let g := (w.split (Adopt.same _)).thenDo (tile 2 (i*(width H L)) L)
  ((v.split g).thenDo (tile 2 _ _)).thenDo (castN _ _ _ (by unfold width; ring))
theorem packed (x : Queue H L i) :
    number ((package H L i).cast x)=
      2^(i*width H L+L)*number ((flag H).cast x.1)+
        (2^L*number ((wound 2 (width H L) (segments H L) (furrow H L) i).cast x.2.1)+number x.2.2) := by
  change number ((castN _ _ _ _).cast ((tile 2 (H+1) _).cast (_,(tile 2 _ _).cast (_,_)))) = _
  rw [castN_n,tile_n,tile_n]; rfl
theorem labels (x : Queue H L i) :
    most ((package H L i).cast x)=
      most ((flag H).cast x.1) ++ most ((wound 2 (width H L) (segments H L) (furrow H L) i).cast x.2.1) ++ most x.2.2 := by
  change most ((castN _ _ _ _).cast ((tile 2 (H+1) _).cast (_,(tile 2 _ _).cast (_,_)))) = _
  rw [castN_most,tile_most,tile_most,List.append_assoc]; rfl

end Packed

end IntegerMultiplication
end Computability
end OAI
