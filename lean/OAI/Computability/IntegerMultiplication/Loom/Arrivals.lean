import OAI.Computability.IntegerMultiplication.Loom.Shuttling
import OAI.Computability.IntegerMultiplication.Earlier

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Strip Dims Adic Port Code
variable {I : Type} {q : ℕ} [NeZero q] (hq : 2 ≤ q)
variable {r : Regime I} {l : I→ℕ}
structure Told (r : Regime I) (v : I→Tape) : Prop where
  solid i : Dims.solid (v i)
  shape : r.Has (Dims.shape ∘ v)
namespace Told
variable {s t : I→Tape}
theorem append (a : Told r s) (b : Told r t) :
    Told r (fun i => s i ++ t i) := by
  refine ⟨fun _ => (solid_cat ..).mpr ⟨a.solid _,b.solid _⟩,?_⟩
  have := (a.shape.pair b.shape).ez (Easy.append (X:=Tally)) -- binder?
  simpa [Function.comp_def,Dims.shape] using this
theorem nil : Told r (fun _ => []) :=
  ⟨fun _ _ h => False.elim (List.not_mem_nil h),Regime.fixed _⟩
theorem stacked (a : Told r s) (n : ℕ) : Told r (fun i => Rack (s i) n) := by
  induction n with
  | zero => exact Told.nil
  | succ n ih => exact a.append ih

include hq in
omit [NeZero q] in
theorem carrier (j : I→ℕ) (h : r.Has (tally ∘ j)) : Told r (fun i => field q (j i)) := by
  have eq (i : ℕ) : field q i = List.replicate i q := by
    induction i <;> simp_all [field,List.replicate_succ]
  refine ⟨?_,?_⟩
  · intro i n hn
    rw [eq] at hn
    have : n=q := List.eq_of_mem_replicate hn
    exact this ▸ hq
  have hv : (Dims.shape ∘ fun (i:I) => field q (j i)) =
      fun i => (tally (j i)).map (fun _ => tally q) := by
    funext i
    simp [Dims.shape,eq,tally]
  rw [hv]
  exact h.ez (show Easy (fun (k:Tally) => k.map fun _ => tally q) from by fun_prop)

theorem station (a : Told r s) : Station r (fun i => layout (s i)) := Station.tape a.solid a.shape

variable {J : Type} {n : ℕ} (f : J ≃ Fin n) {P G B d : I→Tape} (T_ : Told r d)
variable (a : Told r P) (b : Told r G) (c : Told r B)
include T_
include a b in
theorem stair (s : Spot J) :
    Told r (fun i => preamble f (P i) (G i) (d i) s) := by
  obtain ⟨_ | _,j⟩ := s
  · exact a.append (T_.stacked _)
  exact a.append ((T_.stacked n).append (b.append (T_.stacked _)))
include c b in
theorem lounge (s : Spot J) :
    Told r (fun i => appendix f (G i) (B i) (d i) s) := by
  obtain ⟨_ | _,j⟩ := s
  · exact (T_.stacked _).append (b.append ((T_.stacked n).append c))
  exact (T_.stacked _).append c
include b in
theorem corridor (s v : Spot J) :
    Told r (fun i => silence f (G i) (d i) s v) := by
  obtain ⟨_ | _,i⟩ := s <;> obtain ⟨_ | _,j⟩ := v
  · exact T_.stacked _
  · exact (T_.stacked _).append (b.append (T_.stacked _))
  · exact (T_.stacked _).append (b.append (T_.stacked _))
  exact T_.stacked _
end Told

variable (j : I→ℕ) {A : I→Type} {a : (i:I)→Series (A i)}
variable {P G B : I→Tape}
include hq

theorem sizeUp (e : ∀ i,Slot (a i) (P i) (line q (j i)) (B i)) (s : Span q)
    (hj : r.Has (tally ∘ j)) (p : Told r P) (b : Told r B)
    (v : (i:I)→A i→Tree) (h : Manifest A l v) :
    Fleet r l a a v (fun i => v i ∘ ((e i).tune (sweep s (j i))).symm) := by
  let t i := line q (j i)
  let d := fun i => (e i).view
  let shape i := Board (P i) (t i) (B i)
  let w (i:I) := v i ∘ (d i).cast.symm
  have m := h.shift (fun i => ((d i).cast.symm : _ → _))
  change Manifest _ l w at m
  let u (i:I) (z : Pin (P i) × Block q (j i) × Pin (B i)) :=
    w i (z.1,(sweep s (j i)).symm z.2.1,z.2.2)
  let X := Sigma (fun i => Pin (P i))
  have k := within (r:=r.pull (Sigma.fst : X → I)) (l:=l ∘ Sigma.fst) hq (j ∘ (Sigma.fst : X → I)) (Task.BT.map hj (Sigma.fst : X → I) : Regime.Has (r.pull (Sigma.fst : X → I)) _)
    (b.station.pull _) (fun (x:X) y => w x.1 (x.2,y)) (Manifest.localize (s:=fun (x:I) c y => w x (c,y)) m) s
  have z : Fleet r l shape shape w u := Fleet.wind p.station ((terminal hq j hj).product b.station) m k
  have huv : u = (fun i => ((v i ∘ ((e i).tune (sweep s (j i))).symm)) ∘ (d i).cast.symm) := by
    funext i x
    obtain ⟨x,y,b⟩ := x
    change v i _ = v i _
    congr 1
    simp [Slot.tune, Slot.alter,Slot.read,d] -- inside x → ?
  exact Fleet.align v _ d d (huv ▸ z)

/-- translation of the later element in a pair, controlled by the first -/
def slideOver {X Y : Type} (k : X→Y≃Y) : (X × Y) ≃ X × Y where
  toFun v := (v.1,k v.1 v.2)
  invFun v := (v.1,(k v.1).symm v.2)
  left_inv := by rintro ⟨a,b⟩; simp
  right_inv := by rintro ⟨a,b⟩; simp

theorem shiftUp (e : ∀ i,Axis (a i) (P i) (line q (j i)) (G i) (line q (j i)) (B i))
    (s : Pinpoint q) (hj : r.Has (tally ∘ j)) (p : Told r P) (g : Told r G) (b : Told r B)
    (v : (i:I)→A i→Tree) (h : Manifest A l v) :
    Fleet r l a a v (fun i => v i ∘ ((e i).tune
      (slideOver (fun x => glide (s.stamp (j i) * index q (j i) x)))).symm) := by
  let t i := line q (j i)
  let d := fun i => (e i).view
  let sh i := Path (P i) (t i) (G i) (t i) (B i)
  let w (i:I) := v i ∘ (d i).cast.symm
  have m := h.shift (fun i => ((d i).cast.symm : _ → _))
  change Manifest _ l w at m
  let u (i:I)
      (z : Pin (P i) × Block q (j i) × Pin (G i) × Block q (j i) × Pin (B i)) :=
    w i (z.1,z.2.1,z.2.2.1,(glide (s.stamp (j i) * index q (j i) z.2.1)).symm z.2.2.2.1,z.2.2.2.2)
  let X := Sigma (fun i => Pin (P i))
  have k := Adic.along (r:=r.pull (Sigma.fst : X → I)) (l:=l ∘ Sigma.fst) hq (j ∘ (Sigma.fst : X → I)) (Task.BT.map hj (Sigma.fst : X → I) : Regime.Has (r.pull (Sigma.fst : X → I)) _)
    (g.station.pull _) (b.station.pull _) (fun (x:X) y => w x.1 (x.2,y))
    (Manifest.localize (s:=fun (x:I) c y => w x (c,y)) m) s
  have vl := terminal hq j hj
  have z : Fleet r l sh sh w u := Fleet.wind p.station (vl.product (g.station.product (vl.product b.station))) m k
  have huv : u = (fun i => ((v i ∘ ((e i).tune
      (slideOver (fun x => glide (s.stamp (j i) * index q (j i) x)))).symm)) ∘ (d i).cast.symm) := by
    funext i x
    obtain ⟨x,y,g,t,b⟩ := x
    change v i _ = v i _
    congr 1
    simp [Axis.tune,Axis.bridge,Axis.pair,slideOver,d]
  exact Fleet.align v _ d d (huv ▸ z)

end Loom

end IntegerMultiplication
end Computability
end OAI
