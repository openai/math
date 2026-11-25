import OAI.Hierarchy.ProbeFixedNeighbors

namespace OAI
/-! # The ordered input and output sockets occupied by each record of a routed fabric -/
namespace Hierarchy.ProbeStage
noncomputable section

def mapSocketPair {C D : Type*} (g : C → D) (z : C × C) : D × D := (g z.1,g z.2)

def Routes.socketPairs {R : Type} : {X Y : Type} → {f : Fabric X Y} →
    {x : R ↪ X} → {y : R ↪ Y} → Routes R f x y → R → List (f.Column × f.Column)
  | _,_,.step s,x,y,_,p => [(.inl (s.source (x p)),.inr (s.target (y p)))]
  | _,_,.seq a b,_,_,r,p => ((socketPairs (f:=a) r.2.1 p).map (mapSocketPair Sum.inl)) ++
    ((socketPairs (f:=b) r.2.2 p).map (mapSocketPair Sum.inr))

theorem Routes.socketPairs_length {R X Y : Type} {f : Fabric X Y} {x : R ↪ X} {y : R ↪ Y}
    (r : Routes R f x y) (p : R) : (r.socketPairs p).length=f.shapes.length := by
  induction f with
  | step s => rfl
  | seq a b ia ib =>
    change ((r.2.1.socketPairs p).map (mapSocketPair Sum.inl) ++
      (r.2.2.socketPairs p).map (mapSocketPair Sum.inr)).length=(a.shapes++b.shapes).length
    rw [List.length_append,List.length_append,List.length_map,List.length_map,ia r.2.1,ib r.2.2]

structure SocketSequence {C : Type*} (edge : C → C → Prop) (start finish : C) (xs : List (C × C)) : Prop where
  nonempty : 0 < xs.length
  first : ∀ z, xs[0]?=some z → z.1=start
  last : ∀ i z, i+1=xs.length → xs[i]?=some z → z.2=finish
  adjacent : ∀ i z v, xs[i]?=some z → xs[i+1]?=some v → edge z.2 v.1

private theorem SocketSequence.lift {C D : Type*} {edge : C → C → Prop} {dest : D → D → Prop}
    {u v : C} {xs : List (C × C)} (a : SocketSequence edge u v xs) (g : C → D)
    (keep : ∀ x y,edge x y → dest (g x) (g y)) :
    SocketSequence dest (g u) (g v) (xs.map (mapSocketPair g)) where
  nonempty := by simpa only [List.length_map] using a.nonempty
  first z hit := by
    rw [List.getElem?_map] at hit
    obtain ⟨z',found,rfl⟩:=Option.map_eq_some_iff.mp hit
    exact congrArg g (a.first z' found)
  last i z last hit := by
    rw [List.getElem?_map] at hit
    obtain ⟨z',found,rfl⟩:=Option.map_eq_some_iff.mp hit
    exact congrArg g (a.last i z' (by simpa only [List.length_map] using last) found)
  adjacent i z v hz hv := by
    rw [List.getElem?_map] at hz hv
    obtain ⟨z',foundZ,rfl⟩:=Option.map_eq_some_iff.mp hz
    obtain ⟨v',foundV,rfl⟩:=Option.map_eq_some_iff.mp hv
    exact keep _ _ (a.adjacent i z' v' foundZ foundV)

private theorem SocketSequence.join {C : Type*} {edge : C → C → Prop} {u v x y : C}
    {xs ys : List (C × C)} (a : SocketSequence edge u v xs) (b : SocketSequence edge x y ys)
    (link : edge v x) : SocketSequence edge u y (xs++ys) where
  nonempty := by have:=a.nonempty;simp only [List.length_append];omega
  first z hz := by rw [List.getElem?_append_left a.nonempty] at hz;exact a.first _ hz
  last i z last hz := by
    rw [List.length_append] at last
    have:=b.nonempty
    rw [List.getElem?_append_right (by omega)] at hz
    exact b.last _ _ (by omega) hz
  adjacent i z v hz hv := by
    by_cases left : i+1<xs.length
    · rw [List.getElem?_append_left (by omega)] at hz
      rw [List.getElem?_append_left left] at hv
      exact a.adjacent i _ _ hz hv
    by_cases middle : i+1=xs.length
    · rw [List.getElem?_append_left (by omega)] at hz
      rw [List.getElem?_append_right (by omega),show i+1-xs.length=0 by omega] at hv
      simpa only [a.last i _ middle hz,b.first _ hv] using link
    · rw [List.getElem?_append_right (by omega)] at hz
      rw [List.getElem?_append_right (by omega),show i+1-xs.length=i-xs.length+1 by omega] at hv
      exact b.adjacent _ _ _ hz hv

theorem Routes.socketSequence {R X Y : Type} {f : Fabric X Y} {x : R ↪ X} {y : R ↪ Y}
    (r : Routes R f x y) (p : R) :
    SocketSequence f.fixedLink (f.firstColumn (x p)) (f.lastColumn (y p)) (r.socketPairs p) := by
  induction f with
  | step s =>
    constructor
    · exact Nat.zero_lt_succ 0
    · rintro z hit;exact congrArg Prod.fst (Option.some.inj hit).symm
    · intro i z hi hit
      have eq : i=0 := by change i+1=1 at hi;omega
      subst i
      exact congrArg Prod.snd (Option.some.inj hit).symm
    · intro i z v _ hit
      simp [socketPairs] at hit
  | seq a b ia ib =>
    obtain ⟨z,ra,rb⟩:=r
    exact ((ia ra).lift Sum.inl (fun _ _ hp=>hp)).join
      ((ib rb).lift Sum.inr (fun _ _ hp=>hp)) ⟨z p,rfl,rfl⟩

end
end Hierarchy.ProbeStage

end OAI
