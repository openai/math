import OAI.Hierarchy.ProbeFabricAddress
import OAI.Hierarchy.ProbeRoutedSocketPairs
import OAI.Hierarchy.ProbeAdvisedPurchase

namespace OAI
/-! # The chronological route rows and the advised stage arrays name identical sockets -/
namespace Hierarchy.ProbeStage
noncomputable section

def Tiles.socket {R : Type} {s : Shape} (a : Tiles R s.Group s.span) (p : R) (side : Bool) :
    s.Socket := (a.group p,if side then .inr (a.output p) else .inl (a.input p))

def RoutedLayer.socketTag {R : Type} (l : RoutedLayer R) (p : R) (side : Bool) :
    Σ s : Shape,s.Socket := ⟨l.shape,(l.tiles.socket (s:=l.shape) p side)⟩

def pairSocket {C : Type*} (side : Bool) (z : C × C) := if side then z.2 else z.1

theorem Routes.layer_length {R X Y : Type} {f : Fabric X Y} {x : R ↪ X} {y : R ↪ Y}
    (r : Routes R f x y) : r.layers.length=f.shapes.length := by
  simpa only [List.length_map] using congrArg List.length r.layer_shapes

private theorem map_hit_left {A B C : Type*} (xs : List A) (ys : List B) (f : A→C) (g : B→C)
    {i : ℕ} {z : C} (left : i<xs.length) (hit : (xs.map f ++ ys.map g)[i]?=some z) :
    ∃ a,xs[i]?=some a ∧ f a=z := by
  rw [List.getElem?_append_left (by simpa only [List.length_map] using left),List.getElem?_map] at hit
  exact Option.map_eq_some_iff.mp hit

private theorem map_hit_right {A B C : Type*} (xs : List A) (ys : List B) (f : A→C) (g : B→C)
    {i : ℕ} {z : C} (right : xs.length ≤ i) (hit : (xs.map f ++ ys.map g)[i]?=some z) :
    ∃ b,ys[i-xs.length]?=some b ∧ g b=z := by
  rw [List.getElem?_append_right (by simpa only [List.length_map] using right),
    List.length_map,List.getElem?_map] at hit
  exact Option.map_eq_some_iff.mp hit

theorem Routes.socketPair_key {R X Y : Type} {f : Fabric X Y} {x : R ↪ X} {y : R ↪ Y}
    (r : Routes R f x y) (p : R) (i : ℕ) (z : f.Column × f.Column) (l : RoutedLayer R)
    (hit : (r.socketPairs p)[i]?=some z) (row : r.layers[i]?=some l) (side : Bool) :
    f.socketKey (pairSocket side z)=(i,l.socketTag p side) := by
  induction f generalizing i l with
  | step s =>
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hit
      obtain rfl := Option.some.inj row
      cases side
      · rfl
      · change (0,(⟨s.shape,(s.target (y p)).1,.inr (s.target (y p)).2⟩ : Σ t : Shape,t.Socket)) =
            (0,(⟨s.shape,(s.source (x p)).1,.inr (s.target (y p)).2⟩ : Σ t : Shape,t.Socket))
        rw [r.down p]
    | succ i => simp [layers] at row
  | seq a b ia ib =>
    obtain ⟨q,ra,rb⟩:=r
    change (((ra.socketPairs p).map (mapSocketPair Sum.inl) ++
      (rb.socketPairs p).map (mapSocketPair Sum.inr))[i]?)=some z at hit
    change (ra.layers++rb.layers)[i]?=some l at row
    by_cases left : i<a.shapes.length
    · obtain ⟨v,found,mapped⟩ := map_hit_left (ra.socketPairs p) (rb.socketPairs p)
        (mapSocketPair (Sum.inl : a.Column→a.Column⊕b.Column)) (mapSocketPair Sum.inr)
        (by simpa only [ra.socketPairs_length] using left) hit
      subst z
      rw [List.getElem?_append_left (by simpa only [ra.layer_length] using left)] at row
      have child:=ia (r:=ra) (i:=i) (z:=v) (l:=l) found row
      cases side <;> exact child
    · have right : a.shapes.length ≤ i := Nat.le_of_not_gt left
      obtain ⟨v,found,mapped⟩ := map_hit_right (ra.socketPairs p) (rb.socketPairs p)
        (mapSocketPair (Sum.inl : a.Column→a.Column⊕b.Column)) (mapSocketPair Sum.inr)
        (by simpa only [ra.socketPairs_length] using right) hit
      subst z
      rw [List.getElem?_append_right (by simpa only [ra.layer_length] using right)] at row
      rw [ra.socketPairs_length] at found
      rw [ra.layer_length] at row
      have child:=ib (r:=rb) (i:=i-a.shapes.length) (z:=v) (l:=l) found row
      have lift : (Fabric.seq a b).socketKey (pairSocket side (mapSocketPair Sum.inr v)) =
          Fabric.shiftSocket a.shapes.length (b.socketKey (pairSocket side v)) := by cases side <;> rfl
      exact lift.trans ((congrArg (Fabric.shiftSocket a.shapes.length) child).trans
        (Prod.ext (by dsimp [Fabric.shiftSocket];omega) rfl))

private theorem RoutedLayer.tag_transport {R : Type} (l : RoutedLayer R) (s : Shape)
    (e : l.shape=s) (p : R) (side : Bool) :
    l.socketTag p side=⟨s,((e ▸ l.tiles : Tiles R s.Group s.span).socket (s:=s) p side)⟩ := by
  cases e
  rfl

theorem advised_socket_tag (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) (t : StageAt h d)
    (p : Fin (2^h)) (side : Bool) :
    ((advisedRoute h d π).layers[t.val]?).map (fun l=>l.socketTag p side)=
      some ⟨stageAt h d t,(advisedStage h d π t).socket (s:=stageAt h d t) p side⟩ := by
  rw [List.getElem?_eq_getElem (by simpa only [(advisedRoute h d π).layer_length] using t.isLt),Option.map_some]
  apply congrArg some
  unfold advisedStage
  exact RoutedLayer.tag_transport _ _ _ p side

end
end Hierarchy.ProbeStage

end OAI
