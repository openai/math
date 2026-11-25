import OAI.Hierarchy.ProbeMaskedRoute

namespace OAI
/-! # The exact tile list rendered by the recursive subdivision -/

namespace Hierarchy.ProbeStage

def layer {R G : Type} [Fintype G] {m : ℕ} (p : Tiles R G m) : RoutedLayer R :=
  ⟨⟨G,m⟩,p⟩

private theorem tiles_ext {R G : Type} {m : ℕ} {a b : Tiles R G m}
    (hg : a.group=b.group) (hi : a.input=b.input) (ho : a.output=b.output) : a=b := by
  cases a;cases b;cases hg;cases hi;cases ho;rfl

theorem render_enter {R G : Type} [Fintype G] {m B : ℕ} (pos : 0<B)
    (p : Tiles R G m) (a : Allocation B (leftBlock p pos) (rightBlock p pos))
    (r : Routes R (.step (enterSockets G m B pos)) p.first (inner p pos a).first) :
    r.layers = [layer (enter p pos a)] := by
  apply congrArg (fun t : Tiles R (G × Fin (blocks m B)) (B*quota B) => [layer t])
  apply tiles_ext
  · rfl
  · rfl
  funext i
  have port := (join (G:=G) (blocks m B) B (quota B)).symm_apply_eq.mpr (enter_join p pos a i).symm
  exact congrArg Prod.snd port

theorem render_exit {R G : Type} [Fintype G] {m B : ℕ} (pos : 0<B)
    (p : Tiles R G m) (a : Allocation B (leftBlock p pos) (rightBlock p pos))
    (r : Routes R (.step (enterSockets G m B pos).reverse) (inner p pos a).last p.last) :
    r.layers = [layer (exitStage p pos a)] := by
  have port (i : R) := (join (G:=G) (blocks m B) B (quota B)).symm_apply_eq.mpr (exit_join p pos a i).symm
  apply congrArg (fun t : Tiles R (G × Fin (blocks m B)) (B*quota B) => [layer t])
  exact tiles_ext (funext (fun i => congrArg Prod.fst (port i)))
    (funext (fun i => congrArg Prod.snd (port i))) rfl

/-- Enter the current level, emit the child's complete list, then emit the
exit move of the same current level. -/
def render (R : Type) (B : ℕ) (pos : 0<B)
    (assign : {G : Type} → [Fintype G] → {m : ℕ} → (p : Tiles R G m) →
      Allocation B (leftBlock p pos) (rightBlock p pos)) :
    (remaining : ℕ) → {G : Type} → [Fintype G] → {m : ℕ} → Tiles R G m → List (RoutedLayer R)
  | 0,_,_,_,p => [layer p]
  | q+1,_,_,_,p =>
    let a := assign p
    [layer (enter p pos a)] ++ render R B pos assign q (inner p pos a) ++ [layer (exitStage p pos a)]

theorem route_render (R : Type) (B : ℕ) (pos : 0<B)
    (assign : {G : Type} → [Fintype G] → {m : ℕ} → (p : Tiles R G m) →
      Allocation B (leftBlock p pos) (rightBlock p pos)) (q : ℕ) {G : Type} [Fintype G] {m : ℕ}
    (p : Tiles R G m) : (route R B pos assign q p).layers = render R B pos assign q p := by
  induction q generalizing G m with
  | zero => rfl
  | succ q ih =>
    let a := assign p
    let t := inner p pos a
    let whole := route R B pos assign (q+1) p
    let he : Routes R (.step (enterSockets G m B pos)) p.first t.first := whole.2.1
    let hx : Routes R (.step (enterSockets G m B pos).reverse) t.last p.last := whole.2.2.2.2
    have parts : (route R B pos assign (q+1) p).layers =
        he.layers ++ ((route R B pos assign q t).layers ++ hx.layers) := rfl
    rw [parts,render_enter pos p a he,ih,render_exit pos p a hx]
    simp only [render,List.append_assoc,t,a]

theorem advised_render (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) :
    (advisedRoute h d π).layers = render _ (radix h d) (radix_pos h d)
      (fun p => allocateMasked p (radix_pos h d) (formatAdvice h d).row)
      (rounds d) (permutationTiles π) := route_render ..

end Hierarchy.ProbeStage

end OAI
