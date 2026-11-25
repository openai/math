import OAI.Hierarchy.ProbeStagePorts

namespace OAI
/-! # Fixed subdivision lists and record routes through every phase -/

namespace Hierarchy.ProbeStage

open Function

structure Shape where
  Group : Type
  [groups : Fintype Group]
  span : ℕ

attribute [instance] Shape.groups
abbrev Shape.Port (s : Shape) := s.Group × Fin s.span

/-- Embeddings expose the fixed position lists of a single move on each
side of the two physical joint spaces. -/
structure Sockets (X Y : Type) where
  shape : Shape
  source : X ↪ shape.Port
  target : Y ↪ shape.Port

/-- A fabric describes shuffling and padding between moves without referring
to a matching. An occupied joint always has a unique address. -/
inductive Fabric : Type → Type → Type 1
  | step {X Y} (s : Sockets X Y) : Fabric X Y
  | seq {X Z Y} (a : Fabric X Z) (b : Fabric Z Y) : Fabric X Y

def Fabric.shapes : {X Y : Type} → Fabric X Y → List Shape
  | _,_,.step s => [s.shape]
  | _,_,.seq a b => a.shapes ++ b.shapes

/-- Every internal joint carries an injective placement of all records.
At each move the record must stay within a single group. -/
def Routes (R : Type) : {X Y : Type} → Fabric X Y → (R ↪ X) → (R ↪ Y) → Type
  | _,_,.step s,x,y => PLift (∀ r, (s.source (x r)).1 = (s.target (y r)).1)
  | _,_,.seq a b,x,y => Σ z : R ↪ _, Routes R a x z × Routes R b z y

structure RoutedLayer (R : Type) where
  shape : Shape
  tiles : Tiles R shape.Group shape.span

def Routes.layers {R : Type} : {X Y : Type} → {f : Fabric X Y} →
    {x : R ↪ X} → {y : R ↪ Y} → Routes R f x y → List (RoutedLayer R)
  | _,_,.step s,x,y,h => [⟨s.shape, ⟨
    fun r => (s.source (x r)).1, fun r => (s.source (x r)).2, fun r => (s.target (y r)).2,
    fun _ _ eq => x.injective (s.source.injective eq),
    fun i j eq => y.injective (s.target.injective (Prod.ext
      ((h.down i).symm.trans ((Prod.mk.inj eq).1.trans (h.down j))) (Prod.mk.inj eq).2))⟩⟩]
  | _,_,.seq a b,_,_,h => Routes.layers (f:=a) h.2.1 ++ Routes.layers (f:=b) h.2.2

theorem Routes.layer_shapes {R X Y : Type} {f : Fabric X Y} {x : R ↪ X} {y : R ↪ Y}
    (h : Routes R f x y) : h.layers.map RoutedLayer.shape = f.shapes := by
  induction f with
  | step s => rfl
  | seq a b ha hb =>
    exact (List.map_append ..).trans (congrArg₂ (· ++ ·) (ha h.2.1) (hb h.2.2))

def Tiles.first {R G : Type} {m : ℕ} (p : Tiles R G m) : R ↪ G × Fin m :=
  ⟨fun r => (p.group r,p.input r),p.input_inj⟩

def Tiles.last {R G : Type} {m : ℕ} (p : Tiles R G m) : R ↪ G × Fin m :=
  ⟨fun r => (p.group r,p.output r),p.output_inj⟩

def blockSocket (G : Type) (m B : ℕ) (pos : 0 < B) :
    (G × Fin m) ↪ ((G × Fin (blocks m B)) × Fin (B*quota B)) where
  toFun x := ((x.1,(decode m B pos x.2).1), Fin.castLE (blockSize_le_reserved B) (decode m B pos x.2).2)
  inj' := by
    intro x y eq
    have he := Prod.mk.inj eq
    have bg := Prod.mk.inj he.1
    have off := congrArg (fun i : Fin (B*quota B) => i.val) he.2
    exact Prod.ext bg.1 ((decode m B pos).injective (Prod.ext bg.2 (Fin.ext off)))

def enterSockets (G : Type) [Fintype G] (m B : ℕ) (pos : 0 < B) :
    Sockets (G × Fin m) ((G × Fin B) × Fin (innerSize m B)) where
  shape := ⟨G × Fin (blocks m B),B*quota B⟩
  source := blockSocket G m B pos
  target := (join (blocks m B) B (quota B)).symm.toEmbedding

def Sockets.reverse {X Y : Type} (s : Sockets X Y) : Sockets Y X :=
  ⟨s.shape,s.target,s.source⟩

/-- The fixed centered list surrounded by the entering/exiting block moves
at every level. Neither the positions nor the identifications require a
choice of colors. -/
def template (B : ℕ) (pos : 0 < B) :
    (q : ℕ) → (G : Type) → [Fintype G] → (m : ℕ) → Fabric (G × Fin m) (G × Fin m)
  | 0,G,_,m => .step ⟨⟨G,m⟩,Embedding.refl _,Embedding.refl _⟩
  | q+1,G,_,m => .seq (.step (enterSockets G m B pos))
    (.seq (template B pos q (G × Fin B) (innerSize m B)) (.step (enterSockets G m B pos).reverse))

theorem template_length (B : ℕ) (pos : 0 < B) (q : ℕ) (G : Type) [Fintype G] (m : ℕ) :
    (template B pos q G m).shapes.length = 2*q+1 := by
  induction q generalizing G m with
  | zero => rfl
  | succ q ih =>
    simp only [template,Fabric.shapes,List.length_append,List.length_cons,List.length_nil]
    rw [ih]
    omega

/-- Successive bounded-congestion colorings fill the fixed template. The
middle output of every subroute is the original tile's required endpoint. -/
def route (R : Type) (B : ℕ) (pos : 0 < B)
    (assign : {G : Type} → [Fintype G] → {m : ℕ} → (p : Tiles R G m) →
      Allocation B (leftBlock p pos) (rightBlock p pos)) :
    (q : ℕ) → {G : Type} → [Fintype G] → {m : ℕ} → (p : Tiles R G m) →
      Routes R (template B pos q G m) p.first p.last
  | 0,_,_,_,p => ⟨fun _ => rfl⟩
  | q+1,G,_,m,p => by
    let a := assign p
    let t := inner p pos a
    refine ⟨t.first,⟨?_⟩,t.last,route R B pos assign q t,⟨?_⟩⟩
    · intro r
      have joint := (join (G:=G) (blocks m B) B (quota B)).symm_apply_eq.mpr (enter_join p pos a r).symm
      have groups := congrArg Prod.fst joint.symm
      exact groups
    · intro r
      have joint := (join (G:=G) (blocks m B) B (quota B)).symm_apply_eq.mpr (exit_join p pos a r).symm
      have groups := congrArg Prod.fst joint
      exact groups

end Hierarchy.ProbeStage

end OAI
