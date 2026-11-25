import OAI.Hierarchy.ProbeMaskedRoute
import OAI.Hierarchy.ProbeStageTemplateSize

namespace OAI
/-! # The exact physical route of every payload through the recursively advised fabric -/

namespace Hierarchy.ProbeStage
open Function
noncomputable section

/-- An input column and an output column are different sockets even if their port
ordinals agree. Distinct component stages use disjoint physical addresses. -/
def Fabric.Column : {X Y : Type} → Fabric X Y → Type
  | _,_,.step s => s.shape.Port ⊕ s.shape.Port
  | _,_,.seq a b => a.Column ⊕ b.Column

@[instance_reducible]
noncomputable def Fabric.columnFintype : {X Y : Type} → (f : Fabric X Y) → Fintype f.Column
  | _,_,.step s => inferInstanceAs (Fintype (s.shape.Port ⊕ s.shape.Port))
  | _,_,.seq a b => by
    letI := a.columnFintype
    letI := b.columnFintype
    exact inferInstanceAs (Fintype (a.Column ⊕ b.Column))

attribute [instance] Fabric.columnFintype

/-- Count exactly the columns created by the physical input/output sides of each stage. -/
theorem Fabric.column_card {X Y : Type} (f : Fabric X Y) : Fintype.card f.Column =
    2*(f.shapes.map fun g => Fintype.card g.Group*g.span).sum := by
  induction f with
  | step s =>
    change Fintype.card (s.shape.Port ⊕ s.shape.Port)=_
    rw [Fintype.card_sum]
    simp [Fabric.shapes,Shape.Port,two_mul]
  | seq a b ha hb =>
    change Fintype.card (a.Column ⊕ b.Column)=_
    rw [Fintype.card_sum,ha,hb]
    simp [Fabric.shapes,List.map_append,List.sum_append,Nat.mul_add]

/-- Uniform O(n) physical column count, including all inactive slots and both ends
of all fixed stage identifications. -/
theorem permutation_columns {h d : ℕ} (hd : 1 ≤ d) :
    Fintype.card (permutationFabric h d).Column ≤
      2*(permutationFabric h d).shapes.length*(4^(rounds d+1)*2^h) := by
  have sumBound (l : List Shape) (ok : ∀ g ∈ l, Shape.DyadicBounds h d g) :
      (l.map fun g => Fintype.card g.Group*g.span).sum ≤ l.length*(4^(rounds d+1)*2^h) := by
    induction l with
    | nil => simp
    | cons g gs ih =>
      have small := (ok g (List.mem_cons_self ..)).2
      have tail := ih (fun j hj => ok j (List.mem_cons_of_mem _ hj))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
      omega
  rw [Fabric.column_card,mul_assoc]
  exact Nat.mul_le_mul_left 2 (sumBound _ (template_dyadic hd))

def Fabric.firstColumn : {X Y : Type} → (f : Fabric X Y) → X ↪ f.Column
  | _,_,.step s => ⟨fun x => Sum.inl (s.source x),fun _ _ eq => s.source.injective (Sum.inl.inj eq)⟩
  | _,_,.seq a _ => ⟨fun x => Sum.inl (a.firstColumn x),fun _ _ eq => a.firstColumn.injective (Sum.inl.inj eq)⟩

def Fabric.lastColumn : {X Y : Type} → (f : Fabric X Y) → Y ↪ f.Column
  | _,_,.step s => ⟨fun x => Sum.inr (s.target x),fun _ _ eq => s.target.injective (Sum.inr.inj eq)⟩
  | _,_,.seq _ b => ⟨fun x => Sum.inr (b.lastColumn x),fun _ _ eq => b.lastColumn.injective (Sum.inr.inj eq)⟩

/-- Each unit edge is exactly one of the actual routed tile rows. The zero edges
at every internal joint are fixed by the fabric and independent of the permutation. -/
def Routes.payloadEdges {R : Type} : {X Y : Type} → {f : Fabric X Y} →
    {x : R ↪ X} → {y : R ↪ Y} → Routes R f x y → f.Column → f.Column → Bool → Prop
  | _,_,.step s,x,y,_ => fun (u v : s.shape.Port ⊕ s.shape.Port) flag =>
    match u,v,flag with
    | .inl i,.inr o,true => ∃ r, s.source (x r)=i ∧ s.target (y r)=o
    | _,_,_ => False
  | _,_,.seq a b,_,_,h => fun (u v : a.Column ⊕ b.Column) flag =>
    match u,v,flag with
    | .inl i,.inl j,f => Routes.payloadEdges (f:=a) h.2.1 i j f
    | .inr i,.inr j,f => Routes.payloadEdges (f:=b) h.2.2 i j f
    | .inl i,.inr j,false => ∃ shared, a.lastColumn shared=i ∧ b.firstColumn shared=j
    | _,_,_ => False

/-- A concrete path with exactly its tile count and its total number of wires. -/
inductive PayloadPath {C : Type} (edge : C → C → Bool → Prop) : C → C → ℕ → ℕ → Prop where
  | tile {x y} : edge x y true → PayloadPath edge x y 1 1
  | joint {x y} : edge x y false → PayloadPath edge x y 0 1
  | append {x y z a b c d} : PayloadPath edge x y a b → PayloadPath edge y z c d → PayloadPath edge x z (a+c) (b+d)

private theorem PayloadPath.lift {C D : Type} {edge : C → C → Bool → Prop}
    {dest : D → D → Bool → Prop} (place : C → D)
    (transfer : ∀ x y flag, edge x y flag → dest (place x) (place y) flag)
    {x y : C} {n m : ℕ} (path : PayloadPath edge x y n m) : PayloadPath dest (place x) (place y) n m := by
  induction path with
  | tile h => exact .tile (transfer _ _ _ h)
  | joint h => exact .joint (transfer _ _ _ h)
  | append _ _ ih ih' => exact ih.append ih'

/-- Price N and hop count 2N−1 come from the actual tile and joint rows. Each record
ends at its prescribed output embedding, hence at π(r) on the advised construction. -/
theorem Routes.payload_path {R X Y : Type} {f : Fabric X Y} {x : R ↪ X} {y : R ↪ Y}
    (route : Routes R f x y) (r : R) :
    ∃ m, m+1=2*f.shapes.length ∧ PayloadPath route.payloadEdges
      (f.firstColumn (x r)) (f.lastColumn (y r)) f.shapes.length m := by
  induction f with
  | step s => exact ⟨1,rfl,.tile ⟨r,rfl,rfl⟩⟩
  | seq a b ih ih' =>
    obtain ⟨m,l,pa⟩ := ih route.2.1
    obtain ⟨m',l',pb⟩ := ih' route.2.2
    let relation := Routes.payloadEdges (f:=.seq a b) route
    have left : PayloadPath relation (.inl _) (.inl _) a.shapes.length m :=
      pa.lift Sum.inl (fun _ _ _ h => h)
    have right : PayloadPath relation (.inr _) (.inr _) b.shapes.length m' :=
      pb.lift Sum.inr (fun _ _ _ h => h)
    have link : PayloadPath relation (.inl (a.lastColumn (route.1 r)))
        (.inr (b.firstColumn (route.1 r))) 0 1 := .joint ⟨route.1 r,rfl,rfl⟩
    refine ⟨m+1+m',?_,?_⟩
    · simp only [Fabric.shapes,List.length_append]; omega
    · have first : (a.seq b).firstColumn (x r)=Sum.inl (a.firstColumn (x r)) := rfl
      have last : (a.seq b).lastColumn (y r)=Sum.inr (b.lastColumn (y r)) := rfl
      rw [first,last,Fabric.shapes,List.length_append]
      simpa only [Nat.add_zero] using (left.append link).append right

end
end Hierarchy.ProbeStage

namespace Hierarchy.ProbeStage
noncomputable section

/-- External tag ports occupy their own two banks of columns. Each fixed end-of-fabric
identification has scale zero and makes one extra hop between distinct occurrences. -/
abbrev Fabric.AllColumns {X Y : Type} (f : Fabric X Y) := X ⊕ (f.Column ⊕ Y)

def Routes.allPayloadEdges {R X Y : Type} {f : Fabric X Y} {x : R ↪ X} {y : R ↪ Y}
    (route : Routes R f x y) : f.AllColumns → f.AllColumns → Bool → Prop
  | .inl i,Sum.inr (.inl c),false => c=f.firstColumn i
  | .inr (.inl b),.inr (.inl c),flag => route.payloadEdges b c flag
  | .inr (.inl c),.inr (.inr o),false => c=f.lastColumn o
  | _,_,_ => False

theorem Routes.external_path {R X Y : Type} {f : Fabric X Y} {x : R ↪ X} {y : R ↪ Y}
    (route : Routes R f x y) (r : R) : PayloadPath route.allPayloadEdges
      (.inl (x r)) (.inr (.inr (y r))) f.shapes.length (2*f.shapes.length+1) := by
  obtain ⟨m,eq,p⟩ := route.payload_path r
  have first : PayloadPath route.allPayloadEdges (.inl (x r)) (.inr (.inl (f.firstColumn (x r)))) 0 1 :=
    .joint rfl
  have inner := p.lift (fun c => Sum.inr (Sum.inl c)) (dest:=route.allPayloadEdges) (fun _ _ _ e => e)
  have last : PayloadPath route.allPayloadEdges (.inr (.inl (f.lastColumn (y r)))) (.inr (.inr (y r))) 0 1 :=
    .joint rfl
  convert (first.append inner).append last using 1 <;> omega

theorem all_column_bound (h d : ℕ) (hd : 1 ≤ d) :
    Fintype.card (permutationFabric h d).AllColumns ≤
    2*(2^h)+2*(permutationFabric h d).shapes.length*(4^(rounds d+1)*2^h) := by
  have inside := permutation_columns (h:=h) hd
  simp only [Fabric.AllColumns,Fintype.card_sum,Fintype.card_prod,Fintype.card_unit,Fintype.card_fin,one_mul]
  omega

end
end Hierarchy.ProbeStage

end OAI
