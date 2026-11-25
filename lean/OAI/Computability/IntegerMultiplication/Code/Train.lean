import OAI.Computability.IntegerMultiplication.Code.Carry

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
variable {X Y Z : Type*}
-- card budget, reserve 1 even for empty
def cars (a : X → ℝ) (l : List X) :=
  (l.map a).sum + 1
@[simp] theorem cars_nil (a : X → ℝ) : cars a []=1 := by simp [cars]
@[simp] theorem cars_cons (a : X → ℝ) (x l) :
    cars a (x::l) = a x + cars a l := by simp [cars, add_assoc]
theorem cars_pos {a : X → ℝ} (e : ∀ x,0≤a x) (l : List X) : 1 ≤ cars a l := by
  induction l with
  | nil => simp
  | cons x l ih => rw [cars_cons]; linarith [e x]
@[simp] theorem cars_map (a : X→ℝ) (f : Y→X) (l : List Y) :
    cars a (l.map f) = cars (fun x => a (f x)) l := by induction l <;> simp_all

theorem cars_up {a b : X→ℝ} (l : List X) (h : ∀x∈l,a x≤b x) : cars a l ≤ cars b l := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.mem_cons] at h; rw [cars_cons,cars_cons]
    exact add_le_add (h x (.inl rfl)) (ih fun x hx => h x (.inr hx))
@[simp] theorem cars_fixed (c : ℝ) (l : List X) : cars (fun _ => c) l = (l.length:ℝ)*c+1 := by
  induction l with
  | nil => simp
  | cons x l ih => rw [cars_cons,ih,List.length_cons,Nat.cast_add,Nat.cast_one]; ring

open _root_.OAI.Computability.IntegerMultiplication.Code.Task
namespace Volume
variable {p : X→Tree} {a : X→ℝ}
theorem car (h : Volume a p) (e : ∀x, 1≤a x) :
    Volume (cars a) (Task.forest p) := by
  obtain ⟨D,hh⟩ := h
  refine ⟨D+1,fun l => ?_⟩
  induction l with
  | nil => simp [Tree.count]
  | cons x l ih =>
    rw [forest_cons,cars_cons,Tree.count]
    specialize hh x; specialize e x
    push_cast at *
    linarith
end Volume
namespace Carries
variable {a d : X → ℝ} {p q r : X → Tree}
theorem transfer (h : Carries a p q) :
    Carries (cars a) (forest p) (forest q) := by
  have hp := h.small.car h.budget
  refine ⟨?_,hp⟩
  obtain ⟨e,b,hc,D,u⟩ := h.runs
  have v (x) : 0 ≤ a x := le_trans (by norm_num) (e x)
  obtain ⟨H,hh⟩ := hp
  have hu := Task.mapTask (X:=X) Unit (fun _ => p) (fun _ => q) (a := fun _ => b)
    (B := fun _ _ => True) (hc.on fun i : {x : Unit × X // True} => i.val.2)
  refine ⟨cars_pos v,_, hu.on (fun l : List X => ⟨((),l),by simp⟩), D+H+1, fun l => ?_⟩
  have cost : ((costSum b l:ℕ):ℝ) ≤ D * cars a l := by
    induction l with
    | nil => simp
    | cons x l ih =>
      rw [costSum_cons,Nat.cast_add,cars_cons,mul_add]
      apply add_le_add _ ih; specialize u x; linarith
  dsimp only; push_cast
  specialize hh l; have := cars_pos v l
  linarith

/-- Lift to dependent family with varying X over parameters. -/
theorem nested {I : Type*} {A : I → Type*} {a : (i : I) → A i → ℝ} {p q : (i : I) → A i → Tree}
    (h : Carries (fun s : Sigma A => a s.1 s.2) (fun s => p s.1 s.2) (fun s => q s.1 s.2)) :
    Carries (fun s : Σ i, List (A i) => cars (a s.1) s.2) (fun s => forest (p s.1) s.2)
      (fun s => forest (q s.1) s.2) := by
  let lum (s : Σ i, List (A i)) := s.2.map (Sigma.mk s.1)
  simpa [Function.comp_def,lum] using h.transfer.slide lum

-- form for fixed multiplier estimates
theorem batch {I : Type*} {A : I → Type*} {k : I → ℝ} {p q : (i : I) → A i → Tree}
    (h : Carries (fun s : Sigma A => k s.1) (fun s => p s.1 s.2) (fun s => q s.1 s.2)) :
    Carries (fun s : Σ i, List (A i) => (s.2.length:ℝ)*k s.1+1) (fun s => forest (p s.1) s.2)
      (fun s => forest (q s.1) s.2) := by
  simpa using nested (a:= fun i _ => k i) (p:=p) (q:=q) h
end Carries
end Code

end IntegerMultiplication
end Computability
end OAI
