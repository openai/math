import OAI.Computability.IntegerMultiplication.Phase.Align

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Tensor Net.Walsh Strip Strip.Optic Matrix Finset
variable {O I J N K R : Type} [CommRing R] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

-- same XOR on rows of J, directed via one privileged source.
def sync (j : J) (b : J→B) (x : Addr J) : Addr J :=
  fun k => x k + b k*x j
def convey (j : J) (b : J→B) (t : b j=0) : Equiv.Perm (Addr J) where
  toFun := sync j b
  invFun := sync j b
  left_inv x := by
    funext k
    simp [sync,t,add_assoc,show ∀ z:B,z+z=0 by decide]
  right_inv x := by
    funext k
    simp [sync,t,add_assoc, show ∀ z:B,z+z=0 by decide]
omit [Fintype J] [DecidableEq J] in
theorem sync_add (j : J) (b : J→B) (x y : Addr J) :
    sync j b (x+y) = sync j b x + sync j b y := by
  funext i; simp [sync,mul_add,add_left_comm,add_assoc]

omit [Fintype J] [DecidableEq J] in
theorem unite (j : J) (b u : J→B) (s : b j=0) (x : Addr J) :
    sync j u (sync j b x) = sync j (b+u) x := by
  funext i; simp [sync,s,add_mul,add_assoc]
def reduced (v : Addr J) (j : J) : Addr J := v - lad j
omit [Fintype J] in
theorem forfeit (v : Addr J) (j : J) (h : v j=1) : (reduced v j) j=0 := by
  simp [reduced,lad,h]
omit [Fintype J] in
theorem achieve (v : Addr J) (j : J) :
    sync j (reduced v j) (lad j) = v := by
  funext i; simp [sync,reduced,lad]
def project (z : Equiv.Perm I) : Equiv.Perm (N→I) :=
  Equiv.piCongrRight (fun _ => z)
omit [Fintype N] [DecidableEq N] in
theorem project_there (z : Equiv.Perm I) (x : N→I) :
    project z x = z ∘ x := rfl
omit [Fintype N] [DecidableEq N] in
@[simp] theorem project_symm (z : Equiv.Perm I) :
    (project (N:=N) z).symm = project z.symm := rfl

-- Kernel natural under applying a binary change of basis on J
variable (c : Quarter R)
omit [DecidableEq J] in
theorem cardinal (j : J) (u : Addr J) (s : u j=0)
    (v x y : Addr J) (m : Bool) :
    let t := sync j u
    kernel c m (t v) (t x) (t y) = kernel c m v x y := by
  simp only [kernel,Matrix.smul_apply,Matrix.one_apply,Matrix.add_apply,smul_eq_mul,shade,of_apply]
  have z (x y : Addr J) : sync j u x = sync j u y ↔ x=y := (convey j u s).apply_eq_iff_eq
  simp only [← sync_add,z]

theorem inter [Fintype I] (z : Equiv.Perm I) (a d : Mat I R)
    (h : ∀ x y,d (z x) (z y)=a x y) (m : I→R) :
    d *ᵥ travel z m = travel z (a *ᵥ m) := by
  funext t
  obtain ⟨t,rfl⟩ := z.surjective t
  rw [completed]
  change (∑ j,d _ j * (m ∘ z.symm) j)=∑ j, a t j * m j
  let g j := d (z t) j*(m ∘ z.symm) j
  change ∑ j, g j = _
  rw [← Equiv.sum_comp z g]
  simp only [g,Function.comp_apply,Equiv.symm_apply_apply,h]
theorem crowd [Fintype I] (z : Equiv.Perm I) (a d : Mat I R)
    (h : ∀ x y,d (z x) (z y)=a x y) (m : (N→I) → R) :
    Tensor.mat (fun _ : N => d) *ᵥ travel (project z) m =
      travel (project z) (Tensor.mat (fun _ : N => a) *ᵥ m) :=
  inter _ _ _ (by intro _ _; simp [Tensor.app,project_there,h]) m

theorem steer [Fintype I] (l : Lens O (N→I) K)
    (a d : Mat I R) (z : Equiv.Perm I)
    (h : ∀ x y, d (z x) (z y)=a x y) (m : O→R) :
    let Z := Strip.Optic.field l (project z)
    operate l (Tensor.mat (fun _ => d)) (travel Z m) =
      travel Z (operate l (Tensor.mat (fun _ => a)) m) := by
  simp_rw [inside,operate,everywhere,beam_after]
  congr 1
  funext _ _
  exact crowd z a d h _

theorem quotient (o : Optic.Layout O N J K) (v : Addr J)
    (j : J) (e : v j=1) (b : Bool) (w : O→R) :
    let Z := Strip.Optic.field o (project (convey j (reduced v j) (forfeit v j e)))
    travel Z (pipe o (kernel c b (lad j)) (travel Z w)) =
    pipe o (kernel c b v) w := by
  let z := convey j (reduced v j) (forfeit v j e)
  let i := Strip.Optic.field o (project z)
  change travel i (operate _ _ (travel i w))=operate _ _ _
  have g (x y) := cardinal c j (reduced v j) (forfeit v j e) (lad j) x y b
  simp only [achieve] at g
  have s := steer o (kernel c b (lad j)) (kernel c b v) z g (travel i w)
  change operate _ _ (travel i (travel i _)) = _ at s
  have iden : i.symm = i := by apply Equiv.ext; exact fun _ => rfl
  have zz : travel i (travel i w)=w := by
    funext t; change w (i.symm (i.symm t))=_
    have g := i.apply_symm_apply t
    rw [iden] at *; rw [g]
  rw [zz] at s
  exact s.symm

-- factor convey as a finite list of row adds
theorem tape (j : J) (u : Addr J) (t : u j=0) :
    ∃ l : List J, (∀i∈l,i≠j) ∧
    (∀ x, l.foldl (fun y i => sync j (lad i) y) x = sync j u x) := by
  classical
  let s := Finset.univ.filter (fun i => u i=1)
  refine ⟨s.toList,fun i hi hn => ?_, fun x => ?_⟩
  · have : u j=1 := hn ▸ (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2
    rw [t] at this; exact absurd this (by decide)
  have d : ∀ l : List J,(∀i∈l,i≠j)→∀x, l.foldl (fun y i => sync j (lad i) y) x =
      sync j ((l.map lad).sum) x := by
    intro l
    induction l with
    | nil =>
      intro _ x; funext i; change x i=x i+0*x j; simp
    | cons i l ih =>
      intro he x
      rw [List.foldl_cons, ih (fun k h => he k (List.mem_cons_of_mem _ h)),List.map_cons,List.sum_cons,
        unite j (lad i) _ (by simp [lad,Ne.symm (he i List.mem_cons_self)])]
  rw [d]
  · congr
    funext i
    rw [Finset.sum_map_toList,Finset.sum_apply]
    -- characterize
    change (∑ a∈s,lad a i)=_
    simp [lad,s,eq_comm]
    rcases Walsh.bit_value (u i) with h|h <;> simp [h]
  intro i hi r
  have : u j=1 := r ▸ (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2
  rw [t] at this; exact absurd this (by decide)

omit [DecidableEq J] in
theorem privileged (v : Addr J) (e : v ⬝ᵥ v=1) :
    ∃ j,v j=1 := by
  by_contra! h
  have x : v=0 := funext fun i => (bit_value _).resolve_right (h i)
  simp [x] at e
end Phase

end IntegerMultiplication
end Computability
end OAI
