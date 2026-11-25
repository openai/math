import OAI.Computability.IntegerMultiplication.Echo.Field

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Echo
open Finset IntegerMultiplication.Fourier Cap
variable {s t:ℕ}
abbrev glue (e:s≤t) := fun i:Spot s=> (⟨i.val,i.isLt.trans_le e⟩:Spot t)
def hair {A:Type*} [Zero A] (f:Spot s→A) (a:Spot t) : A :=
  if h:a.val< s then f ⟨a.val,h⟩ else 0
@[simp] theorem glue_inj (e:s≤t) : Function.Injective (glue e) :=
  fun _i _j v=> Fin.ext (congrArg (@Fin.val t) v)
@[simp] theorem validGlue (e:s≤t) (i:Spot s) : (glue e i).val < s := i.isLt
@[simp] theorem collect {A:Type*} [Zero A] (e:s≤t) (f:Spot s→A) (i:Spot s):
    hair f (glue e i)=f i := by unfold hair; simp
-- any pi dimension
variable {d:ℕ} {n m : Bounds d}
abbrev patch (e:n≤ m) (v:Vector_ n):Vector_ m := fun i=> glue (e i) (v i)
theorem patched (e:n≤ m) : Function.Injective (patch e) :=
  fun _a _b q=> funext fun i=> glue_inj (e i) (congrFun q i)

def Valid (n:Bounds d) (x:Vector_ m):Prop := ∀ i,(x i).val < n i
def recover (n:Bounds d) (x:Vector_ m) (h : Valid n x) : Vector_ n:=fun i=>⟨(x i).val,h i⟩
theorem valid_ (e:n≤ m) (x:Vector_ n): Valid n (patch e x) := fun _=> validGlue ..
@[simp] theorem unpack (e:n≤ m) (x:Vector_ n) (h : Valid n (patch e x)):
    recover n (patch e x) h=x := rfl
@[simp] theorem box (e:n≤ m) (x:Vector_ m) (h:Valid n x):
    patch e (recover n x h)=x:= rfl

private instance dValid {n:Bounds d} (x:Vector_ m):Decidable (Valid n x):=
  Fintype.decidableForallFintype
def shell {A:Type*} [Zero A] (f:Vector_ n→A) (x:Vector_ m): A :=
  if h:Valid n x then f (recover n x h) else 0
theorem barter {A:Type*} [Zero A] (e:n≤ m) (f:Vector_ n→A) (x:Vector_ n):
    shell f (patch e x)=f x := by unfold shell; split; rfl; next h=> exact (h (valid_ e x)).elim
theorem barren {A:Type*} [Zero A] (h_:n≤ m) (f:Vector_ n→A) {x:Vector_ m} (h : x∉ (Set.range (patch (show n≤ m from h_)))) :
    shell f x=0 := by unfold shell; split <;> first|rfl|exact (h ⟨_,box _ _ (by assumption)⟩).elim

noncomputable def cast_ (k:Square n) : Square m :=
  fun i x y=> hair (fun x' => hair (k i x') y) x
@[simp] theorem cast_eq (e:n≤ m) (k:Square n) (x y:Vector_ n) (i:Fin d):
    cast_ k i (patch e x i) (patch e y i)=k i (x i) (y i) := by unfold cast_ patch; rw [collect,collect]
theorem cast_v (e:n≤ m) (k:Square n) {z:Vector_ m} (h:z∉Set.range (patch e))(y:Vector_ m):
    ∏ i,cast_ k i (z i) (y i)=0 ∧ ∏ i,cast_ k i (y i) (z i)=0 := by
  have U : ¬Valid n z := fun a=> h ⟨_,box e z a⟩
  obtain ⟨i,v⟩:= not_forall.mp U
  constructor
  · apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact dite_eq_right v
  · apply Finset.prod_eq_zero (Finset.mem_univ i)
    unfold cast_ hair; split
    next h =>rfl
    rfl

theorem sumImage {A B:Type*} [Fintype A] [Fintype B] [DecidableEq B] {O:Type*} [AddCommMonoid O] (f:A→B)
    (h:Function.Injective f) (x:B→O) (p:∀ b∉Set.range f,x b=0):
    ∑ b,x b=∑ a,x (f a) := by
  rw [← Finset.sum_subset (subset_univ (Finset.image f univ)) (by intro b _ h; apply p; simpa using h)]
  exact sum_image (fun _ _ _ _=> fun e=> h e)
theorem extension (e:n≤ m) (k:Square n) (x:Along n) :
    strand m (cast_ k) (shell x) = shell (strand n k x) := by
  classical
  funext i
  by_cases h:i∈Set.range (patch e)
  · obtain ⟨z,rfl⟩:=h
    rw [barter]
    unfold strand
    rw [sumImage (patch e) (patched e) _ (by
      intro y v; rw [barren e _ v,mul_zero])]
    simp_rw [cast_eq,barter e]
  unfold strand; rw [barren e _ h]
  apply Finset.sum_eq_zero
  intro j _
  rw [(cast_v e k h j).1,zero_mul]

theorem shell_pt (x y:Along n):
    (fun i:Vector_ m=>shell x i*shell y i)=shell (fun i=>x i*y i) := by
  funext i; unfold shell; split; rfl; simp
end Echo

end IntegerMultiplication
end Computability
end OAI
