import OAI.Computability.IntegerMultiplication.Packed.Light

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Strip Code Loom Adic Port Dims Strip.Optic
noncomputable section

variable {X : Type} (P G R S : X→Tape) (H L i : X→ℕ) {r : Regime X}
variable (hP : Told r P) (hG : Told r G) (hR : Told r R) (hS : Told r S)
variable (h : r.Has fun x=>signs (H x) (L x) (i x)) (c : r.Has (tally ∘ extent H L i))
variable (guard : ∀ x a,a∈P x++G x++R x++S x→a≤Net.Shuttle.base)
variable {l : X→ℕ}
variable (spar : ∀ x, (3*extent H L i x+1)*(32*i x)≤ 2^width (H x) (L x))
variable {U:X→Type} (u : (x:X)→Series (U x)) (z : ∀ x,(u x).count≤l x)

-- xor selected in chunks on actual Slot Q
def move {H L i} :=
  (ideal (H:=H) (L:=L) (i:=i)).trans streak

include hP hG hR hS h c z guard spar
attribute [local irreducible] order
set_option maxRecDepth 2000 in
private theorem sealed (p : Equiv.Perm Pos) :
    Action P G R S H L i (r:=r) (l:=l) u (fun _x=> agent p move) := by
  have U :
      Action P G R S H L i (r:=r) (l:=l) u (fun x=> agent p repair) :=
    fun v => Breeze.launch (shower P G R S H L i hP hG hR hS h c spar u z v p)
      (Spindle.belly (extent H L i) Net.Motif.sigma_range.1.le)
  have cp (m n : (x:X) → Equiv.Perm (Plate (H x) (L x) (i x))) (M : Action P G R S H L i (r:=r) (l:=l) u (fun x=>agent p (m x)))
      (N : Action P G R S H L i (r:=r) (l:=l) u (fun x=>agent p (n x))) :
      Action P G R S H L i (r:=r) (l:=l) u (fun x=>agent p ((m x).trans (n x))) := by
    have h0 := port P G R S H L i hP hG hR hS c
    intro f
    let v x := travel (invoke (agent p (m x)) (P x) (G x) (R x) (S x)) (f x)
    have e := Spindle.Breeze.pipe (M f) (N v) (Drive.fetch h0.1 (cloth_size _ _ h0 f z))
    let T x := (agent p (m x)).trans (agent p (n x))
    suffices eq : (fun x => agent p ((m x).trans (n x)))=T by rw [eq]; exact e
    funext x
    exact (agent_con ..).symm
  have eq (H L i : ℕ) : (cruise order).trans (repair (H:=H) (L:=L) (i:=i))=ideal := by
    ext x : 1; simp only [repair,Equiv.trans_apply,Equiv.symm_apply_apply]
  let f (x:X) := cruise (H:=H x) (L:=L x) (i:=i x) order
  let g (x:X) := repair (H:=H x) (L:=L x) (i:=i x)
  let m (x:X) := ideal (H:=H x) (L:=L x) (i:=i x)
  have V : Action P G R S H L i (r:=r) (l:=l) u (fun x => agent p (m x)) := by
    have e : m=(fun x=> (f x).trans (g x)) := funext (fun _=> (eq ..).symm)
    rw [e]
    exact cp f g (touring P G R S H L i hP hG hR hS h c guard u z p) U
  exact cp m _ V (theory P G R S H L i hP hG hR hS h c u z p)

end

-- transfer packet from actual layout
variable {h j n : ℕ}
abbrev slot (h j n : ℕ) := Fin (n+1)→Chunk h j
def bind (x y : Chunk h j) : Chunk h j :=
  ((y.1.1,other y.1.2 x.1.2),y.2)
def replace_ (x y : slot h j n) : slot h j n :=
  fun i => bind (x i) (y i)
@[simp] theorem retains (x y : Chunk h j) : bind x (bind x y)=y := by simp [bind]
def addRow (x : Triple (slot h j n)) := (x.1,replace_ x.1 x.2.1,x.2.2)
def plusRow : Equiv.Perm (Triple (slot h j n)) where
  toFun := addRow
  invFun := addRow
  left_inv := by rintro ⟨x,v,y⟩; simp [addRow]; funext i; exact retains ..
  right_inv := by rintro ⟨x,v,y⟩; simp [addRow]; funext i; exact retains ..
noncomputable section
abbrev net (x : slot h j n) := (baton h j n).cast x
theorem warp (x y : slot h j n) :
    let k := guide (net x) (net y)
    let b := touch k (other (heat (net y)) (heat (net x)))
    b=net (replace_ x y) := by
  dsimp only [touch,heat,guide]
  let v := fun (f : slot h j n) => net f
  have e (f:slot h j n) : (v f).1 = (f 0).1 := begins ..
  have z (f:slot h j n) (i:Fin n) : (v f).2.1 i=((f i.castSucc).2,(f i.succ).1) := correspond ..
  have d (f:slot h j n) : (v f).2.2=(f (Fin.last n)).2 := tails ..
  refine Prod.ext ?_ (Prod.ext (funext fun i=>?_) ?_)
  · change ((v y).1.1,other (v y).1.2 (v x).1.2)=(v _).1
    rw [e,e,e]; rfl
  · change ((v y).2.1 i |>.1,((v y).2.1 i).2.1,other _ ((v x).2.1 i).2.2)=(v _).2.1 i -- inferred other arg
    rw [z,z,z]; rfl
  change (v y).2.2=(v _).2.2; rw [d,d]; rfl

theorem portal (u : Equiv.Perm Pos) (x : Triple (slot h j n)) :
    (arrange u) (allThree net x) = allThree net (arrange u x) := by
  change mark _ = _
  refine Prod.ext (under ..) (Prod.ext (under ..) (under ..))
theorem rode (v : Triple (slot h j n)) (p : Equiv.Perm Pos) :
    (agent p move) (allThree net v)=allThree net ((agent p plusRow) v) := by
  suffices t : ∀ z:Triple (slot h j n), move (allThree net z) = allThree net (plusRow z) by
    unfold agent
    rw [Equiv.trans_apply,Equiv.trans_apply,portal,t,arrange_symm,portal]
    rfl
  rintro ⟨x,y,z⟩
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  exact warp _ _
theorem back (v : Triple (slot h j n)) (p : Equiv.Perm Pos) :
    (agent p move).symm (allThree net v) = allThree net ((agent p plusRow).symm v) := by
  obtain ⟨x,rfl⟩ := (agent p plusRow).surjective v
  rw [← rode,Equiv.symm_apply_apply,Equiv.symm_apply_apply]

def build0 (P G R S : Tape) (h j n : ℕ) : Adopt (layouts P G R S (chunks h j |> fun x => Loom.Track x (n+1))) (domeQ P G R S h j n) :=
  let b := baton h j n
  (Adopt.same _).split (b.split ((Adopt.same _).split (b.split ((Adopt.same _).split (b.split (Adopt.same _))))))
theorem appear {P G R S : Tape} (x : Dome P G R S (slot h j n)) (p : Equiv.Perm Pos) :
    let B := (build0 P G R S h j n).cast
    B.symm ((invoke (agent p move) _ _ _ _).symm (B x))=(invoke (agent p plusRow) _ _ _ _).symm x := by
  dsimp only
  rw [gone,gone,show peek _=allThree net (peek x) from rfl,back]
  let m := (agent p plusRow).symm (peek x)
  change (build0 P G R S h j n).cast.symm (wipe _ (allThree net m))=wipe x m
  apply (build0 P G R S h j n).cast.injective
  rw [Equiv.apply_symm_apply]
  rfl

variable {X : Type} (P G R S : X→Tape) (H L i : X→ℕ) {r : Regime X}
variable (hP : Told r P) (hG : Told r G) (hR : Told r R) (hS : Told r S)
variable (h0 : r.Has fun x=>signs (H x) (L x) (i x)) (c : r.Has (tally ∘ extent H L i))
variable (guard : ∀ x a,a∈P x++G x++R x++S x→a≤Net.Shuttle.base)
variable {l : X→ℕ}
variable (spar : ∀ x, (3*extent H L i x+1)*(32*i x)≤ 2^width (H x) (L x))
variable {U:X→Type} (u : (x:X)→Series (U x)) (z : ∀ x,(u x).count≤l x)

abbrev enable x := layouts (P x) (G x) (R x) (S x) (Loom.Track (chunks (H x) (L x)) (i x+1))
include hP hG hR hS h0 c z guard spar
theorem theme (q : Equiv.Perm Pos)
    (f : (x:X)→Dome (P x) (G x) (R x) (S x) (slot (H x) (L x) (i x))→U x→Bead) :
    let s := enable P G R S H L i
    Breeze (modes H L i) r (fun i=>(s i).count) l (together r.header (cloth s u f))
      (cloth s u fun x=> Strip.Optic.travel (invoke (agent q plusRow) ..) (f x)) := by
  let b x := build0 (P x) (G x) (R x) (S x) (H x) (L x) (i x)
  let v (x:X) := f x ∘ (b x).cast.symm
  have g := sealed P G R S H L i hP hG hR hS h0 c guard spar u z q v
  have e (x:X) : rate P G R S H L i x = (enable P G R S H L i x).count := (b x).cost.symm
  dsimp only
  simp_rw [← e]
  suffices a : cloth (Series0 P G R S H L i) u v=cloth (enable P G R S H L i) u f ∧
      cloth (Series0 P G R S H L i) u (fun x=> travel (invoke (agent q move) ..) (v x))
      = cloth (enable P G R S H L i) u (fun x=> travel (invoke (agent q plusRow) ..) (f x)) by
    unfold Sail at g
    change Breeze _ _ _ _ _ (cloth _ u (fun x => travel (invoke (agent q move) ..) (v x))) at g
    rw [a.1] at g
    erw [a.2] at g
    exact g
  constructor <;> funext x <;>
    change stripe _ _=stripe (enable P G R S H L i x) _ <;>
    erw [(b x).packet] <;>
    apply congrArg (stripe _) <;> funext a
  · change strip (u x) (f x ((b x).cast.symm ((b x).cast a)))=_
    rw [Equiv.symm_apply_apply]
  change strip (u x) (f x ((b x).cast.symm ((invoke (agent q move) ..).symm ((b x).cast a))))=_
  erw [appear a q]
  rfl
end
end Packed

end IntegerMultiplication
end Computability
end OAI
