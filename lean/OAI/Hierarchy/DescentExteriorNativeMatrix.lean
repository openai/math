import OAI.Hierarchy.DescentExteriorMatrixROM
import OAI.Hierarchy.DescentExteriorCoefficient

namespace OAI
/-! # Installing the computed cumulative matrix and running the exterior checker -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentExteriorMatrixUpdate DescentGL Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {w e j r t h : ℕ}
local notation "k" => j+(j+r)
local notation "H" => span j r t e
local notation "n" => e*2^(j+r)

theorem install_image (origin : ℕ) (P M : Fin e→Layout k) (x : Fin e→Plane j r→Fin t→Bool)
    (z : Hidden e j r t→Bool) (op : Expr) (m after : Memory w) (was : Loaded origin P x z m)
    (written : after=image (origin+H) e op m)
    (trueCode : ∀i:Fin e,after (origin+H+i.val)=((matrixCode (M i)).val:Word w)) :
    Loaded origin M x z after := by
  have room : e≤H := (Nat.le_mul_of_pos_right e (Nat.two_pow_pos (j+r))).trans (row_room j r t e)
  apply install origin M P x z m after was
  · intro i neq u bound
    have ne : i.val≠1:=fun he=>neq (Fin.ext he)
    by_cases low : i.val=0
    · have loc : (bank j r t e origin i.val).base+u<origin+H := by simp [bank,low,bound]
      simp [written,ProtocolRAM.image,fillSegment,Nat.not_le_of_gt loc]
    · have next : 2*H≤ i.val*H := Nat.mul_le_mul_right H (by omega)
      have loc : origin+H+e≤(bank j r t e origin i.val).base+u := by change _≤origin+i.val*H+u;omega
      simp [written,ProtocolRAM.image,fillSegment,Nat.not_lt_of_ge loc]
  · intro u hu
    change after (origin+1*H+u)=_
    rw [one_mul]
    by_cases live : u<e
    · simpa [padWord,live] using trueCode ⟨u,live⟩
    · have unchanged : after (origin+H+u)=m (origin+H+u) := by
        simp [written,ProtocolRAM.image,fillSegment,show ¬(origin+H+u<origin+H+e) by omega]
      rw [unchanged]
      simpa [bank,columnWords,padWord,live] using was 1 u hu

def composed (w j r t e h origin romBase : ℕ) (a b : Bank) : Procedure w :=
  (scan w (origin+span j r t e) e (phase a b (offsetBank romBase (j+(j+r)))
      (tableBank romBase (j+(j+r)) h))).seq (service w j r t e origin)

attribute [local irreducible] CheapCode Procedure.seq scan service serviceMemory Loaded Receipt

set_option maxHeartbeats 600000 in
theorem run_composed (origin romBase : ℕ) (a b : Bank) (fa : a.Fits w (origin+H))
    (fb : b.Fits w (origin+H)) (na : e≤a.size) (nb : e≤b.size) (gap : romBase+2^(k*k)+2^(k*k)*2^(h*h)≤origin+H)
    (wordPos : 0<w) (room : 2^j*t≤w) (space : origin+22*H<2^w)
    (ext : Layout h→Layout k) (prev : Fin e→Layout k) (localStep : Fin e→Layout h) (printed : Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) :
    (composed w j r t e h origin romBase a b).Spec (fun m=>
      Loaded origin printed x z m ∧
      (∀i:Fin e,m (a.base+i.val)=((matrixCode (prev i)).val:Word w)) ∧
      (∀i:Fin e,m (b.base+i.val)=((matrixCode (localStep i)).val:Word w)) ∧
      (∀i:Fin (2^(k*k)+2^(k*k)*2^(h*h)),m (romBase+i.val)=rom ext i))
      (fun m dst=>dst=serviceMemory (j:=j) (r:=r) (t:=t) (e:=e) origin
        (image (origin+H) e (phase a b (offsetBank romBase k) (tableBank romBase k h)) m) ∧
        Receipt origin (fun i=>(prev i).trans (ext (localStep i))) x z dst)
      (20+54*e+364*n) ∧ CheapCode (composed w j r t e h origin romBase a b) := by
  have eFits : e≤H := (Nat.le_mul_of_pos_right e (Nat.two_pow_pos (j+r))).trans (row_room j r t e)
  let combined:=fun i=>(prev i).trans (ext (localStep i))
  let first:=scan w (origin+H) e (phase a b (offsetBank romBase k) (tableBank romBase k h))
  let last:=service w j r t e origin
  obtain ⟨code,cheapCode⟩:=run_mounted romBase (origin+H) ext prev localStep a b fa fb na nb gap (by omega)
  obtain ⟨flight,cheapFlight⟩:=native_exact origin wordPos room space combined x z
  have prep : first.Spec (fun m=>Loaded origin printed x z m ∧
      (∀i:Fin e,m (a.base+i.val)=((matrixCode (prev i)).val:Word w)) ∧
      (∀i:Fin e,m (b.base+i.val)=((matrixCode (localStep i)).val:Word w)) ∧
      (∀i:Fin (2^(k*k)+2^(k*k)*2^(h*h)),m (romBase+i.val)=rom ext i))
      (fun m after=>after=image (origin+H) e (phase a b (offsetBank romBase k) (tableBank romBase k h)) m ∧
        Loaded origin combined x z after) (4+54*e) := by
    intro P R T machine pc reg pub exit inst «public» cfg m atpc data
    obtain ⟨cnt,tick,done,out,ran,stop,img,correct⟩:=code machine pc reg pub exit inst «public» cfg m atpc data.2
    exact ⟨cnt,tick,done,out,ran,stop,img,install_image origin printed combined x z _ m out data.1 img correct⟩
  change _ ∧ CheapCode (first.seq last)
  refine ⟨?_,@cheap_seq w first last (@cheapCode) (@cheapFlight)⟩
  refine @Procedure.Spec.mono w (first.seq last) _ _ _ _ ((4+54*e)+(16+364*n)) (20+54*e+364*n)
    (@Procedure.Spec.seq w first last _ (Loaded origin combined x z) _ _ (4+54*e) (16+364*n)
      (@prep) (@flight) (fun _ _ h=>h.2)) (fun _ h=>h) ?_ (by omega)
  rintro m dst ⟨tmp,⟨eq,_⟩,endAt,rr⟩
  exact ⟨endAt.trans (congrArg (serviceMemory (j:=j) (r:=r) (t:=t) (e:=e) origin) eq),rr⟩

end
end Hierarchy.DescentExteriorShelf

end OAI
