import OAI.Computability.IntegerMultiplication.Packed.Completion
import OAI.Computability.IntegerMultiplication.Strip.Static

namespace OAI
namespace Computability
namespace IntegerMultiplication

set_option synthInstance.maxSize 5000
namespace Packed
open Strip Dims Code Adic Loom
variable {H L i : ℕ}
abbrev Wires := Triple (Fin 2)
def xor : Equiv.Perm Wires where
  toFun x := (x.1,other x.2.1 x.1,x.2.2)
  invFun x := (x.1,other x.2.1 x.1,x.2.2)
  left_inv p := by simp
  right_inv p := by simp
abbrev heat (x : Queue H L i) : Fin 2 := x.1.2
def touch (x : Queue H L i) (k : Fin 2) : Queue H L i :=
  ((x.1.1,k),x.2)
def allThree {K A : Type} (f : K→A) (x : Triple K) := (f x.1,f x.2.1,f x.2.2)
@[simp] theorem under {K A : Type} (v : Triple K) (f : K→A) (x : Pos) :
    note (allThree f v) x = f (note v x) := by cases x <;> rfl
def Fire (x : Plate H L i) :=
  (x.1,touch x.2.1 (other (heat x.2.1) (heat x.1)),x.2.2)
def streak : Equiv.Perm (Plate H L i) where
  toFun := Fire
  invFun := Fire
  left_inv i := by simp [Fire,touch,heat]
  right_inv i := by simp [Fire,touch,heat]

def forge (u : Equiv.Perm Wires) (x : Plate H L i) :=
  let v := u (allThree heat x)
  (touch x.1 v.1,touch x.2.1 v.2.1,touch x.2.2 v.2.2)
theorem forges (x : Plate H L i) :
    Fire x=forge xor x := rfl
@[simp]
private theorem onPos (x : Pos) (f : Equiv.Perm Wires) (p : Plate H L i) :
    note (forge f p) x = touch (note p x) (note (f (allThree heat p)) x) :=
  match x with
  | .sun | .noon | .moon => rfl
theorem commuted (x : Plate H L i) (u : Equiv.Perm Pos) (f : Equiv.Perm Wires) :
    arrange u (forge f x) = forge (agent u.symm f) ((arrange u) x) := by
  suffices h : note (arrange u (forge f x)) = note (forge (agent u.symm f) ((arrange u) x)) by
    simpa only [marked] using congrArg mark h
  have v (q : Pos) (u : Equiv.Perm Pos) {K : Type} (p : Triple K) :
      note ((arrange u) p) q= note p (u q) := by
    unfold arrange; simp
  funext q
  simp only [v,onPos,agent,Equiv.trans_apply,arrange_symm]
  apply congrArg _; change _ = note _ (u q); apply congrArg (fun x => note (f x) (u q)); symm
  apply (show Function.Injective (note (K:=Fin 2)) from fun x y p => by simpa only [marked] using congrArg mark p)
  funext p
  simp [v]
theorem agency (x : Plate H L i) (u : Equiv.Perm Pos) :
    (agent u streak).symm x=forge ((agent u xor).symm) x := by
  change (arrange u).symm (Fire (arrange u x))=_
  rw [forges]
  change arrange u.symm (forge xor (arrange u x))=_
  rw [commuted, show (arrange u.symm) (arrange u x)=x from Equiv.symm_apply_apply (arrange u) x]
  rfl -- inv of conjugate defeq?

abbrev Spare (H L i : ℕ) :=
  Pin (Adic.field 2 H) × (Fin i → Seg L H) × Tail L -- Unit omitted, from File product Unit after H
abbrev spore (H L i : ℕ) :=
  ((line 2 H).cart Series.one).cart ((Loom.Track (segments H L) i).cart (line 2 L))
abbrev rest (H L i : ℕ) :=
  (Pin (field 2 H) × Unit) × (Fin i→Seg L H) × Tail L
def fileDot (H L i : ℕ) : File (lineQ H L i) (Fin 2) (spore H L i) :=
  let a := File.unite (File.shade (line 2 H)) (File.look (Series.natural 2))
  let b := a.unite (File.shade ((Loom.Track (segments H L) i).cart (line 2 L)))
  b.selectCongr ((Equiv.prodPUnit (Unit × Fin 2)).trans (Equiv.punitProd _))
abbrev kept (P G R S : Tape) (H L i : ℕ) :=
  Pin P × rest H L i × Pin G × rest H L i × Pin R × rest H L i × Pin S
abbrev keel (P G R S : Tape) (H L i : ℕ) :=
  layouts P G R S (spore H L i)
def fileAcross (P G R S : Tape) (H L i : ℕ) : File (domeQ P G R S H L i) Wires (keel P G R S H L i) :=
  let q := fileDot H L i
  let m := (File.shade (layout P)).unite (q.unite ((File.shade (layout G)).unite (q.unite
    ((File.shade (layout R)).unite (q.unite (File.shade (layout S)))))))
  let t : (Unit × Fin 2 × Unit × Fin 2 × Unit × Fin 2 × Unit) ≃ Wires :=
    { toFun x := (x.2.1,x.2.2.2.1,x.2.2.2.2.2.1)
      invFun x := ((),x.1,(),x.2.1,(),x.2.2,())
      left_inv _ := rfl
      right_inv _ := rfl }
  m.selectCongr t
theorem matched {P G R S : Tape} (x : Dome P G R S (Queue H L i)) :
    Fix.slot (fileAcross ..) x = allThree heat (peek x) := rfl
theorem fed {P G R S : Tape} (x : Dome P G R S (Queue H L i)) (u : Equiv.Perm Pos) :
    (Strip.Optic.field (fileAcross ..).focus (agent u xor)).symm x =
      (invoke (agent u streak) P G R S).symm x := by
  rw [gone,agency]
  rfl

def front (i : Dim × Adic.Raw 2) := toll (cut i).1
theorem poly_front : Poly front :=
  poly_cut.fstCompose.compose facile_toll.poly
theorem detect (x : Queue H L i) :
    front (signs H L i,badge x)=heat x := by
  rw [front,peeled,lines]; simp only; rw [flag_word]; simp [heat,toll]

variable {X : Type} (P G R S : X→Tape) (H L i : X→ℕ) {r : Regime X}
variable (hP : Told r P) (hG : Told r G) (hR : Told r R) (hS : Told r S)
variable (h : r.Has fun x=>signs (H x) (L x) (i x)) (c : r.Has (tally ∘ extent H L i))
noncomputable section
include hP hG hR hS h c
theorem supervisor :
    Strip.Trace r (Series0 P G R S H L i) (fun _x a => send (allThree heat (peek a))) := by
  have v := inspect P G R H L i hP.station hG.station hR.station c S hS.station
  let D := Addr P G R S H L i
  let hat (x:X) (v:D x) := send (names (peek v))
  apply v.tune
  let rt := onboard r hat v.meter
  have a : rt.Has fun x:Sigma D=> names (peek x.2) := onboard_hat hat v.meter
  have E : rt.Has fun x:Sigma D=> signs (H x.1) (L x.1) (i x.1) :=
    onboard_small hat v.meter (send ∘ _) h
  let n := a.ez Easy.fst
  let m := (a.ez Easy.snd).ez Easy.fst
  let l := (a.ez Easy.snd).ez Easy.snd
  have u (x : (v:Sigma D)→Queue (H v.1) (L v.1) (i v.1))
      (g : rt.Has fun v => badge (x v)) :
      rt.Has fun v=>heat (x v) := by simpa only [detect] using (E.pair g).thenDo poly_front
  exact (u _ n).pair ((u _ m).pair (u _ l))

variable {l : X→ℕ} {U:X→Type} (u : (x:X)→Series (U x)) (z : ∀ x,(u x).count≤l x)
include z
set_option maxHeartbeats 1000000 in
theorem theory (p : Equiv.Perm Pos) :
    Action P G R S H L i (r:=r) (l:=l) u (fun _x=> agent p streak) := by
  intro f
  let q (x:X) := fileAcross (P x) (G x) (R x) (S x) (H x) (L x) (i x)
  have b :=
    letI : (x:X) → DecidableEq (Addr P G R S H L i x) := fun _=>Classical.decEq _
    letI : (x:X) → Fintype (Addr P G R S H L i x) := fun _=>inferInstance
    letI : (x:X) → Fintype (kept (P x) (G x) (R x) (S x) (H x) (L x) (i x)) := fun _=>inferInstance
    localAction q (agent p xor) _ (visible u f z) (supervisor P G R S H L i hP hG hR hS h c)
  have hx := Breeze.launch b (Spindle.belly _ Net.Motif.sigma_range.1.le :
    ∀ x, 1≤ Packed.modes H L i x)
  unfold  stackRun at hx -- then rewrite Optic
  unfold Strip.Optic.travel at *
  have e :
      (fun (a:X) (x:Addr P G R S H L i a)=> strip (u a)
        (f a ((Strip.Optic.field (q a).focus (agent p xor)).symm x))) =
        fun a x=> strip (u a) (f a ((invoke (agent p streak) ..).symm x)) := by
    funext a x
    apply congrArg _
    apply congrArg _
    exact fed _ _
  change Breeze _ _ _ _ _ (fun a=> stripe _ (fun x => strip _ (f a ((Strip.Optic.field (q a).focus (agent p xor)).symm x)))) at hx
  simp_rw [congrFun (congrFun e _) _] at hx -- need correct simp
  exact hx
end
end Packed

end IntegerMultiplication
end Computability
end OAI
