import OAI.Computability.IntegerMultiplication.Packed.Route

namespace OAI
namespace Computability
namespace IntegerMultiplication

set_option synthInstance.maxSize 1000
namespace Packed
open Strip Dims Loom Code _root_.OAI.Computability.IntegerMultiplication.Fix Strip.Optic
variable (P G R S : Tape) {K : Type} (k : Series K)
variable [DecidableEq K]
abbrev Apart := Pin P × Unit × Pin G × Unit × Pin R × Unit × Pin S
abbrev closet := (layout P).cart (Series.one.cart ((layout G).cart (Series.one.cart ((layout R).cart
  (Series.one.cart (layout S))))))
def close : File (layouts P G R S k) (Triple K) (closet P G R S) :=
  let H := File.look k
  let g := (File.shade (layout P)).unite (H.unite ((File.shade (layout G)).unite (H.unite
    ((File.shade (layout R)).unite (H.unite (File.shade (layout S)))))))
  let t : (Unit × K × Unit × K × Unit × K × Unit) ≃ Triple K :=
    { toFun x := (x.2.1,x.2.2.2.1,x.2.2.2.2.2.1)
      invFun x := ((),x.1,(),x.2.1,(),x.2.2,())
      left_inv _ := rfl
      right_inv _ := rfl }
  g.selectCongr t
theorem faces (x : Dome P G R S K) : slot (close P G R S k) x=peek x := rfl
theorem faithful (p : Equiv.Perm (Triple K)) :
    field (close P G R S k).focus p = invoke p _ _ _ _ := rfl

variable {X : Type} (P G R S : X→Tape) (H L i : X→ℕ) {r : Regime X}
variable (hP : Told r P) (hG : Told r G) (hR : Told r R) (hS : Told r S)
variable (h : r.Has fun x=>signs (H x) (L x) (i x)) (c : r.Has (tally ∘ extent H L i))
variable {l : X→ℕ}
variable (spar : ∀ x, (3*extent H L i x+1)*(32*i x)≤ 2^width (H x) (L x))
variable {U:X→Type} (u : (x:X)→Series (U x)) (z : ∀ x,(u x).count≤l x)
noncomputable section
open Pos
include hP hG hR hS h c
-- trace tunes names arranged by Enum q
omit hP hG hR hS h c in
private theorem turn_easy {A : Type} [Codec A] (q : Equiv.Perm Pos) :
    Easy (arrange (K:=A) q : Triple A → Triple A) := by
  have h (i : Pos) : Easy (fun x : Triple A => note x i) := by
    cases i <;> unfold note <;> fun_prop
  exact (h (q Pos.sun)).pair ((h (q Pos.noon)).pair (h (q Pos.moon)))
omit h in
theorem bypass (q0 : Equiv.Perm Pos) :
    Strip.Trace r (Series0 P G R S H L i)
      (fun _x v => send (names (arrange q0 (peek v)))) := by
  have m := inspect P G R H L i hP.station hG.station hR.station c S hS.station
  let D := Addr P G R S H L i
  let label (x:X) (i:D x) := send (names (peek i))
  apply m.tune
  let rt := onboard r label m.meter
  have v : rt.Has (fun w:Sigma D => names (peek w.2)) := onboard_hat label m.meter
  have eq (x) (i:D x) : names (arrange q0 (peek i))=arrange q0 (names (peek i)) := by
    let t := peek i
    have e (j : Pos) : badge (note t j)=note (names t) j := by cases j <;> rfl
    exact Prod.ext (e _) (Prod.ext (e _) (e _))
  simp_rw [eq]
  exact v.ez (turn_easy q0) -- included crap?
include z spar
variable (f : (x:X)→Addr P G R S H L i x→U x→Bead)
attribute [local irreducible] repair

set_option maxHeartbeats 400000 in
theorem shower (q0 : Equiv.Perm Pos) :
    let A := Series0 P G R S H L i
    Drive r (rate P G R S H L i) l (cloth A u f) (cloth A u
      fun x=> travel (invoke (agent q0 repair) ..) (f x)) := by
  let g (x:X) := (close (P x) (G x) (R x) (S x) (lineQ (H x) (L x) (i x))).selectCongr (arrange q0)
  let a := fun (x:X) (p:Addr P G R S H L i x) => slot (g x) p
  have eq (x:X) (p:Addr P G R S H L i x) : a x p=arrange q0 (peek p) := rfl
  have v := bypass P G R S H L i hP hG hR hS c q0
  let D := Addr P G R S H L i
  let hat (x:X) (i:D x) := send (names (a x i))
  let hs0 : Strip.Trace r (Series0 P G R S H L i) hat := v
  let rt := onboard r hat hs0.meter
  let V (x:Sigma D) := a x.1 x.2
  have e : rt.Has fun x:Sigma D=>names (V x) := onboard_hat hat hs0.meter
  have E : rt.Has fun x:Sigma D => signs (H x.1) (L x.1) (i x.1) :=
    onboard_small hat hs0.meter (send ∘ _) h
  let iden (x:X) := emblem ∘ (names : Plate (H x) (L x) (i x) → _)
  have x0 :=
    Strip.Trace.tune (m:=fun (x:X) (y:D x) => send (sheet (g x) spotted (iden x ∘ repair) y)) hs0 (send0 (H:=fun x:Sigma D=>H x.1) (L:=fun x:Sigma D=>L x.1) (i:=fun x:Sigma D=>i x.1) E V e)
  have x1 :=
    Strip.Trace.tune (m:=fun (x:X) (y:D x) => send (sheet (g x) spotted (iden x) y)) hs0 (send1 (H:=fun x:Sigma D=>H x.1) (L:=fun x:Sigma D=>L x.1) (i:=fun x:Sigma D=>i x.1) E V e)
  have m := hs0.valid
  have hv := cloth_size _ _ m f z
  let H0 := extent H L i
  have vP :=
    Drive.fetch m.1 hv
  let f0 := (fun (x:X) (i:D x) => (u x).tab (f x i))
  let s0 := Series0 P G R S H L i
  let Q0 := cloth s0 u f
  have V0 : Drive r (fun i=>(s0 i).count) l Q0 (stackRun s0 fun x y => send (f0 x y)) := by
    have ht := Drive.self m.1 hv
    suffices t : stackRun s0 (fun x y=>send (f0 x y))=Q0 from t.symm ▸ ht -- ht type malign; simp
    unfold Q0 cloth stackRun; funext i; apply congrArg (stripe _); funext x; exact (stripe_eq' ..).symm
  let E0 := fun x:X => Queue (H x) (L x) (i x)
  have p :=
    letI : (x:X)→DecidableEq (Plate (H x) (L x) (i x)) := fun _=>inferInstance
    letI : (x:X)→DecidableEq (Addr P G R S H L i x) := fun _=> Classical.decEq _
    letI : (x:X)→Fintype (Addr P G R S H L i x) := fun _=>inferInstance
    letI : (x:X)→Fintype (Plate (H x) (L x) (i x)) := fun _=>inferInstance
    letI : (x:X)→Fintype (Apart (P x) (G x) (R x) (S x)) := fun _=>inferInstance
    Palace g (fun _=>repair) (fun _=>spotted) iden (fun _=>identify)
    f0 (fun _=>valid_repair)
    (d:=fun x => 3*H0 x) (fun _ i=> size_key i)
    V0 (vP.chain (x0.offer.monoSize (fun _=>le_rfl) (fun _=>Nat.zero_le _))) (vP.chain
      (x1.offer.monoSize (fun _=>le_rfl) (fun _=>Nat.zero_le _)))
    (fun _=>le_rfl) (by
      have vt : Dom r.scale H0 :=
        (Regime.Small.extent (k:=fun i=>send (tally (H0 i))) (r:=r) c).mono
          (fun i=>by change _≤ size (tally (H0 i)); rw [size_tally,tally_length]; omega)
      exact (Dom.const _ 3).mul vt)
    3 (fun x y => by
      have exp := bulk (u x) (f x y)
      simp only [Loom.strip,stripe_eq'] at exp
      change (send ((u x).tab (f x y))).count ≤ _
      specialize z x; omega)
    (by
      refine ⟨1,fun x=> ?_⟩
      have z := @spotted_rate (H x) (L x) (i x)
      rw [Nat.one_mul]
      apply Nat.le_of_mul_le_mul_right (c:=2^width (H x) (L x))
      rw [Nat.mul_assoc]
      calc
       _ ≤ (3*H0 x+1)*((32*i x)*_) := Nat.mul_le_mul_left _ z
       _ ≤ _ := by
        change _ ≤ Fintype.card (Plate (H x) (L x) (i x)) * _
        rw [← Nat.mul_assoc,Nat.mul_comm (Fintype.card _)]
        exact Nat.mul_le_mul_right _ (spar x)
      exact pow_pos (by decide) _)
  unfold stackRun at p
  -- transport invoke = field g rotation
  change Drive r _ l _ (fun x => stripe _ (fun y => strip _ (travel (invoke ..) (f x) y)))
  simp only [Loom.strip,stripe_eq']
  -- use p
  simp only [stripe_eq'] at p
  exact p -- field.selectCongr op defeq
end
end Packed

end IntegerMultiplication
end Computability
end OAI
