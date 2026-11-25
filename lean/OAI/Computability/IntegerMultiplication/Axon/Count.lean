import OAI.Computability.IntegerMultiplication.Earth.Bolt
import OAI.Computability.IntegerMultiplication.Fourier.Line

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Axon
open Code Adic Packed Net Net.Walsh Strip.Dims Earth IntegerMultiplication.Fourier Loom
open Finset Matrix
variable {k : ℕ}
abbrev Face (k:ℕ) := Walsh.Addr (Fin k)
abbrev alpha (x:Face k) : List (Fin 2) := List.ofFn (fun i : Fin k => (x i : Fin 2))
private theorem alpha_length (x : Face k) : (alpha x).length = k := List.length_ofFn
private theorem alpha_getElem (x : Face k) (i : Fin k) :
    (alpha x)[i.val]'(by rw [alpha_length]; exact i.isLt) = x i := by
  have hh : i.val < (alpha x).length := by rw [alpha_length]; exact i.isLt
  unfold alpha
  exact List.getElem_ofFn hh
abbrev bold (x:Face k) := Adic.code (alpha x).reverse
abbrev light (x:Face k) := Adic.code (alpha x)
theorem shadow (x : Block 2 k) : alpha (layBit k x)=most x := by
  apply List.ext_getElem ((alpha_length _).trans (Adic.length x).symm)
  intro i hi hi'
  have hik : i < k := by rw [alpha_length] at hi; exact hi
  rw [show (alpha (layBit k x))[i] = (layBit k x) ⟨i,hik⟩ from alpha_getElem _ ⟨i,hik⟩]
  rfl
theorem bright (x : Block 2 k) : bold (layBit k x)=number x := by simp [bold,shadow,number,least]

abbrev crest (x:Face (k+1)) := x 0
abbrev stem (x:Face (k+1)) : Face k := fun i=> x i.succ
abbrev branch (x: (B × Face k)) : Face (k+1) := join x
theorem stem_b (x:B×Face k) : stem (branch x)=x.2 := funext fun i=> tail_j _ _ i
theorem crest_b (x:B×Face k) : crest (branch x)=x.1 := first_j _ _
theorem glow (x:Face (k+1)) : alpha x = (show Fin 2 from crest x) :: alpha (stem x) := List.ofFn_succ
abbrev pin (x : B) : ℕ := (x : Fin 2).val
theorem born (x:Face (k+1)) :
    bold x = 2^k*pin (crest x) + bold (stem x) := by
  have hlen : (alpha (stem x)).length = k := List.length_ofFn
  unfold bold
  rw [glow,List.reverse_cons,cat,List.length_reverse,hlen,code,code]
  simp [pin,Nat.add_comm]; rfl
theorem born_l (x : Face (k+1)) :
    light x = 2*light (stem x)+pin (crest x) := by
  unfold light; rw [glow,code,Nat.add_comm]; rfl
theorem vellum (x : Face k) : bold x < 2^k := by
  simpa only [bold, List.length_reverse, alpha_length] using Adic.limit (alpha x).reverse
def localV (x : Face k) : Spot (2^k) := ⟨bold x,vellum x⟩
theorem unique : Function.Bijective (localV (k:=k)) := by
  apply (Fintype.bijective_iff_injective_and_card ..).mpr
  constructor
  · intro a b t
    obtain ⟨a,rfl⟩ := (layBit k).surjective a
    obtain ⟨b,rfl⟩ := (layBit k).surjective b
    have e := congrArg Fin.val t
    change bold (layBit k a) = bold (layBit k b) at e
    rw [bright,bright] at e
    rw [Adic.number_inj _ _ e]
  simp only [Face,Walsh.Addr,Net.Tensor.Vec, Fintype.card_fun,Fintype.card_fin,B, Spot,ZMod.card]

noncomputable def localE (k) := Equiv.ofBijective (localV (k:=k)) unique
def refl_ (x : Face k) : Face k := x ∘ Fin.rev
theorem alpha_refl (x:Face k) : alpha (refl_ x)=(alpha x).reverse := by
  apply List.ext_getElem (by rw [alpha_length, List.length_reverse, alpha_length])
  intro i a b
  simp only [List.getElem_reverse]
  have ha : i < k := by rw [alpha_length] at a; exact a
  have hs : (alpha x).length - 1 - i < k := by rw [alpha_length]; omega
  have hrev : (alpha x).length - 1 - i < (alpha x).length := by
    have hl := alpha_length x
    omega
  rw [show (alpha (refl_ x))[i] = refl_ x ⟨i,ha⟩ from alpha_getElem _ ⟨i,ha⟩]
  rw [show (alpha x)[(alpha x).length - 1 - i]'hrev =
      x ⟨(alpha x).length - 1 - i,hs⟩ from alpha_getElem _ ⟨_,hs⟩]
  change x (Fin.rev ⟨i,ha⟩) = x ⟨(alpha x).length - 1 - i,hs⟩
  have hidx : (Fin.rev ⟨i,ha⟩ : Fin k) = ⟨(alpha x).length - 1 - i,hs⟩ := by
    apply Fin.ext
    dsimp [Fin.rev]
    have hl := alpha_length x
    omega
  exact congrArg x hidx
theorem shine (x:Face k) : light (refl_ x)=bold x := by
  unfold light; rw [alpha_refl]

-- suffix for phase
def beyond {k : ℕ} (x:Face k) (i:Fin k) : ℕ := bold x % 2^(k-(i.val+1))
theorem beyond_b (x : Face (k+1)) : beyond x 0=bold (stem x) := by
  unfold beyond
  simp only [Fin.val_zero,Nat.zero_add,Nat.add_sub_cancel_right]
  rw [born,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (vellum _)]
theorem beyond_s (x : Face (k+1)) (i:Fin k) : beyond x i.succ=beyond (stem x) i := by
  unfold beyond
  simp only [born,Fin.val_succ]
  have q : i.val < k := i.isLt
  let t := k-(i.val+1)
  rw [show k+1-(i.val+1+1)=t by unfold t; omega]
  have h : k=t+(i.val+1) := (Nat.sub_add_cancel q).symm
  have e : 2^k=2^t*2^(i.val+1) := by conv_lhs => rw [h,pow_add]
  rw [e,Nat.mul_assoc,Nat.mul_add_mod_self_left]
end Axon

end IntegerMultiplication
end Computability
end OAI
