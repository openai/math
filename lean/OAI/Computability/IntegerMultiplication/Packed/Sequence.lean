import OAI.Computability.IntegerMultiplication.Packed.Dance

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Adic Strip Dims Loom IntegerMultiplication.Port
variable {H L i : ℕ}
abbrev cap (n w u : ℕ) := (n+1)*width w u
-- maybe cap ordering avoid Loom.Where.cap
abbrev Span (R : Type) (i : ℕ) := Fin i → R -- Span collision open Port
def sumSeq {R : Type} [CommRing R] (H L : ℕ) : (i : ℕ) → Span R i → R
| 0,_ => 0
| i+1,v => ((2^(i*width H L):ℕ):R)*v 0+sumSeq H L i (fun j => v j.succ)
theorem combine {R : Type} [CommRing R] (a b : Span R i) :
    sumSeq H L i (a+b)=sumSeq H L i a+sumSeq H L i b := by
  induction i with
  | zero => simp [sumSeq]
  | succ i ih =>
    simp only [sumSeq]
    rw [Pi.add_apply, left_distrib, show (fun (j:Fin i) => (a+b) j.succ)=(fun j=>a j.succ)+(fun j=>b j.succ) from rfl,
       ih]; ring
theorem liftSeq {R : Type} [CommRing R] (v : Span ℤ i) :
    sumSeq H L i (fun j => (v j:R))=(sumSeq H L i v : ℤ) := by
  induction i with
  | zero => simp [sumSeq]
  | succ i ih => simp only [sumSeq]; rw [ih]; push_cast; rfl
noncomputable section
def totient (z : Seg L H) : ℤ := (number ((furrow H L).cast z):ℕ)
theorem parity (z : Seg L H) :
    totient z=2*(number (guard H L z):ℤ)+z.2.2.val := by
  unfold totient; rw [furrow_n]; push_cast; rfl
def small (H L : ℕ) (x : ℤ) := 0≤x ∧ x<(2^(width H L):ℕ)

theorem represent (v : ℤ) (h : small H L v) :
    ∃ z : Seg L H, totient z=v := by
  have i : NeZero (2^(width H L)) := inferInstance
  have g : v.toNat < 2^(width H L) := by obtain ⟨a,b⟩ := h; omega
  let a := (index 2 (width H L)).symm (v.toNat:ZMod (2^width H L))
  refine ⟨(furrow H L).cast.symm a,?_⟩
  have a0 := h.1
  unfold totient a
  rw [Equiv.apply_symm_apply,Adic.decode,ZMod.val_natCast_of_lt g]; omega

theorem unique : Function.Injective (totient (H:=H) (L:=L)) :=
  fun x y h => (furrow H L).cast.injective (number_inj 2 (width H L) (by unfold totient at h; exact_mod_cast h))

theorem echo_repr {R : Type} [CommRing R] (v : Fin i→Seg L H) :
    (number ((wound 2 (width H L) (segments H L) (furrow H L) i).cast v):R) =
      sumSeq H L i (fun j => (totient (v j):R)) := by
  induction i with
  | zero => rw [wind_naught]; simp [sumSeq]
  | succ i ih =>
    rw [wind,sumSeq]
    rw [Nat.cast_add,Nat.cast_mul,ih]
    unfold totient
    push_cast
    rfl

abbrev Omega (H L i : ℕ) := Tower 2 (cap i H L)
def flight (x : Queue H L i) := index 2 (cap i H L) ((package H L i).cast x)
def plane : Queue H L i ≃ Omega H L i := (package H L i).cast.trans (index 2 (cap i H L))
def offsets (v : Span ℤ i) : Omega H L i :=
  (↑(2^L:ℕ):Omega H L i)*(sumSeq H L i v:ℤ)
@[simp] theorem flown (x : Queue H L i) : plane x=flight x := rfl

theorem drift (x : Queue H L i) (y : Span (Seg L H) i) (v : Span ℤ i)
    (agreement : ∀ j,totient (y j)=totient (x.2.1 j)+v j) :
    plane (show Queue H L i from (x.1,y,x.2.2)) =
      plane x+offsets v := by
  simp only [flown,flight, Adic.idx_nat,packed,Nat.cast_add,Nat.cast_mul,echo_repr,agreement,
    Int.cast_add, offsets,← liftSeq]
  let a (j : Fin i) : Omega H L i := (totient (x.2.1 j):ℤ)
  let b (j : Fin i) : Omega H L i := (v j:ℤ)
  have hh := combine (H:=H) (L:=L) a b
  change sumSeq (R:=Omega H L i) H L i (fun j => ↑(totient (x.2.1 j))+↑(v j))=_+_ at hh
  rw [hh]; ring

def slide (v : Span ℤ i) : Queue H L i ≃ Queue H L i :=
  plane.trans ((Equiv.addRight (offsets v)).trans plane.symm)
theorem dress (x : Queue H L i) (y : Span (Seg L H) i) (v : Span ℤ i)
    (agreement : ∀ j,totient (y j)=totient (x.2.1 j)+v j) :
    slide v x = (x.1,y,x.2.2) := by
  apply plane.injective
  rw [drift x y v agreement]
  rw [slide,Equiv.trans_apply,Equiv.trans_apply,Equiv.apply_symm_apply]; rfl
end
end Packed

end IntegerMultiplication
end Computability
end OAI
