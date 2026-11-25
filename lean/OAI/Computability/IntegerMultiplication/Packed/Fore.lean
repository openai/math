import OAI.Computability.IntegerMultiplication.Strip.Index
import OAI.Computability.IntegerMultiplication.Packed.Badger

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Strip Code Dims Adic Loom
variable {P G R S : Tape} {H L i : ℕ} {A : Type}
abbrev fore (P G R : Tape) (Q : Type) := Pin P × Q × Pin G × Q × Pin R
abbrev foreOrder (P G R : Tape) {Q : Type} (s : Series Q) :=
  (layout P).cart (s.cart ((layout G).cart (s.cart (layout R))))
def eye (v : fore P G R A) := (v.2.1,v.2.2.2.1)
def fors (v : Dome P G R S A) : fore P G R A :=
  (v.1,v.2.1,v.2.2.1,v.2.2.2.1,v.2.2.2.2.1)
def joinD {A : Type} (q : Series A) (P G R S : Tape) :
    Adopt (layouts P G R S q) ((foreOrder P G R q).cart (q.cart (layout S))) :=
  let t := layout P; let v := layout G; let g := layout R
  let h := q.cart (layout S)
  let e := (Adopt.rotate q g h).back
  let z := ((Adopt.same v).split e).thenDo (Adopt.rotate v (q.cart g) h).back
  let d := ((Adopt.same q).split z).thenDo (Adopt.rotate q (v.cart (q.cart g)) h).back
  ((Adopt.same _).split d).thenDo (Adopt.rotate t _ h).back
@[simp] theorem join_to (q : Series A) (v : Dome P G R S A) :
    (joinD q P G R S).cast v=(fors v,v.2.2.2.2.2) := rfl
@[simp] theorem join_back (q : Series A) (v : fore P G R A) (t : A) (s : Pin S) :
    (joinD q P G R S).cast.symm (v,t,s)=(v.1,v.2.1,v.2.2.1,v.2.2.2.1,v.2.2.2.2,t,s) := rfl

variable {X : Type} (P G R : X→Tape) (H L i : X→ℕ) {r : Regime X}
variable (hP : Station r (fun x => layout (P x))) (hG : Station r (fun x => layout (G x)))
    (hR : Station r (fun x => layout (R x)))
variable (d : r.Has (fun x => tally (cap (i x) (H x) (L x))))

include d
abbrev Qt i0 := lineQ (H i0) (L i0) (i i0)
abbrev extent i0 := cap (i i0) (H i0) (L i0)

theorem initiative :
    Strip.Trace r (Qt H L i) (fun _x a => send (badge a)) := by
  let v := fun x => line 2 (cap (i x) (H x) (L x))
  have e := terminal (p:=2) (by decide) (extent H L i) d
  have z : Strip.Trace r v (fun _ a => send (least a)) := by
    obtain ⟨C,E⟩ : ∃ C:ℕ,∀ a:Fin 2,size a+1 ≤ C :=
      ⟨∑ a:Fin 2,(size a+1),fun a => Finset.single_le_sum (f:=fun a:Fin 2 => size a+1) (fun _ _=>Nat.zero_le _) (Finset.mem_univ a)⟩
    have hd : Dom r.scale (extent H L i) := (Regime.Small.extent (k:=fun x => send (tally (extent H L i x))) (r:=r) d).mono
      (fun x => by change _ ≤ size (tally _); rw [size_tally,tally_length]; omega)
    let T := fun x:X=>Block 2 (extent H L i x)
    refine ⟨e, ((Dom.const _ C).mul (hd.map (Sigma.fst:Sigma T→X)) |>.add (Dom.const _ 1)).mono ?_,
      Adic.marked (p:=2) (by decide) (extent H L i) d (fun x => (lineSize ..).ge)⟩
    intro x; change size _ ≤ C*_+1; simpa only [length'] using raw_size 2 C E (least x.2)
  exact z.via (fun x => package _ _ _)

omit d in
private theorem tells {I Y Z : Type} [Codec Y] [Codec Z] {A:I→Type} {r:Regime I} {s : (i:I)→Series (A i)}
    (m : (i:I)→A i→Y) (h : Strip.Trace r s (fun i a => send (m i a)))
    (f : Y → Z) (u : Easy f) :
    Strip.Trace r s (fun i a => send (f (m i a))) :=
  h.tune (Regime.Has.ez (r:=onboard r (fun i a => send (m i a)) h.meter) (onboard_hat (r:=r) (fun i a => send (m i a)) h.meter : Regime.Has (onboard r (fun i a => send (m i a)) h.meter) (fun x => m x.1 x.2)) u)
include hP hG hR
theorem scout : Strip.Trace r (fun x => foreOrder (P x) (G x) (R x) (Qt H L i x))
    (fun _x a => send (badge (eye a).1,badge (eye a).2)) := by
  have t := initiative H L i d
  let y (s : Tree) := s
  have a := (Trace.always hP (.atom false)).product
    (t.product ((Trace.always hG (.atom false)).product (t.product (Trace.always hR (.atom false)))))
  let U := Raw 2
  let m := fun x:X => fore (P x) (G x) (R x) (Queue (H x) (L x) (i x))
  exact tells (fun i (v:m i) => (false,badge v.2.1,false,badge v.2.2.2.1,false)) a
    (fun (a:Bool × U × Bool × U × Bool) => (a.2.1,a.2.2.2.1)) (by fun_prop)

theorem inspect (S : X→Tape) (g : Station r (fun x=>layout (S x))) :
    Strip.Trace r (Series0 P G R S H L i) (fun _x v => send (names (peek v))) := by
  have a := scout P G R H L i hP hG hR d
  have b := (initiative H L i d).product (Trace.always g (send false))
  have h := a.product b
  have j := h.via (fun x => joinD (Qt H L i x) _ _ _ _)
  let V := Addr P G R S H L i
  let T := Raw 2
  exact tells (fun i (v:V i) => ((badge (peek v).1,badge (peek v).2.1),badge (peek v).2.2,false)) j
    (fun (p : (T×T) × T×Bool) => (p.1.1,p.1.2,p.2.1)) (by fun_prop)
end Packed

end IntegerMultiplication
end Computability
end OAI
