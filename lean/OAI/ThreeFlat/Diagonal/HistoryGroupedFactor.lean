import OAI.ThreeFlat.Diagonal.MotifHistoryStep
import OAI.ThreeFlat.Diagonal.HistoryAssembly
import OAI.ThreeFlat.Diagonal.MotifBinaryPacking

namespace OAI
/-! # Realizing the grouped site tensor by its occupied motif parties

Only motifs with a party at the selected site contribute. The internal edges
of one such motif are guessed privately, in its supplied edge order. Each
party receives old boundary pins, external boundary pins, or private bits,
through a fixed local port map.
-/

namespace ThreeFlat.Diagonal.MotifKernel

open LinearAlgebra.SpectralBooks HistoryContraction MotifBinaryPacking
open scoped Classical BigOperators

variable {M J E G F : Type} [Fintype M] [Fintype J] [Fintype E] [Fintype G] [DecidableEq G] [CommSemiring F]

abbrev Active (place : M → J → G) (v : G) := {m : M // ∃ j, place m j = v}

omit [Fintype G] in
theorem groupedFactor_empty (P : PortGraph J E) (place : J → G) {I : E → Type} [∀ e, Fintype (I e)]
    (K : ∀ j, P.State I j → F) (g : G) (b : WiresAt P.tail P.head place (I := I) none)
    (absent : ¬∃ j, place j = g) : groupedFactor P place K g b = 1 := by
  let : IsEmpty {j // place j = g} := ⟨fun j => absent ⟨j.val,j.property⟩⟩
  let : IsEmpty {e // wireOwner P.tail P.head place e = some g} := ⟨by
    rintro ⟨e,h⟩
    rw [wireOwner] at h
    split at h
    · exact absent ⟨P.tail e,Option.some.inj h⟩
    · contradiction⟩
  let : Unique (WiresAt P.tail P.head place (I := I) (some g)) := inferInstanceAs
    (Unique ((e : {e // wireOwner P.tail P.head place e = some g}) → I e))
  simp [groupedFactor]

omit [Fintype G] in
/-- Eliminate every absent motif before constructing the physical site tree. -/
theorem product_active (P : M → PortGraph J E) (place : M → J → G) {I : M → E → Type} [∀ m e, Fintype (I m e)]
    (K : ∀ m j, (P m).State (I m) j → F) (g : G) (b : ∀ m, WiresAt (P m).tail (P m).head (place m) (I := I m) none) :
    (∏ m, groupedFactor (P m) (place m) (K m) g (b m)) =
      ∏ m : Active place g, groupedFactor (P m.val) (place m.val) (K m.val) g (b m.val) := by
  let f (m : M) := groupedFactor (P m) (place m) (K m) g (b m)
  change (∏ m, f m) = ∏ m : {m // ∃ j, place m j = g}, f m.val
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun m => ∃ j, place m j = g) f]
  have gone : (∏ m : {m // ¬∃ j, place m j = g}, f m.val) = 1 :=
    Finset.prod_eq_one fun m _ => groupedFactor_empty _ _ _ _ _ m.property
  rw [gone,mul_one]

variable (P : PortGraph J E) (place : J → G) (v : G) (I : E → Type) [∀ e, Fintype (I e)]

abbrev Absorbed := {e // wireOwner P.tail P.head place e = some v}

/-- Compact allocation of the internal edge payloads of one motif at its
unique owner. Its labels may contain both selector and variable payload bits. -/
structure PrivateOrder where
  count : ℕ
  edge : Fin count ≃ Absorbed P place v
  width : E → ℕ
  binary : ∀ e, I e ≃ (Fin (width e) → Bool)

namespace PrivateOrder

variable {P place v I} (D : PrivateOrder P place v I)

def lengths (i : Fin D.count) := D.width (D.edge i).val

def bits := ∑ i, D.lengths i

def decode : (Fin D.bits → Bool) ≃ WiresAt P.tail P.head place (I:=I) (some v) :=
  (flatten D.lengths).symm.trans <| (Equiv.piCongrRight (fun i => (D.binary (D.edge i).val).symm)).trans
    (Equiv.piCongrLeft (fun a : Absorbed P place v => I a.val) D.edge)

omit [Fintype J] [Fintype E] [Fintype G] [(e : E) → Fintype (I e)] in
theorem packed_bit (x : Fin D.bits → Bool) (i : Fin D.count) (j : Fin (D.lengths i)) :
    D.binary (D.edge i).val (D.decode x (D.edge i)) j = x (finSigmaFinEquiv ⟨i,j⟩) := by
  let f := Equiv.piCongrLeft (fun a : Absorbed P place v => I a.val) D.edge
  let a (i : Fin D.count) := (D.binary (D.edge i).val).symm ((flatten D.lengths).symm x i)
  have eq := congrArg (fun q => q i) (f.symm_apply_apply a)
  change D.decode x (D.edge i) = a i at eq
  rw [eq]
  exact congrFun ((D.binary (D.edge i).val).apply_symm_apply _) j

end PrivateOrder

omit [Fintype G] in
/-- At one occupied motif a single ordered glue sums its absorbed private
wires, while each constituent party independently runs its LUT network. -/
theorem group_network {p c : ℕ} (D : PrivateOrder P place v I)
    (ord : Fin c ≃ {j // place j = v}) (arity : Fin c → ℕ) (N : ∀ i, BitNetwork F (arity i))
    (wire : ∀ i, Fin (arity i) → BitSource D.bits p) (pin : Fin p → Bool)
    (b : WiresAt P.tail P.head place (I:=I) none) (K : ∀ j, P.State I j → F)
    (party : ∀ i x, (N i).eval (fun j => (wire i j).read x pin) = K (ord i).val
      (portAt P (ord i) (atParty P.tail P.head place (ord i) b ((ord i).property.symm ▸ D.decode x)))) :
    (BitNetwork.Ordered.glue N wire).eval pin = groupedFactor P place K v b := by
  rw [BitNetwork.Ordered.glue_eval,groupedFactor]
  apply Fintype.sum_equiv D.decode
  intro x
  apply Fintype.prod_equiv ord
  intro i
  exact party i x

end ThreeFlat.Diagonal.MotifKernel

end OAI
