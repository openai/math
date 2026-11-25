import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.Diagonal.AlphabetCode

section
/-! # Locality at stations and junctions of a subdivided graph -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} [Field F] {a b : Wire} (G : Diagram F a b)
  {x x' : Val a} {y y' : Val b} {s s' : G.End → Bool}

theorem station_local (v : G.V) (hs : ∀ e, G.station e = v → s e = s' e) :
    G.normalized.vertex x y s (.inl v) = G.normalized.vertex x' y' s' (.inl v) := by
  unfold vertex
  apply congrArg₂ (G.table v).2.2
  · apply congrArg (bits (G.table v).1).symm
    funext i
    exact hs (.inl (G.src ⟨v, i⟩)) (congrArg Sigma.fst (G.src.symm_apply_apply _))
  · apply congrArg (bits (G.table v).2.1).symm
    funext i
    exact hs (.inr (G.dst ⟨v, i⟩)) (congrArg Sigma.fst (G.dst.symm_apply_apply _))

theorem junction_local (v : G.Joint)
    (hx : ∀ i, Sum.inl i = v → bits a x i = bits a x' i)
    (hy : ∀ j, Sum.inr (.inl j) = v → bits b y j = bits b y' j)
    (hs : ∀ e, G.junction e = v → s e = s' e) :
    G.normalized.vertex x y s (.inr v) = G.normalized.vertex x' y' s' (.inr v) := by
  let f (a b : Bool) : F := if a = b then 1 else 0
  rcases v with i|j|e
  · exact congrArg₂ f (hx i rfl) (hs (.inl (.inl i)) rfl)
  · exact congrArg₂ f (hs (.inr (.inl j)) rfl) (hy j rfl)
  · exact congrArg₂ f (hs (.inr (.inr e)) rfl) (hs (.inl (.inr e)) rfl)

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-! # Shared and private symbols of a reported contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

open Spectral
variable {F : Type} [Field F] {n h d r : ℕ} (A : Expansion F n h)
  (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d)

abbrev Edge (n r d h : ℕ) := (Position n r d h × Bool) ⊕ Class r

def owner (x : Label n r) : Worker r :=
  if x R.1 ∈ A.reportGroups N R then .station (x (other hn R.1)) else .home (x R.1)

def endpoint (p : Position n r d h) (b : Bool) : Label n r :=
  corner p.1.1 (if b then Cube.flip Finset.univ p.2.1 else p.2.1)

def src : Edge n r d h → Worker r
  | .inl (p, b) => A.owner hn N R (endpoint p b)
  | .inr c => if A.shared N R c then .home c.1 else .packet c.2.2

def dst : Edge n r d h → Worker r
  | .inl (p, b) =>
    let c := packetClass hn R.1 p.1
    if A.shared N R c then A.owner hn N R (endpoint p b) else .packet c.2.2
  | .inr c => if A.shared N R c then .home c.2.1 else .packet c.2.2

def size : Edge n r d h → ℕ
  | .inl _ => 1
  | .inr c => A.classWidth R c

abbrev symbol : Edge n r d h → Type
  | .inl _ => Bool
  | .inr c => A.Alphabet hn N R c

open Classical in
instance symbolFintype : (e : Edge n r d h) → Fintype (A.symbol hn N R e)
  | .inl _ => inferInstanceAs (Fintype Bool)
  | .inr c => inferInstanceAs (Fintype (A.Alphabet hn N R c))

abbrev Assignment := (e : Edge n r d h) → A.symbol hn N R e

def rows {hn : 2 ≤ n} {N : ℕ} {R : A.Report r d} (a : A.Assignment hn N R) (b : Bool) :
    Packet n r d → Block n h := fun p i => a (.inl ((p, i), b))

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

section
/-!
# Sizes of worker templates

Projecting the vertex labels to any one coordinate preserves the
density bound. The two endpoints of the padded slots are exactly
uniform in each coordinate, so the same estimate covers padding pins.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Finset Spectral
variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b}
  {n r d h M : ℕ} (L : Layout G n r h)

theorem project_bound {V : Type} [Fintype V] (f : V → Label n r)
    (hv : ∀ z, multiplicity f z * r ^ n ≤ M)
    (i : Fin n) (g : Fin r) :
    multiplicity (fun v => f v i) g * r ≤ M := by
  classical
  let Z := {z : Label n r // z i = g}
  let e : {v // f v i = g} ≃ (Σ z : Z, {v // f v = z.val}) :=
    { toFun := fun v => ⟨⟨f v.val, v.property⟩, v.val, rfl⟩
      invFun := fun p => ⟨p.2.val, by rw [p.2.property, p.1.property]⟩
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨z, hz⟩, v, hv⟩; change f v = z at hv; subst z; rfl }
  have he : multiplicity (fun v => f v i) g = ∑ z : Z, multiplicity f z.val := by
    unfold multiplicity
    rw [Fintype.card_congr e, Fintype.card_sigma]
  have hz : Fintype.card Z * r = r ^ n := label_uniform i g
  apply Nat.le_of_mul_le_mul_right (c := r ^ n) _ (pow_pos (Fin.pos g) _)
  calc
    _ = (∑ z : Z, multiplicity f z.val * r ^ n) * r := by rw [he, ← sum_mul, mul_right_comm]
    _ ≤ (∑ _z : Z, M) * r := Nat.mul_le_mul_right r (sum_le_sum fun z _ => hv z.val)
    _ = M * r ^ n := by simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]; rw [← hz]; ring

theorem Layout.vertex_bound (hv : ∀ z, multiplicity L.color z * r ^ n ≤ 16 * M)
    (i : Fin n) (g : Fin r) :
    multiplicity (fun v => L.color v i) g * r ≤ 16 * M := project_bound L.color hv i g

/-- In particular this counts every location of an input padding pin. -/
theorem endpoint_uniform (b : Bool) (i : Fin n) (g : Fin r) :
    multiplicity (fun p : Position n r d h => Expansion.endpoint p b i) g * r =
      Fintype.card (Position n r d h) := by
  let f (j : Cube n × Fin h) := if b then !(j.1 i) else j.1 i
  have he (p : Packet n r d) (j : Cube n × Fin h) :
      Expansion.endpoint (p, j) b i = group p.1 i (f j) := by
    cases b <;> simp [Expansion.endpoint, corner, group, Cube.flip, f]
  have hm : multiplicity (fun p : Position n r d h => Expansion.endpoint p b i) g =
      ∑ j : Cube n × Fin h, multiplicity (fun p : Packet n r d => group p.1 i (f j)) g := by
    simp only [multiplicity, Fintype.card_subtype]
    have hcard (p : Position n r d h → Prop) [DecidablePred p] :
        (univ.filter p).card = ∑ i, if p i then 1 else 0 := by simp
    rw [hcard, Fintype.sum_prod_type, sum_comm]
    simp only [he, sum_boole, Nat.cast_id]
  rw [hm, sum_mul]
  simp only [group_uniform, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id,
    Position, Fintype.card_prod]
  ring

theorem Layout.end_bound (hv : Fintype.card (Position n r L.d h) ≤ 13 * M)
    (i : Fin n) (g : Fin r) :
    (multiplicity (fun e => L.color (.inl (G.station e)) i) g +
      multiplicity (fun e => L.color (.inr (G.junction e)) i) g) * r ≤ 26 * M := by
  have bound (b : Bool) (f : G.End → Fin r)
      (hf : ∀ e, Expansion.endpoint (L.assign e) b i = f e) :
      multiplicity f g * r ≤ 13 * M := by
    have he : multiplicity f g ≤
        multiplicity (fun p : Position n r L.d h => Expansion.endpoint p b i) g := by
      let lift : {e // f e = g} → {p // Expansion.endpoint p b i = g} :=
        fun e => ⟨L.assign e.val, (hf e.val).trans e.property⟩
      apply Fintype.card_le_of_injective lift
      intro x y hxy
      exact Subtype.ext (L.assign.injective (congrArg Subtype.val hxy))
    exact (Nat.mul_le_mul_right r he).trans ((endpoint_uniform b i g).le.trans hv)
  have h₀ := bound false (fun e => L.color (.inl (G.station e)) i)
    (fun e => congrArg (fun t => t.1 i) (L.follows e))
  have h₁ := bound true (fun e => L.color (.inr (G.junction e)) i)
    (fun e => congrArg (fun t => t.2 i) (L.follows e))
  rw [add_mul]
  omega

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end
