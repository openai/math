import OAI.Computability.BorderVNP.CoverLorentzIndex

/-!
# Short words in the congruence layers

In Lemma 5.1 commutators of words at two balanced depths produce a word
realizing any multiple of a basis direction at the sum of the depths. The
bound below is `(d-1)^2` letters at depth `d ≥ 2`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

/-- A word in the fixed list of right-multiplication generators with the
indicated length bound and product in the integral quaternion unit group. -/
def HasWord (S : Finset Orderˣ) (n : ℕ) (g : Orderˣ) : Prop :=
  ∃ w : List Orderˣ, (∀ s ∈ w, s ∈ S) ∧ w.length ≤ n ∧ w.prod = g

/-- Concatenating two words adds their length bounds. -/
theorem HasWord.mul {S : Finset Orderˣ} {n m : ℕ} {x y : Orderˣ}
    (hx : HasWord S n x) (hy : HasWord S m y) : HasWord S (n+m) (x*y) := by
  obtain ⟨u,hu,lu,rfl⟩ := hx
  obtain ⟨v,hv,lv,rfl⟩ := hy
  exact ⟨u++v,fun s h => (List.mem_append.mp h).elim (hu s) (hv s),
    by simpa only [List.length_append] using Nat.add_le_add lu lv, List.prod_append⟩

/-- A word over a symmetric set can be inverted at the same length. -/
theorem HasWord.inv {S : Finset Orderˣ} (hs : ∀ s ∈ S, s⁻¹ ∈ S) {n : ℕ} {x : Orderˣ}
    (hx : HasWord S n x) : HasWord S n x⁻¹ := by
  obtain ⟨u,hu,lu,rfl⟩ := hx
  refine ⟨(u.map (·⁻¹)).reverse, ?_, by simpa using lu, (List.prod_inv_reverse u).symm⟩
  intro s h
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp h)
  exact hs _ (hu _ hv)

/-- Increasing a word budget preserves its witness. -/
theorem HasWord.mono {S : Finset Orderˣ} {n m : ℕ} {x : Orderˣ} (h : HasWord S n x)
    (hn : n ≤ m) : HasWord S m x := by
  obtain ⟨u,hu,lu,hx⟩ := h
  exact ⟨u,hu,lu.trans hn,hx⟩

/-- A single generator gives a word of length one. -/
theorem HasWord.single {S : Finset Orderˣ} {x : Orderˣ} (h : x ∈ S) : HasWord S 1 x :=
  ⟨[x], by simpa using h, by simp, by simp⟩

/-- The imaginary residue module in the congruence tower. -/
abbrev Layer := ZMod 7 × ZMod 7 × ZMod 7

/-- A multiple of an individual basis direction in the imaginary residue module. -/
def axis (i : Fin 3) (t : ZMod 7) : Layer :=
  if i = 0 then (t,0,0) else if i = 1 then (0,t,0) else (0,0,t)

/-- The imaginary coordinates of the quaternion bracket modulo seven. -/
def bracket (x y : Layer) : Layer :=
  (-6 * (x.2.1 * y.2.2 - x.2.2 * y.2.1),
   -4 * (x.2.2 * y.1 - x.1 * y.2.2),
   2 * (x.1 * y.2.1 - x.2.1 * y.1))

private theorem residues_bracket (x y : Order) :
    residues (x*y-y*x) = bracket (residues x) (residues y) := by
  rcases x with ⟨a,b,c,d⟩
  rcases y with ⟨u,v,w,z⟩
  ext <;> simp [residues, bracket, QuaternionAlgebra.mk_mul_mk] <;> ring

private theorem axis_bracket : ∀ (i : Fin 3) (t : ZMod 7),
    ∃ j k : Fin 3, ∃ r s : ZMod 7, bracket (axis j r) (axis k s) = axis i t := by decide

/-- A group commutator has the bracket as its leading residue. -/
theorem commutator_lift (d e : ℕ) (x : gamma (d+2)) (y : gamma (e+2)) :
    ∃ z : gamma (d+e+4), z.val = x.val*y.val*x.val⁻¹*y.val⁻¹ ∧
      (leading (d+e+3) z).toAdd =
        bracket (leading (d+1) x).toAdd (leading (e+1) y).toAdd := by
  let a := coefficient (d+2) x
  let b := coefficient (e+2) y
  have ha : x.val.val = atDepth (d+2) a := coefficient_spec _ x
  have hb : y.val.val = atDepth (e+2) b := coefficient_spec _ y
  obtain ⟨c,hc,hr⟩ := depth_commutator (d+1) (e+1) a b (ha ▸ x.2.1) (hb ▸ y.2.1)
  rw [show d+1+(e+1)+2 = d+e+4 by omega] at hc
  let g := x.val*y.val*x.val⁻¹*y.val⁻¹
  have hg : (g : Order) = atDepth (d+e+4) c := by
    simp only [g, Units.val_mul, inverse_star _ x.2.1, inverse_star _ y.2.1, ha, hb]
    exact hc
  have hm : norm (g : Order) = 1 := by
    simp only [g, Units.val_mul, norm_mul, inverse_star _ x.2.1, inverse_star _ y.2.1,
      norm_star, x.2.1, y.2.1, one_mul]
  let z : gamma (d+e+4) := ⟨g, hm, c, hg⟩
  have hz : coefficient (d+e+4) z = c :=
    atDepth_inj _ ((coefficient_spec _ z).symm.trans hg)
  refine ⟨z,rfl,?_⟩
  change residues (coefficient (d+e+4) z) = bracket (residues a) (residues b)
  rw [hz,residues_congr hr,residues_bracket]

/-- If the fixed symmetric generating list contains one lift for each basis
multiple at depths two and three, then all higher depths have quadratic-length
words. Each recursively constructed word is in the actual congruence subgroup. -/
theorem axis_word (S : Finset Orderˣ) (hs : ∀ s ∈ S, s⁻¹ ∈ S)
    (base : ∀ d ≤ 1, ∀ (i : Fin 3) (t : ZMod 7), ∃ x : gamma (d+2),
      x.val ∈ S ∧ (leading (d+1) x).toAdd = axis i t) (d : ℕ) (i : Fin 3) (t : ZMod 7) :
    ∃ x : gamma (d+2), HasWord S ((d+1)^2) x.val ∧ (leading (d+1) x).toAdd = axis i t := by
  induction d using Nat.strong_induction_on generalizing i t with
  | h d ih =>
    by_cases hd : d ≤ 1
    · obtain ⟨x,hx,hr⟩ := base d hd i t
      exact ⟨x, (HasWord.single hx).mono (Nat.one_le_pow 2 _ (by omega)), hr⟩
    · let e := (d-2)/2
      let f := (d-1)/2
      have he : e < d := by dsimp [e]; omega
      have hf : f < d := by dsimp [f]; omega
      have hsplit : d = e+f+2 := by dsimp [e,f]; omega
      obtain ⟨j,k,r,s,hbr⟩ := axis_bracket i t
      obtain ⟨x,hx,lx⟩ := ih e he j r
      obtain ⟨y,hy,ly⟩ := ih f hf k s
      obtain ⟨z,hz,lz⟩ := commutator_lift e f x y
      rw [lx,ly,hbr] at lz
      have hb : (e+1)^2 + (f+1)^2 + (e+1)^2 + (f+1)^2 ≤ (e+f+2+1)^2 := by
        have hef : e ≤ f := by dsimp [e,f]; omega
        have hfe : f ≤ e+1 := by dsimp [e,f]; omega
        have hsq := Nat.pow_le_pow_left (Nat.succ_le_succ hef) 2
        have hlarge := Nat.pow_le_pow_left (show 2*(f+1) ≤ e+f+2+1 by omega) 2
        nlinarith
      rw [hsplit]
      refine ⟨z, ?_,lz⟩
      rw [hz]
      exact (((hx.mul hy).mul (hx.inv hs)).mul (hy.inv hs)).mono hb

end Cover

end BorderVNP
end Computability
end OAI
