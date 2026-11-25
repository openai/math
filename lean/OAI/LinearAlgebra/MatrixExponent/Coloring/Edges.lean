import OAI.LinearAlgebra.MatrixExponent.Coloring.Matching
import OAI.LinearAlgebra.MatrixExponent.Coloring.Shift

/-!
# Parallel bisection of a regular bipartite graph

At odd degree a perfect matching takes the last colour. In the even
remainder, append the split bit to both endpoints. This encodes *both*
subproblems on the original edge array. One recursive call suffices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring

variable {h k : ℕ}

def retired (S : Finset (B k)) (d : ℕ) (L R : B h → B k)
    (x : B h → Bool) : B h → Bool :=
  if d % 2 = 0 then fun _ => false else matching S d L R x

def rest (x y : B h → Bool) (i : B h) := x i && !y i

def enlarge (S : Finset (B k)) : Finset (B (k + 1)) :=
  (S ×ˢ Finset.univ).image (Function.uncurry double)

def nextEnd (L : B h → B k) (b : B h → Bool) (i : B h) :=
  double (L i) (b i)

def combine (d : ℕ) (z b : Bool) (j : B h) : B h :=
  ⟨(if z then d - 1 else 2 * j.val + b.toNat) % 2 ^ h, Nat.mod_lt _ (Nat.two_pow_pos h)⟩

def recurse {k : ℕ} (fuel : ℕ) (S : Finset (B k)) (d : ℕ) (L R : B h → B k)
    (x : B h → Bool) : B h → B h :=
  match fuel with
  | 0 => fun _ => 0
  | n + 1 =>
    let y := retired S d L R x
    let a := rest x y
    let b := split L R a
    let c := recurse n (enlarge S) (d / 2) (nextEnd L b) (nextEnd R b) a
    fun i => combine d (y i) (b i) (c i)

def colours (S : Finset (B k)) (d : ℕ) (L R : B h → B k)
    (x : B h → Bool) : B h → B h :=
  recurse (h + 1) S d L R x

variable {S : Finset (B k)} {d : ℕ} {L R : B h → B k}
variable {x y : B h → Bool} {i j : B h}

private theorem degree_pos (hi : x i = true) : 0 < degree L x (L i) :=
  Finset.card_pos.mpr ⟨i, by simp [hi]⟩

private theorem Regular.degree_pos (he : Regular S d L R x) (hi : x i = true) : 0 < d := by
  have hp := Coloring.degree_pos (L := L) hi
  rw [he.1] at hp
  split_ifs at hp <;> omega

private theorem Regular.unique (he : Regular S d L R x) (hd : d ≤ 1)
    (hi : x i = true) (hj : x j = true) (hp : L i = L j ∨ R i = R j) : i = j := by
  have aux (f : B h → B k) (hf : ∀ u, degree f x u = if u ∈ S then d else 0)
      (eq : f i = f j) : i = j := by
    have hn : degree f x (f i) ≤ 1 := by rw [hf]; split <;> omega
    exact Finset.card_le_one.mp hn i (by simp [hi]) j (by simp [hj, eq])
  exact hp.elim (aux L he.1) (aux R he.2)

private theorem outgoing (he : Regular S d L R x) (hs : S.card * d ≤ 2 ^ h) :
    Regular S (d % 2) L R (retired S d L R x) ∧ ∀ i, retired S d L R x i = true → x i = true := by
  by_cases hd : d % 2 = 0
  · simp [retired, hd, Regular, degree]
  · rw [retired, ite_eq_right hd, show d % 2 = 1 by omega]
    exact he.matching (by omega) hs

private theorem remaining (he : Regular S d L R x) (hy : Regular S (d % 2) L R y)
    (hsub : ∀ i, y i = true → x i = true) :
    Regular S (2 * (d / 2)) L R (rest x y) := by
  have aux (f : B h → B k) (j : B k) :
      degree f (rest x y) j + degree f y j = degree f x j := by
    let U := Finset.univ.filter (fun i => x i = true ∧ f i = j)
    let V := Finset.univ.filter (fun i => y i = true ∧ f i = j)
    have h : V ⊆ U := by
      intro i hi
      obtain ⟨hi, he⟩ := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub i hi, he⟩
    have hz : Finset.univ.filter (fun i => rest x y i = true ∧ f i = j) = U \ V := by
      ext i
      cases e : y i <;> simp [U, V, rest, e]
    unfold degree
    rw [hz]
    exact Finset.card_sdiff_add_card_eq_card h
  constructor
  · intro j
    have := aux L j
    rw [he.1, hy.1] at this
    split_ifs at * <;> omega
  · intro j
    have := aux R j
    rw [he.2, hy.2] at this
    split_ifs at * <;> omega


private theorem double_eq {i j : B k} {a b : Bool} :
    double i a = double j b ↔ i = j ∧ a = b := by
  rw [Fin.ext_iff]
  cases a <;> cases b <;> simp [double, Fin.ext_iff] <;> omega

private theorem double_surj (i : B (k + 1)) : ∃ j : B k, ∃ b, double j b = i := by
  have hi := i.isLt
  simp only [pow_succ] at hi
  refine ⟨⟨i.val / 2, by omega⟩, decide (i.val % 2 = 1), Fin.ext ?_⟩
  by_cases e : i.val % 2 = 1 <;> simp [double, e] <;> omega

private theorem mem_enlarge (u : B k) (b : Bool) : double u b ∈ enlarge S ↔ u ∈ S := by
  simp only [enlarge, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨⟨i, z⟩, hi, he⟩
    exact (double_eq.mp he).1 ▸ hi
  · exact fun h => ⟨(u, b), h, rfl⟩

private theorem enlarge_cost (hs : S.card * d ≤ 2 ^ h) : (enlarge S).card * (d / 2) ≤ 2 ^ h := by
  have he : (enlarge S).card ≤ S.card * 2 :=
    Finset.card_image_le.trans_eq (by simp)
  calc
    _ ≤ S.card * 2 * (d / 2) := Nat.mul_le_mul_right _ he
    _ ≤ S.card * d := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ _ := hs

private theorem bisect (he : Regular S (2 * d) L R x) :
    Regular (enlarge S) d (nextEnd L (split L R x)) (nextEnd R (split L R x)) x := by
  have even (f : B h → B k) (hf : ∀ j, degree f x j = if j ∈ S then 2 * d else 0) :
      EvenFibers f x := by
    intro j
    change Even (degree f x j)
    rw [hf]
    split
    · exact ⟨d, two_mul d⟩
    · exact ⟨0, rfl⟩
  have eq (u : B (k + 1)) :
      degree (nextEnd L (split L R x)) x u = (if u ∈ enlarge S then d else 0) ∧
      degree (nextEnd R (split L R x)) x u = (if u ∈ enlarge S then d else 0) := by
    obtain ⟨j, b, rfl⟩ := double_surj u
    obtain ⟨hl, hr⟩ := split_balanced (even L he.1) (even R he.2) j b
    change _ = degree L x j at hl
    change _ = degree R x j at hr
    rw [he.1] at hl
    rw [he.2] at hr
    simp only [degree, nextEnd, mem_enlarge, double_eq]
    split_ifs at * <;> omega
  exact ⟨fun u => (eq u).1, fun u => (eq u).2⟩

private def Proper (d : ℕ) (L R : B h → B k) (x : B h → Bool) (c : B h → B h) :=
  ∀ i, x i = true → (c i).val < d ∧
    ∀ j, x j = true → c i = c j → (L i = L j ∨ R i = R j) → i = j

private theorem merge_proper {b : B h → Bool} {c : B h → B h} (hd : d ≤ 2 ^ h)
    (hy : Regular S (d % 2) L R y)
    (hc : Proper (d / 2) (nextEnd L b) (nextEnd R b) (rest x y) c) :
    Proper d L R x (fun i => combine d (y i) (b i) (c i)) := by
  let out i := combine d (y i) (b i) (c i)
  have literal (i : B h) (hi : x i = true) :
      (y i = true ∧ d % 2 = 1 ∧ (out i).val = d - 1) ∨
      (rest x y i = true ∧ (out i).val = 2 * (c i).val + (b i).toNat ∧
        (out i).val < 2 * (d / 2)) := by
    cases ey : y i
    · have hi' : rest x y i = true := by simp [rest, hi, ey]
      have hb : (b i).toNat < 2 := by cases b i <;> decide
      have ht := (hc i hi').1
      have he : (out i).val = 2 * (c i).val + (b i).toNat := by
        simp only [out, combine, ey, Bool.false_eq_true, ite_false]
        exact Nat.mod_eq_of_lt (by omega)
      exact .inr ⟨hi', he, by omega⟩
    · have ht := hy.degree_pos ey
      refine .inl ⟨rfl, by omega, ?_⟩
      simp only [out, combine, ey, ite_true]
      exact Nat.mod_eq_of_lt (by omega)
  intro i hi
  change (out i).val < d ∧ _
  refine ⟨by rcases literal i hi with h | h <;> omega, ?_⟩
  intro j hj he eq
  change out i = out j at he
  have hv := congrArg Fin.val he
  rcases literal i hi with ⟨hi, hdi, ei⟩ | ⟨hi, ei, hdi⟩ <;>
    rcases literal j hj with ⟨hj, hdj, ej⟩ | ⟨hj, ej, hdj⟩
  · exact hy.unique (by omega) hi hj eq
  · omega
  · omega
  · have ee : double (c i) (b i) = double (c j) (b j) :=
      Fin.ext (ei.symm.trans (hv.trans ej))
    obtain ⟨ec, eb⟩ := double_eq.mp ee
    apply (hc i hi).2 j hj ec
    exact eq.imp (fun h => double_eq.mpr ⟨h, eb⟩) (fun h => double_eq.mpr ⟨h, eb⟩)

private theorem proper (fuel : ℕ) (hd : d ≤ 2 ^ h) (hf : d < 2 ^ fuel)
    (hs : S.card * d ≤ 2 ^ h) (he : Regular S d L R x) :
    Proper d L R x (recurse fuel S d L R x) := by
  induction fuel generalizing k d x with
  | zero =>
    intro i hi
    have := he.degree_pos hi
    simp only [pow_zero] at hf
    omega
  | succ fuel ih =>
    obtain ⟨hy, hsub⟩ := outgoing he hs
    have hr := bisect (remaining he hy hsub)
    rw [pow_succ] at hf
    have hp := ih (d := d / 2) (by omega) (by omega) (enlarge_cost hs) hr
    rw [recurse]
    exact merge_proper hd hy hp

theorem edge_coloring {h k : ℕ} (S : Finset (B k)) (d : ℕ) (hd : d ≤ 2 ^ h)
    (hs : S.card * d ≤ 2 ^ h) (L R : B h → B k) (x : B h → Bool) (he : Regular S d L R x) :
    ∀ i, x i = true → (colours S d L R x i).val < d ∧
      ∀ j, x j = true → colours S d L R x i = colours S d L R x j →
        (L i = L j ∨ R i = R j) → i = j :=
  proper (h + 1) hd (by rw [pow_succ]; have := Nat.two_pow_pos h; omega) hs he

end OAI.LinearAlgebra.MatrixExponent.Coloring
