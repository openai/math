import OAI.Computability.BorderVNP.CoverLorentzArithmetic

/-!
# Leading residues in the quaternion congruence tower

The first congruence coefficient is additive under multiplication. Seventh powers
preserve it while raising depth, and the leading coefficient of a group commutator is
the additive bracket of the two coefficients.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

/-- The principal congruence expansion with specified leading coefficient and depth. -/
def atDepth (d : ℕ) (x : Order) : Order := 1 + (7 : ℤ)^d • x

/-- An integral quaternion representing a residue modulo seven. -/
def SevenEq (x y : Order) : Prop := ∃ t : Order, x = y + (7 : ℤ) • t

/-- A depth-`d` element of norm one with first coefficient equal to `v` modulo seven. -/
def Realized (d : ℕ) (v : Order) : Prop :=
  ∃ x : Order, norm (atDepth d x) = 1 ∧ SevenEq x v

/-- Products at fixed depth add their leading coefficients. -/
theorem depth_mul (d : ℕ) (x y : Order) :
    atDepth d x * atDepth d y = atDepth d (x + y + (7 : ℤ)^d • (x * y)) := by
  simp only [atDepth, add_mul, mul_add, one_mul, mul_one, smul_add, smul_mul_assoc, mul_smul_comm]
  abel

/-- Scalar conjugation of the principal congruence expansion. -/
theorem star_atDepth (d : ℕ) (x : Order) : star (atDepth d x) = atDepth d (star x) := by
  change star (1 + (7 : ℤ)^d • x) = 1 + (7 : ℤ)^d • star x
  rw [star_add, star_one]
  congr 1
  exact map_zsmul (starAddEquiv : Order ≃+ Order) _ _

/-- Conjugation is an inverse on integral norm-one quaternions. -/
theorem mul_star_eq_one (x : Order) (h : norm x = 1) : x * star x = 1 := by
  rw [QuaternionAlgebra.mul_star_eq_coe]
  change (QuaternionAlgebra.coe _ : Order) = QuaternionAlgebra.coe (1 : ℤ)
  congr 1
  rcases x with ⟨a,b,c,d⟩
  simp only [QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk, norm] at *
  linarith

/-- Sevenfold powering raises depth by one with the same leading coefficient. -/
theorem depth_seventh (d : ℕ) (x : Order) :
    ∃ y : Order, (atDepth (d+1) x)^7 = atDepth (d+2) y ∧ SevenEq y x := by
  let s : ℤ := 7^d
  let t : Order :=
    (3*s) • x^2 + (35*s^2) • x^3 + (245*s^3) • x^4 +
    (1029*s^4) • x^5 + (2401*s^5) • x^6 + (2401*s^6) • x^7
  refine ⟨x + (7 : ℤ) • t, ?_, t, rfl⟩
  have expand (z : Order) : (1+z)^7 = 1 + (7 : ℤ) • z + (21 : ℤ) • z^2 +
      (35 : ℤ) • z^3 + (35 : ℤ) • z^4 + (21 : ℤ) • z^5 + (7 : ℤ) • z^6 + z^7 := by
    simp only [zsmul_eq_mul, Int.cast_ofNat]
    noncomm_ring
  simp only [atDepth, expand, smul_pow, smul_smul, t, smul_add, pow_succ' (7:ℤ)]
  simp only [s]
  simp only [add_assoc]
  repeat' apply congrArg₂ (HAdd.hAdd : Order → Order → Order)
  all_goals first | rfl | (apply congrArg (fun z : ℤ => z • _); ring)

/-- The bracket is the leading coefficient of the quaternion group commutator. -/
theorem depth_commutator (d e : ℕ) (x y : Order)
    (hx : norm (atDepth (d+1) x) = 1) (hy : norm (atDepth (e+1) y) = 1) :
    ∃ z : Order,
      atDepth (d+1) x * atDepth (e+1) y * star (atDepth (d+1) x) * star (atDepth (e+1) y) =
        atDepth (d+e+2) z ∧ SevenEq z (x*y - y*x) := by
  let a := atDepth (d+1) x
  let b := atDepth (e+1) y
  let v := x*y - y*x
  have ha : a * star a = 1 := mul_star_eq_one _ hx
  have hb : b * star b = 1 := mul_star_eq_one _ hy
  have diff : a*b - b*a = (7:ℤ)^(d+e+2) • v := by
    have pow_eq : (7:ℤ)^(d+e+2) = (7:ℤ)^(d+1) * 7^(e+1) := by
      rw [← pow_add]; congr 1; omega
    simp only [a,b,v,atDepth, pow_eq, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, smul_add, smul_smul, smul_sub]
    rw [mul_comm ((7:ℤ)^(e+1)) ((7:ℤ)^(d+1))]
    abel
  refine ⟨v * (star a * star b), ?_, ?_⟩
  · change a*b*star a*star b = 1 + (7:ℤ)^(d+e+2) • (v * (star a * star b))
    rw [← smul_mul_assoc, ← diff, sub_mul]
    have cancel : (b*a) * (star a * star b) = 1 := by
      calc
        _ = b * (a * star a) * star b := by noncomm_ring
        _ = 1 := by rw [ha, mul_one, hb]
    rw [cancel, mul_assoc (a*b), add_sub_cancel]
  · let u := (7 : ℤ)^d • star x
    let w := (7 : ℤ)^e • star y
    have astar : star a = 1 + (7 : ℤ) • u := by
      change star (atDepth (d+1) x) = _
      rw [star_atDepth]
      simp only [atDepth,u,smul_smul,pow_succ']
    have bstar : star b = 1 + (7 : ℤ) • w := by
      change star (atDepth (e+1) y) = _
      rw [star_atDepth]
      simp only [atDepth,w,smul_smul,pow_succ']
    refine ⟨v * (w + u + (7 : ℤ) • (u*w)), ?_⟩
    rw [astar,bstar]
    simp only [v, add_mul, mul_add, one_mul, mul_one, smul_add, smul_mul_assoc, mul_smul_comm,
      sub_mul, smul_sub]
    abel

/-- Equality of leading residues is transitive. -/
theorem SevenEq.trans {x y z : Order} (hxy : SevenEq x y) (hyz : SevenEq y z) : SevenEq x z := by
  obtain ⟨u, rfl⟩ := hxy
  obtain ⟨v, rfl⟩ := hyz
  exact ⟨v + u, by rw [smul_add, add_assoc]⟩

/-- Multiplication of two residues respects their representatives. -/
theorem SevenEq.mul {x x' y y' : Order} (hx : SevenEq x x') (hy : SevenEq y y') :
    SevenEq (x*y) (x'*y') := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  exact ⟨u*y' + x'*w + (7 : ℤ) • (u*w), by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add]
    abel⟩

/-- Subtraction of residues respects representatives. -/
theorem SevenEq.sub {x x' y y' : Order} (hx : SevenEq x x') (hy : SevenEq y y') :
    SevenEq (x-y) (x'-y') := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  exact ⟨u-w, by rw [smul_sub]; abel⟩

/-- Powers preserve norm one. -/
theorem norm_pow (x : Order) (k : ℕ) : norm (x^k) = norm x ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ k hk => rw [pow_succ, norm_mul, hk, pow_succ]

/-- Quaternion conjugation preserves norm. -/
theorem norm_star (x : Order) : norm (star x) = norm x := by
  rcases x with ⟨a,b,c,d⟩
  simp [norm]

/-- Realizability depends only on the specified residue. -/
theorem Realized.congr {d : ℕ} {x y : Order} (hx : Realized d x) (hxy : SevenEq x y) :
    Realized d y := by
  obtain ⟨u, hu, h⟩ := hx
  exact ⟨u,hu,h.trans hxy⟩

/-- The norm-one layer is closed under addition of first coefficients. -/
theorem Realized.add {d : ℕ} {x y : Order} (hx : Realized (d+1) x) (hy : Realized (d+1) y) :
    Realized (d+1) (x+y) := by
  obtain ⟨a,ha,⟨u,hu⟩⟩ := hx
  obtain ⟨b,hb,⟨w,hw⟩⟩ := hy
  refine ⟨a + b + (7 : ℤ)^(d+1) • (a*b), ?_, ?_⟩
  · rw [← depth_mul (d+1) a b, norm_mul, ha, hb, one_mul]
  · refine ⟨u + w + (7 : ℤ)^d • (a*b), ?_⟩
    rw [hu,hw,pow_succ',smul_add,smul_add,smul_smul]
    abel

/-- Integer multiplicities generated by repetition in a positive-depth layer. -/
theorem Realized.nsmul {d : ℕ} {x : Order} (hx : Realized (d+1) x) (n : ℕ) :
    Realized (d+1) (n • x) := by
  induction n with
  | zero =>
    rw [zero_smul]
    exact ⟨0, by simp only [atDepth, smul_zero, add_zero]; rfl, 0, by simp⟩
  | succ n h => simpa only [succ_nsmul] using h.add hx

/-- Every realizable residue lifts unchanged one level further. -/
theorem Realized.raise {d : ℕ} {v : Order} (h : Realized (d+1) v) : Realized (d+2) v := by
  obtain ⟨x,hx,hv⟩ := h
  obtain ⟨y, he, hr⟩ := depth_seventh d x
  exact ⟨y,by rw [← he,norm_pow,hx,one_pow],hr.trans hv⟩

/-- Taking a commutator realizes the bracket in the sum of the two depths. -/
theorem Realized.bracket {d e : ℕ} {v w : Order}
    (hv : Realized (d+1) v) (hw : Realized (e+1) w) :
    Realized (d+e+2) (v*w - w*v) := by
  obtain ⟨x,hx,hv⟩ := hv
  obtain ⟨y,hy,hw⟩ := hw
  obtain ⟨z,he,hr⟩ := depth_commutator d e x y hx hy
  exact ⟨z,by rw [← he]; simp only [norm_mul,norm_star,hx,hy,one_mul],
    hr.trans ((hv.mul hw).sub (hw.mul hv))⟩

private theorem basisI_one : Realized 1 basisI := by
  have h : Realized 1 ((3 : ℕ) • basisI) :=
    ⟨⟨14,10,0,0⟩,rfl,⟨2,1,0,0⟩,rfl⟩
  exact (h.nsmul 5).congr ⟨⟨0,2,0,0⟩,rfl⟩

private theorem basisJ_one : Realized 1 basisJ := by
  have h : Realized 1 ((5 : ℕ) • basisJ) :=
    ⟨⟨2688,0,1552,0⟩,rfl,⟨384,0,221,0⟩,rfl⟩
  exact (h.nsmul 3).congr ⟨⟨0,0,2,0⟩,rfl⟩

/-- Starting at depth two, each of the three imaginary basis coefficients occurs. -/
theorem basis_realized (d : ℕ) :
    Realized (d+2) basisI ∧ Realized (d+2) basisJ ∧ Realized (d+2) basisK := by
  induction d with
  | zero =>
    have h := (basisI_one.bracket basisJ_one).nsmul 4
    exact ⟨basisI_one.raise,basisJ_one.raise,h.congr ⟨⟨0,0,0,1⟩,rfl⟩⟩
  | succ d h => exact ⟨h.1.raise,h.2.1.raise,h.2.2.raise⟩

/-- Every triple of mod-seven imaginary coordinates occurs at every depth at least two. -/
theorem imaginary_realized (d : ℕ) (a b c : Fin 7) :
    Realized (d+2) (a.val • basisI + b.val • basisJ + c.val • basisK) := by
  obtain ⟨hi,hj,hk⟩ := basis_realized d
  exact ((hi.nsmul a.val).add (hj.nsmul b.val)).add (hk.nsmul c.val)

end Cover

end BorderVNP
end Computability
end OAI
