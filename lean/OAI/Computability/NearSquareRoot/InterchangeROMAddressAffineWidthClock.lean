import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineWidth
import OAI.Computability.NearSquareRoot.InterchangeROMAddressGather

/-! # Full-stream bound for the signed width compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress.Affine

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom Space AffineAddress InterchangeROMAddress

private def mirrorHeader (K d : ℕ) (t : Template × Header) : ℕ :=
  size t.2 + size (projection (t.1.1.1,t.2)) + InterchangeROMMirror.projectTime K d t.1.1.1 t.2 + 1

private theorem mirrorHeader_poly (K d : ℕ) : Dom size (mirrorHeader K d) := by
  let r := fun t : Template × Header => (t.1.1.1,t.2)
  have hr : Poly r := by unfold r; fun_prop
  have hproj := (hr.compose projection_poly).length
  have htime := ((Dom.const (size (X:=Template × Header)) 5).mul
    (show Poly (fun t : Template × Header => t.1.1.1) from by fun_prop).length).add
    ((Dom.const _ K).mul ((hr.length.add (Dom.const _ 1)).pow d))
  exact (((show Poly (fun t : Template × Header => t.2) from by fun_prop).length.add hproj).add
    (htime.add (Dom.const _ 20))).add (Dom.const _ 1)

private def Under (m : Usage) (w : ℕ) := m.time ≤ w ∧ m.space ≤ w ∧ m.depth ≤ w

private theorem mirror_below {K d C : ℕ} {t : Template × Header} {x : Tree} {n w : ℕ}
    (hv : mirrorHeader K d t ≤ w) (hx : x.count ≤ w) (hn : n ≤ w) (_hw : 1 ≤ w) :
    Under (mirrorUsage K d C t.1.1.1 t.2 x n) ((4*C+4)*w) := by
  let q := (Tree.fork (send (projection (t.1.1.1,t.2))) x).count+n+1
  have bound : q ≤ 4*w := by
    dsimp only [q,Tree.count]
    change (send t.2).count + (send (projection (t.1.1.1,t.2))).count + _ + 1 ≤ w at hv
    omega
  have u : C*q ≤ 4*C*w := by
    calc
      _ ≤ C*(4*w) := Nat.mul_le_mul_left _ bound
      _ = _ := by ac_rfl
  change Under ⟨_,max _ (C*q),max _ (C*q)⟩ _
  unfold Under
  dsimp only [Usage.time,Usage.space,Usage.depth,Tree.count]
  change (send t.2).count + (send (projection (t.1.1.1,t.2))).count +
    InterchangeROMMirror.projectTime K d t.1.1.1 t.2 + 1 ≤ w at hv
  dsimp only [q,Tree.count] at u ⊢
  rw [Nat.add_mul]
  omega

private theorem width_below {neg : Bool} {h x z : Tree} {m lane : Usage} {w A B : ℕ}
    (hh : h.count ≤ w) (hx : x.count ≤ w) (hz : z.count ≤ w) (hw : 1 ≤ w)
    (hm : Under m (A*w)) (hl : Under lane (B*w)) :
    Under (widthUsage neg h x z m lane) ((110+A+B)*w) := by
  rcases hm with ⟨mt,ms,md⟩
  rcases hl with ⟨lt,ls,ld⟩
  rw [Nat.add_mul,Nat.add_mul]
  cases neg <;> simp only [widthUsage,Bool.cond_false,Bool.cond_true,joinUsage,restoreUsage,Under,Tree.count] <;> omega

/-- Every signed width template executes within a single-stream affine scan price
for time, per-register capacity, and return depth. -/
theorem width_command : ∃ M C j : ℕ, ∀ {J : Type} [DecidableEq J] {n b f : ℕ} [NeZero b]
    (ord : J ≃ Fin n) (P G S : Tape) (_ : solid P) (_ : solid G) (_ : solid S) (_ : 2 ≤ b)
    (slot : Spot J) (a : Span b) (v : Keys P G S J (Block b f) → Tree) env deck base,
    DeckCap base deck →
    let physical := arrays ord (line b f) P G S
    let h := header f P G S
    let rows := InterchangeAffineMask.widthRows a.neg a.top.count a.down.count
    let literal := spec ord b slot slot rows.1 rows.2
    let source := stripe physical v
    let dest := stripe physical (v ∘ (reflect ord (.width slot a) trivial P G S f).symm)
    let cost := scanPrice M C j (InterchangeAffineMask.colors rows.1 rows.2).length
      literal h physical.count source dest
    BoundedFits env (numericWidth b n (slot.1,(ord slot.2).val) a.neg a.top.count a.down.count)
      (pile 0 (.fork (send h) source) deck) (pile 0 dest deck) cost (base+cost) cost := by
  obtain ⟨K,d,e,Km,dm,Cm,run⟩ := run_width
  obtain ⟨C₁,j₁,laneBound⟩ := cap_le K d e
  obtain ⟨j₂,C₂,headerBound⟩ := mirrorHeader_poly Km dm
  let C := C₁+C₂+1
  let j := j₁+j₂
  let M := 110+(4*Cm+4)+(5*K+3)
  refine ⟨M,C,j,?_⟩
  intro J dec n b f nz ord P G S hp hg hs hb slot a v env deck base hd
  let h := header f P G S
  let sl := oneStop (p:=b) (j:=f) (P:=P) (G:=G) (B:=S) ord slot
  let cells := arrays ord (line b f) P G S
  let z := signedSource a.neg sl v
  let x := width ord P G S hp hg hs hb slot a z
  let t := (x.static,x.layout)
  let source := stripe cells v
  let dest := stripe cells (v ∘ (reflect ord (.width slot a) trivial P G S f).symm)
  let N := cells.count
  let W := work C j N x
  have zsize : (stripe cells z).count = source.count := by
    change (stripe cells (signedSource a.neg sl v)).count = (stripe cells v).count
    rw [stripe_eq,stripe_eq]
    change size (cells.tab (signedSource a.neg sl v)) = size (cells.tab v)
    cases a.neg <;> simp only [signedSource,Bool.false_eq_true,ite_false,ite_true,tab_volume_eq]
  have start := slotRows_source sl a z
  have stop := slotRows_signed sl a v
  change x.rows.source.map Prod.snd = cells.tab z at start
  change x.rows.target.map Prod.snd = cells.tab (v ∘ (reflect ord (.width slot a) trivial P G S f).symm) at stop
  have volume : recordVolume x = source.count+dest.count+1 := by
    simp only [recordVolume,start,stop]
    change (send (cells.tab z)).count+(send (cells.tab _)).count+1 = _
    rw [← stripe_eq,← stripe_eq,zsize]
  have short₁ : C₁*(size t+1)^j₁ ≤ C*(size t+1)^j :=
    Nat.mul_le_mul (by dsimp [C]; omega) (Nat.pow_le_pow_right (by omega) (by dsimp [j]; omega))
  have short₂ : C₂*(size t+1)^j₂ ≤ C*(size t+1)^j :=
    Nat.mul_le_mul (by dsimp [C]; omega) (Nat.pow_le_pow_right (by omega) (by dsimp [j]; omega))
  have wmono : work C₁ j₁ N x ≤ W :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ short₁) _)
  have lane := (laneBound N x (width_priced ord P G S hp hg hs hb slot a z d)).trans
    (Nat.mul_le_mul_left _ wmono)
  have lanes : Under (positiveUsage K d e x) ((5*K+3)*W) := by
    exact ⟨by dsimp [positiveUsage]; omega, lane, by dsimp [positiveUsage]; omega⟩
  have inner : recordVolume x+(N+1)*(C*(size t+1)^j) ≤ W :=
    Nat.le_mul_of_pos_left _ (by omega)
  have positive : 0 < C*(size t+1)^j := Nat.mul_pos (by dsimp [C]; omega) (Nat.pow_pos (by omega))
  have nle : N ≤ W := by
    have p := Nat.le_mul_of_pos_right (N+1) positive
    omega
  have mle : mirrorHeader Km dm t ≤ W := by
    have h₁ := (headerBound t).trans short₂
    have h₂ := Nat.le_mul_of_pos_left (C*(size t+1)^j) (show 0<N+1 by omega)
    omega
  have he : (send h).count ≤ W := by
    have : size t.2 ≤ mirrorHeader Km dm t := by dsimp [mirrorHeader]; omega
    exact this.trans mle
  have src : source.count ≤ W := by rw [volume] at inner; omega
  have one : 1 ≤ W := by rw [volume] at inner; omega
  have mir := mirror_below (C:=Cm) mle src nle one
  have total := width_below (neg:=a.neg) he src (zsize.le.trans src) one mir lanes
  have ok := run ord P G S hp hg hs hb slot a v env deck base hd
  have finish := ok.mono total.1 (Nat.add_le_add_left total.2.1 base) total.2.2
  dsimp only at finish ⊢
  change BoundedFits _ _ _ _ (M*W) (base+M*W) (M*W) at finish
  have price : M*W = scanPrice M C j x.rows.colors.length x.static h N source dest := by
    simp only [W,work,volume,scanPrice,Nat.mul_assoc]
    rfl
  rw [price] at finish
  exact finish

end InterchangeROMAddress.Affine

end NearSquareRoot
end Computability
end OAI
