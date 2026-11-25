import OAI.Hierarchy.DescentPackedWalshLayout

namespace OAI
/-! # Native Walsh pointer rows and short arithmetical lookup tables in one fixed ROM -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {u l w : ℕ}

private theorem at_page {H b : ℕ} (a : Axis u l) (v : Fin H) (p : Cube u) (j : Fin 3) :
    headerWord (w:=w) H b a (j.val*page H u+(row v p).val)=
      ![((row v (above a p false)).val:Word w),((row v (above a p true)).val:Word w),
        ((2^((b+b)*2^l)*(upperSign a p).toNat:ℕ):Word w)] j := by
  have hf := (row v p).isLt
  have hs := hf.trans_le (rows_le H u)
  have hmod : (j.val*page H u+(row v p).val)%page H u=(row v p).val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt hs]
  have hh : j.val*page H u+(row v p).val<3*page H u := by
    have h0:=Nat.mul_le_mul_right (page H u) (show j.val+1≤3 from j.isLt)
    rw [Nat.succ_mul] at h0
    omega
  have eqn : headerWord (w:=w) H b a (j.val*page H u+(row v p).val) =
      (if j.val*page H u+(row v p).val<page H u then ((row v (above a p false)).val:Word w)
       else if j.val*page H u+(row v p).val<2*page H u then ((row v (above a p true)).val:Word w)
       else ((2^((b+b)*2^l)*(upperSign a p).toNat:ℕ):Word w)) := by
    unfold headerWord
    simp only [dite_eq_left hh]
    simp only [hmod,dite_eq_left hf]
    have back : unrow (⟨(row v p).val,hf⟩ : Fin (H*2^u))=(v,p):=unrow_row v p
    simp only [back,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [eqn]
  fin_cases j
  · change (if 0*page H u+(row v p).val<page H u then _ else _) = ((row v (above a p false)).val:Word w)
    simp [hs]
  · change (if 1*page H u+(row v p).val<page H u then _ else if 1*page H u+(row v p).val<2*page H u then _ else _) =
      ((row v (above a p true)).val:Word w)
    rw [ite_eq_right (by omega),ite_eq_left (by omega)]
  · change (if 2*page H u+(row v p).val<page H u then _ else if 2*page H u+(row v p).val<2*page H u then _ else _) =
      ((2^((b+b)*2^l)*(upperSign a p).toNat:ℕ):Word w)
    rw [ite_eq_right (by omega),ite_eq_right (by omega)]

theorem literal {H b : ℕ} (root first : ℕ) (axes : List (Axis u l)) (m : Memory w) (t : Fin axes.length) :
    Literal (shelf root first t.val H u l b) axes[t.val] H b (mounted H b root axes m) := by
  let P:=page H u
  let R:=span H u l b
  let off:=root+t.val*R
  have idx3 (d : Fin 3) (v : Fin H) (p : Cube u) : d.val*P+(row v p).val<R := by
    have rowRoom:=(row v p).isLt.trans_le (rows_le H u)
    have pay:=Nat.mul_le_mul_right P (show d.val+1≤3 from d.isLt)
    rw [Nat.succ_mul] at pay
    have ceil : d.val*P+(row v p).val<3*P := by change (row v p).val<P at rowRoom;omega
    exact ceil.trans_le ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have read (j : ℕ) (hj : j<R) := mounted_at H b root axes m t ⟨j,hj⟩
  have rp (j : Fin 3) (v : Fin H) (p : Cube u) := (read _ (idx3 j v p)).trans (at_page axes[t.val] v p j)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro v p
    simpa [shelf,P,R,Nat.add_assoc] using rp 0 v p
  · intro v p
    simpa [shelf,P,R,Nat.add_assoc] using rp 1 v p
  · intro v p
    simpa [shelf,P,R,Nat.add_assoc] using rp 2 v p
  · intro n
    have h:=n.isLt
    have hr : 3*P+n.val<R:=by
      change 3*P+n.val<3*P+2^(smallKey l b)+2^(bigKey l b)
      exact (Nat.add_lt_add_left h _).trans_le (Nat.le_add_right _ _)
    have up : ¬3*P+n.val<3*P:=by omega
    have reached:=read (3*P+n.val) hr
    simpa [shelf,Nat.add_assoc,headerWord,P,R,smallKey,up,Nat.add_sub_cancel_left,h] using reached
  · intro n
    have h:=n.isLt
    have hr : 3*P+2^(smallKey l b)+n.val<R:=by
      change 3*P+2^(smallKey l b)+n.val<3*P+2^(smallKey l b)+2^(bigKey l b)
      exact Nat.add_lt_add_left h _
    have high : ¬3*P+2^(smallKey l b)+n.val<3*P:=Nat.not_lt.mpr ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    have later : ¬3*P+2^(smallKey l b)+n.val-3*P<2^(smallKey l b):=by omega
    have reached:=read _ hr
    have pos : 3*P+2^(smallKey l b)+n.val-(3*P+2^(smallKey l b))=n.val:=by omega
    have tab : headerWord (w:=w) H b axes[t.val] (3*P+2^(smallKey l b)+n.val)=
        ((dictionary (b:=b) axes[t.val] n).val:Word w) := by
      dsimp only [P] at high later pos ⊢
      unfold headerWord
      simp only [dite_eq_right high,dite_eq_right later,pos,dite_eq_left (show n.val<2^(bigKey l b) from n.isLt)]
    simpa only [shelf,P,R,Nat.add_assoc] using reached.trans tab

theorem Literal.keep {B : Banks} {H b cut : ℕ} {a : Axis u l} {m o : Memory w}
    (lit : Literal B a H b m) (frame : ∀z<cut,o z=m z)
    (lo : B.lo.base+H*2^u≤cut) (hi : B.hi.base+H*2^u≤cut) (sign : B.sign.base+H*2^u≤cut)
    (sh : B.shift.base+2^(smallKey l b)≤cut) (ta : B.table.base+2^(bigKey l b)≤cut) :
    Literal B a H b o := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro v p;exact (frame _ ((Nat.add_lt_add_left (row v p).isLt _).trans_le lo)).trans (lit.lo v p)
  · intro v p;exact (frame _ ((Nat.add_lt_add_left (row v p).isLt _).trans_le hi)).trans (lit.hi v p)
  · intro v p;exact (frame _ ((Nat.add_lt_add_left (row v p).isLt _).trans_le sign)).trans (lit.sign v p)
  · intro j;exact (frame _ ((Nat.add_lt_add_left j.isLt _).trans_le sh)).trans (lit.shift j)
  · intro j;exact (frame _ ((Nat.add_lt_add_left j.isLt _).trans_le ta)).trans (lit.table j)

theorem header_after {H b root first : ℕ} (axes : List (Axis u l)) (t : Fin axes.length) (initial next : Memory w)
    (keep : ∀z<first,next z=mounted H b root axes initial z) (space : root+axes.length*span H u l b≤first) :
    Literal (shelf root first t.val H u l b) axes[t.val] H b next := by
  have cap:=(Nat.add_le_add_left (Nat.mul_le_mul_right (span H u l b) (show t.val+1≤axes.length from t.isLt)) root).trans space
  rw [Nat.succ_mul] at cap
  let start:=root+t.val*span H u l b
  have bound : start+3*page H u+2^(smallKey l b)+2^(bigKey l b)≤first := by
    simpa only [start,span,Nat.add_assoc] using cap
  have rows:=rows_le H u
  have nonneg1:=Nat.zero_le (2^(smallKey l b))
  have nonneg2:=Nat.zero_le (2^(bigKey l b))
  apply (literal root first axes initial t).keep keep
  all_goals simp only [shelf]; dsimp only [start] at bound; omega

end
end Hierarchy.DescentPackedWalsh

end OAI
