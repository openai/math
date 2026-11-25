import OAI.Computability.IntegerMultiplication.Port.Specialize

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Port
noncomputable section
structure Nug (p : ℕ) where
  count : ℕ
  pos : count≠0
  side : Nat.Coprime count p
namespace Nug
variable {p}
def own (z : Nug p) (j : ℕ) : (Tower p j)ˣ := ZMod.unitOfCoprime z.count (z.side.pow_right j)
@[simp] theorem identifies (z : Nug p) (j : ℕ) : (z.own j : Tower p j)=z.count := rfl
def one : Nug p := ⟨1,by decide,by simp⟩
def mul (a b : Nug p) : Nug p := ⟨a.count*b.count,Nat.mul_ne_zero a.pos b.pos,a.side.mul_left b.side⟩
@[simp] theorem own_one (j p : ℕ) : (one (p:=p)).own j = 1 := Units.ext (by simp [one])
@[simp] theorem own_mul (j) (a b : Nug p) :
    (a.mul b).own j = a.own j * b.own j := Units.ext (by simp [mul])
def small (pr : Nat.Prime p) (m : ℕ) (h : m≠0) (e : m<p) : Nug p :=
  ⟨m,h,(pr.coprime_iff_not_dvd.mpr (fun x => by have := Nat.le_of_dvd (by omega : 0 < m) x; omega)).symm⟩
end Nug
structure Span (p : ℕ) where
  neg : Bool
  top : Nug p
  down : Nug p

namespace Span
variable {p j}
def polarity (p j : ℕ) (a : Bool) : (Tower p j)ˣ := if a then -1 else 1
@[simp] theorem xority (p j : ℕ) (a b : Bool) : polarity p j (xor a b) =
    polarity p j a * polarity p j b := by cases a <;> cases b <;> simp [polarity]
@[simp] theorem reflex (p j : ℕ) (a : Bool) : (polarity p j a)⁻¹ = polarity p j a := by
  cases a <;> simp [polarity]
@[simp] theorem declines (p j : ℕ) (a : Bool) : polarity p j (!a) = -polarity p j a := by
  cases a <;> simp [polarity]

def fold (j) (z : Span p) : (Tower p j)ˣ := polarity p j z.neg * z.top.own j * (z.down.own j)⁻¹
def land (j) (z : Span p) : Tower p j := z.fold j

def compose (a b : Span p) : Span p := ⟨xor a.neg b.neg, a.top.mul b.top, a.down.mul b.down⟩
def opposite (a : Span p) : Span p := ⟨!a.neg,a.top,a.down⟩
def reciprocal (a : Span p) : Span p := ⟨a.neg,a.down,a.top⟩
def one : Span p := ⟨false,Nug.one,Nug.one⟩

@[simp] theorem fold_com (a b : Span p) : (compose a b).fold j = a.fold j * b.fold j := by
  simp [compose, fold, mul_inv_rev]
  ac_rfl
@[simp] theorem fold_opp (a : Span p) : (opposite a).fold j = -a.fold j := by simp [opposite,fold]
@[simp] theorem fold_rec (a : Span p) : (reciprocal a).fold j = (a.fold j)⁻¹ := by
  simp [reciprocal,fold,mul_inv_rev]; ac_rfl
@[simp] theorem fold_one (p j : ℕ) : (one (p:=p)).fold j = 1 := by simp [one,fold,polarity]
@[simp] theorem land_opp (a : Span p) : (opposite a).land j = -a.land j := by simp [land]
@[simp] theorem land_com (a b : Span p) : (compose a b).land j = a.land j*b.land j := by simp [land]
@[simp] theorem land_rec (a : Span p) : a.land j*a.reciprocal.land j=1 := by
  simp only [land,fold_rec,Units.mul_inv]
@[simp] theorem land_one (p j) : (one (p:=p)).land j = 1 := by simp [land]
end Span

abbrev Pinpoint (p : ℕ) := Option (Span p)
namespace Pinpoint
variable {p j : ℕ}
def stamp (j) (s : Pinpoint p) : Tower p j := s.elim 0 (Span.land j)
def opposite (s : Pinpoint p) := s.map (·.opposite)
def right (s : Pinpoint p) (a : Span p) := s.map (·.compose a)
def unit : Pinpoint p := some Span.one

@[simp] theorem rev (s : Pinpoint p) : (stamp j s.opposite) = -s.stamp j := by cases s <;> simp [stamp,opposite]
@[simp] theorem rscale (s : Pinpoint p) (a : Span p) :
    (stamp j (right s a))=stamp j s*a.land j := by cases s <;> simp [stamp,right]
@[simp] theorem none : stamp j (.none:Pinpoint p) = 0 := rfl
@[simp] theorem one : stamp j (unit:Pinpoint p) = 1 := by simp [unit,stamp]

theorem from_rat (x : ℚ) (pr : Nat.Prime p) (d : x.den<p) (n : x.num.natAbs < p) :
    ∃ s : Pinpoint p, ∀ j, Token x (s.stamp j) := by
  by_cases e : x.num=0
  · have ex : x=0 := by
      nth_rw 1 [← x.num_div_den]
      rw [e,Int.cast_zero,zero_div]
    refine ⟨Option.none, fun j => ?_⟩
    change Token x (0 : Tower p j)
    rw [ex]
    exact Token.zero
  let a := decide (x.num<0)
  let u := Nug.small pr x.num.natAbs (Int.natAbs_ne_zero.mpr e) n
  let v := Nug.small pr x.den x.den_ne_zero d
  refine ⟨some ⟨a,u,v⟩,fun j => ?_⟩
  let c : Tower p j := (Span.polarity p j a : (Tower p j)ˣ)
  have h0 : c*(u.count:Tower p j)=x.num := by
    dsimp only [a,c,u,Span.polarity,Nug.small]
    generalize ht : x.num=z
    cases z <;> simp
    simp [show ∀ k : ℕ, ¬(k:ℤ)<0 from by simp]
  refine ⟨↑x.den,x.num,?_,?_,?_⟩
  · simpa [v,Nug.small] using (v.own j).isUnit
  · change (↑(x.den:ℤ) : Tower p j) * (↑(Span.fold j ⟨a,u,v⟩) : Tower p j) = _
    rw [Int.cast_natCast, ← (show (v.own j:Tower p j)=x.den from rfl), Span.fold]
    simp only [Units.val_mul]
    change _ * (c * (u.own j:Tower p j) * _) = _
    rw [mul_comm (v.own j : Tower p j), mul_assoc (c*_), Units.inv_mul,mul_one]
    exact h0
  rw [Int.cast_natCast, mul_comm]
  exact (eq_div_iff (Nat.cast_ne_zero.mpr x.den_ne_zero)).mp x.num_div_den.symm

end Pinpoint
end
end Port

end IntegerMultiplication
end Computability
end OAI
