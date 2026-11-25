import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Bounds on the short local fields of a dated packed program -/
namespace Hierarchy.DescentDatedAddressBook
open DescentCompiler.TerminalScale Filter

/-- A dyadic exponent common to every date and every admitted parameter at that height. -/
def SmallAt {ι : ℕ→Type*} (J : ℕ→ℕ) (a : ∀h,ι h→ℕ) : Prop :=
  ∃e : ℕ,∀ᶠ h : ℕ in atTop,∀i,a h i≤scale (J h) e

namespace SmallAt
variable {ι : ℕ→Type*} {J : ℕ→ℕ} {a b : ∀h,ι h→ℕ}

theorem of_le (wide : SmallAt J b) (lower : ∀h i,a h i≤b h i) : SmallAt J a :=by
  rcases wide with ⟨e,he⟩
  exact ⟨e,he.mono fun h hh i=>(lower h i).trans (hh i)⟩

theorem const (J : ℕ→ℕ) (c : ℕ) : SmallAt (ι:=ι) J (fun _ _=>c) :=by
  refine ⟨c,Eventually.of_forall fun h _=>?_⟩
  exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))

theorem mul (ha : SmallAt J a) (hb : SmallAt J b) : SmallAt J (fun h i=>a h i*b h i) :=by
  obtain ⟨p,hp⟩:=ha
  obtain ⟨q,hq⟩:=hb
  refine ⟨p+q,?_⟩
  filter_upwards [hp,hq] with h p' q'
  intro i
  rw [←scale_mul]
  exact Nat.mul_le_mul (p' i) (q' i)

theorem max (ha : SmallAt J a) (hb : SmallAt J b) : SmallAt J (fun h i=>Max.max (a h i) (b h i)) :=by
  obtain ⟨p,hp⟩:=ha
  obtain ⟨q,hq⟩:=hb
  refine ⟨p+q,?_⟩
  filter_upwards [hp,hq] with h p' q'
  intro i
  exact max_le ((p' i).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_right p q))))
    ((q' i).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_left q p))))

theorem add (ha : SmallAt J a) (hb : SmallAt J b) : SmallAt J (fun h i=>a h i+b h i) :=by
  apply ((const J 2).mul (ha.max hb)).of_le
  intro h i
  have ha':=le_max_left (a h i) (b h i)
  have hb':=le_max_right (a h i) (b h i)
  omega

theorem clog (ha : SmallAt J a) : SmallAt J (fun h i=>Nat.clog 2 (a h i)) :=
  ha.of_le fun _h _i=>Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

theorem at_height (B e : ℕ) (positive : 0<B) (bought : 2*e≤B)
    (width : ∀ᶠ h : ℕ in atTop,∀i,a h i≤scale (Nat.log 2 h/(2*B)) e) :
    ∀ᶠ h : ℕ in atTop,∀i,8*a h i≤h :=by
  filter_upwards [width,eventually_home 0 0 e B positive (by simpa using bought)] with h wh room
  intro i
  have pay:=room.2 0 1 (a h i) (by simp [tail]) (by simp) (wh i)
  omega

end SmallAt
end Hierarchy.DescentDatedAddressBook

end OAI
