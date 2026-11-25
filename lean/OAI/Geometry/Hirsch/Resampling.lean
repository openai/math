import OAI.Geometry.Hirsch.Thinning

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

namespace Law

variable {Ω Γ : Type} [Fintype Ω] [Fintype Γ] (p : Law Ω) (q : Law Γ)

def tensor : Law (Ω × Γ) where
  mass x := p.mass x.1 * q.mass x.2
  nonneg x := mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp [← Finset.mul_sum,total]

theorem tensor_mean (f : Ω × Γ → ℝ) :
    (p.tensor q).mean f = p.mean (fun x => q.mean (fun y => f (x,y))) := by
  simp only [mean,Fintype.sum_prod_type,Finset.mul_sum,tensor,mul_assoc]

theorem tensor_prob (e : Ω × Γ → Prop) :
    (p.tensor q).prob e = p.mean (fun x => q.prob (fun y => e (x,y))) := by
  simp only [← mean_ind,tensor_mean]

theorem tensor_both (e : Ω → Prop) (f : Γ → Prop) :
    (p.tensor q).prob (fun x => e x.1 ∧ f x.2) = p.prob e * q.prob f := by
  rw [← mean_ind,tensor_mean]
  simp only [← ind_mul,mean_scale,mean_ind]
  simp_rw [mul_comm _ (q.prob f)]
  rw [mean_scale,mean_ind]

theorem tensor_first (e : Ω → Prop) : (p.tensor q).prob (fun x => e x.1) = p.prob e := by
  rw [← mean_ind,tensor_mean]
  simp only [mean_const,mean_ind]

theorem preserve (f : Ω ≃ Ω) (hf : ∀ x, p.mass (f x) = p.mass x) (e : Ω → Prop) :
    p.prob (fun x => e (f x)) = p.prob e := by
  simpa only [prob,hf] using Equiv.sum_comp f (fun x => if e x then p.mass x else 0)

theorem event_loss (start stop fail : Ω → Prop) (hh : ∀ x, start x → stop x ∨ fail x) :
    p.prob start - p.prob fail ≤ p.prob stop := sub_le_iff_le_add.mpr ((p.mono hh).trans (p.either ..))

end Law

abbrev Table (Bit : Type) := Bit → Bool

namespace Table

variable {Bit Y : Type}

def Reads (s : Set Bit) (f : Table Bit → Y) := ∀ x y, Set.EqOn x y s → f x = f y

theorem Reads.mono {s t : Set Bit} {f : Table Bit → Y} (hf : Reads s f) (hs : s ⊆ t) :
    Reads t f := fun _ _ h => hf _ _ (h.mono hs)

def replace (s : Set Bit) (x y : Table Bit) : Table Bit := fun b => if b ∈ s then y b else x b

theorem Reads.replace {s : Set Bit} {f : Table Bit → Y} (hf : Reads s f) (x y) :
    f (Table.replace s x y) = f y := hf _ _ (fun _ h => by simp [Table.replace,h])

theorem Reads.keep {s : Set Bit} {f : Table Bit → Y} (hf : Reads sᶜ f) (x y) :
    f (Table.replace s x y) = f x := hf _ _ (fun b h => by simp [Table.replace,show b ∉ s from h])

def swap (s : Set Bit) (x : Table Bit × Table Bit) := (replace s x.1 x.2,replace s x.2 x.1)

theorem involution (s : Set Bit) : Function.Involutive (swap s) := by
  intro x
  ext b <;> by_cases h : b ∈ s <;> simp [swap,replace,h]

end Table

structure Coins (Bit : Type) where
  bias : Bit → ℝ
  pos : ∀ b, 0 < bias b
  le_one : ∀ b, bias b ≤ 1

namespace Coins

open Table

variable {Bit : Type} [Fintype Bit] [DecidableEq Bit] (coin : Coins Bit)

def bit (b : Bit) : Law Bool where
  mass x := if x then coin.bias b else 1-coin.bias b
  nonneg := by rintro (_ | _) <;> simp [coin.le_one,(coin.pos _).le]
  total := by simp

def law : Law (Table Bit) := Law.product coin.bit

abbrev two := coin.law.tensor coin.law

def swapped (s : Set Bit) := (involution s).toPerm (swap s)

theorem preserve (s : Set Bit) (e : Table Bit × Table Bit → Prop) :
    coin.two.prob (fun x => e (swap s x)) = coin.two.prob e := by
  apply coin.two.preserve (swapped s) _ e
  intro x
  change (∏ b, (coin.bit b).mass (Table.replace s x.1 x.2 b)) *
    (∏ b, (coin.bit b).mass (Table.replace s x.2 x.1 b)) =
    (∏ b, (coin.bit b).mass (x.1 b)) * (∏ b, (coin.bit b).mass (x.2 b))
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun b _ => by by_cases h : b ∈ s <;> simp [Table.replace,h,mul_comm])

theorem marginal (s : Set Bit) (e : Table Bit → Prop) :
    coin.two.prob (fun x => e (Table.replace s x.1 x.2)) = coin.law.prob e :=
  (coin.preserve s (fun x => e x.1)).trans (coin.law.tensor_first _ e)

theorem independent {s : Set Bit} {e f : Table Bit → Prop}
    (he : Reads sᶜ e) (hf : Reads s f) : coin.law.Independent e f := by
  unfold Law.Independent
  rw [← coin.marginal s (fun x => e x ∧ f x)]
  simp only [he.keep,hf.replace]
  exact coin.law.tensor_both _ _ _

theorem resample_both (s : Set Bit) {e f : Table Bit → Prop} (hf : Reads s f) :
    coin.two.prob (fun x => e (Table.replace s x.1 x.2) ∧ f x.1) = coin.law.prob e * coin.law.prob f := by
  rw [← coin.law.tensor_both,← coin.preserve s (fun x => e x.1 ∧ f x.2)]
  simp only [swap,hf.replace]

def All (s : Finset Bit) (x : Table Bit) := ∀ b ∈ s, x b = true

omit [Fintype Bit] [DecidableEq Bit] in
theorem reads_all (s : Finset Bit) : Reads (↑s) (All s) := fun _ _ he => propext
  ⟨fun h b hb => (he hb).symm.trans (h b hb),fun h b hb => (he hb).trans (h b hb)⟩

def weight (s : Finset Bit) := ∏ b ∈ s, coin.bias b

theorem all_prob (s : Finset Bit) : coin.law.prob (All s) = coin.weight s := by
  unfold law All
  rw [Law.independent coin.bit (fun b x => b ∈ s → x = true)]
  have he : ∀ b, (coin.bit b).prob (fun x => b ∈ s → x = true) = if b ∈ s then coin.bias b else 1 := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb,bit,Law.prob]
  simp [he,weight]

end Coins
end OAI.Geometry.Hirsch.Layer
