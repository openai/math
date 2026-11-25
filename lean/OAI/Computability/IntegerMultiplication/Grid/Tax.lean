import OAI.Computability.IntegerMultiplication.Grid.Signs

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Grid
open Code Bits
/-- clock for all short integer multiplications. argument w = supplied width, estimates eventually used at w=Cp. -/
def hail (w:ℕ) := Nat.clog 2 (w+1)
def tax (w:ℕ) := 8^(hail w / 127)

private theorem roof (w) :
    2^hail w ≤ 2*(w+1) := by
  cases w with
  | zero => simp [hail]
  | succ w =>
    have v : 0< hail (w+1) := Nat.clog_pos (by decide) (by omega)
    have t : 2^(hail (w+1)).pred < w+1+1 :=
      Nat.pow_pred_clog_lt_self (by decide) (by omega)
    rw [show hail (w+1)=(hail (w+1)).pred+1 from (Nat.succ_pred_eq_of_pos v).symm,pow_succ]
    omega

theorem tax_pos (w) : 1 ≤ tax w := Nat.pow_pos (by decide)

-- bound under constant factors (produced by Easy op).
theorem rise (c x w) (h:x≤ c*(w+1)) : hail x ≤ hail w + Nat.clog 2 (c+1) := by
  rw [hail,Nat.clog_le_iff_le_pow (by decide),pow_add]
  have u := Nat.le_pow_clog (b:=2) (by decide) (w+1)
  have v := Nat.le_pow_clog (b:=2) (by decide) (c+1)
  have t := Nat.mul_le_mul u v
  unfold hail; nlinarith
theorem snow (c) :
    ∃ k : ℕ,∀ x w:ℕ, x≤ c*(w+1) → tax x≤ k*tax w := by
  refine ⟨8^(Nat.clog 2 (c+1)+1),fun x w h=>?_⟩
  unfold tax
  have := rise _ _ _ h
  simp only [← pow_add]
  apply pow_le_pow_right₀ (by decide)
  omega

variable {I : Type}
abbrev cost (a : I→ℕ) (i:I) : ℝ := ((a i:ℝ)+1)*tax (a i)

theorem cost_pos (w : I→ℕ) (i) : 1 ≤ cost w i :=
  one_le_mul_of_one_le_of_one_le (by simp) (by exact_mod_cast tax_pos (w i))

variable {A Q Z H : Type} {x : I→ A} {s : I→ℕ} [Codec A] [Codec H] [Codec Q] [Codec Z]
/-- narrow result engineering. Retain linear output budget so these compose. -/
structure Chore (s : I→ℕ) (x : I→A) (y:I→Q) : Prop where
  input_ : ∃ D:ℕ,∀ i, Code.size (x i) ≤ D*(s i+1)
  output_ : ∃ D:ℕ,∀ i,size (y i) ≤ D*(s i+1)
  bill : Carries (cost s) (send ∘ x) (send ∘ y)

-- simplifies API: Charming f if chore on inputs at width n=size; closure ultimately.
@[fun_prop] def Charming (f:A→Q) := Chore size (id (α:=A)) f
theorem smooth {f:A→Q} (h:Easy f):Charming f := by
  obtain ⟨C,T⟩ := h.length
  have g := cost_pos (I:=A) Code.size
  let i : Volume (cost size) (send (X:=A)) := ⟨1,fun x=> ?_⟩
  · exact ⟨⟨1,by simp⟩,⟨C,fun i=> (T _).trans (by gcongr; omega)⟩,
      Carries.func g i f h⟩
  unfold cost; push_cast; rw [one_mul]
  have h : (1:ℝ)≤ tax (size x) := by exact_mod_cast tax_pos _
  change (size x:ℝ)≤ _
  nlinarith [Nat.cast_nonneg (α:=ℝ) (size x)]

theorem Charming.slide {f:A→Q} (d:I→A) {b:I→ℕ} (u:Charming f)
    (C:ℕ) (h:∀ i,size (d i)≤ C*(b i+1)) :
    Chore b d (f ∘ d) := by
  obtain ⟨_,⟨g,t⟩,z⟩ := u
  obtain ⟨k,e⟩ := snow C
  refine ⟨⟨_,h⟩,⟨g*(C+1),fun i=>?_⟩,(z.slide d).times (cost_pos b) ((C+1)*k) (fun i=> ?_)⟩
  · specialize h i; specialize t (d i)
    dsimp only [Function.comp_apply]
    nlinarith
  specialize h i; specialize e _ _ h
  unfold cost
  dsimp only [Function.comp_apply]
  exact_mod_cast (show (size (d i)+1)*tax (size (d i)) ≤ (C+1)*k*((b i+1)*tax (b i)) by
    nlinarith [Nat.mul_le_mul (by nlinarith : size (d i)+1 ≤ (C+1)*(b i+1)) e])

namespace Charming
@[fun_prop] theorem leads {f : A→Q} {g:Q→H} (h: Charming f) (i: Charming g) :
    Charming (fun x=>g (f x)) := by
  obtain ⟨C,e⟩ := h.output_
  have v := slide f i C e
  exact ⟨h.input_,v.output_,h.bill.chain v.bill⟩
@[fun_prop] theorem staring : Charming (fun i:A=>i) := smooth Easy.identity
@[fun_prop] theorem constant (q : Q) : Charming (fun _:A=>q) := smooth (Easy.const _)
@[fun_prop] theorem fst_ {f:A→H×Q} (h:Charming f) :
    Charming (fun i=> (f i).1) := h.leads (smooth Easy.fst)
@[fun_prop] theorem snd_ {f:A→H×Q} (h:Charming f) :
    Charming (fun i=> (f i).2) := h.leads (smooth Easy.snd)
@[fun_prop] theorem pairing {f:A→H} {g:A→Q} (p:Charming f) (q:Charming g) :
    Charming (fun x=>(f x,g x)) := by
  obtain ⟨C,e⟩ := p.output_; obtain ⟨B,d⟩ := q.output_
  refine ⟨⟨1,by simp⟩,⟨C+B+1,fun i=>?_⟩,p.bill.twice q.bill⟩
  specialize e i; specialize d i
  rw [size_prod]; nlinarith
end Charming
-- specialize Toom with hail W bound
@[fun_prop] theorem product_value : Charming Bits.product := by
  refine ⟨⟨1,by simp⟩,?_,?_⟩
  · refine ⟨4,fun i=> ?_⟩
    rw [size_word,Bits.length_prod,size_prod,size_word,size_word]
    omega
  let i : Toom.IW → ℕ := size
  have e := Bits.word_product.on (fun x: Word×Word=> ⟨(x,hail (i x)),by
    rcases x with ⟨a,b⟩; dsimp only
    unfold hail i
    apply le_trans _ (Nat.le_pow_clog (by decide) _)
    rw [size_prod,size_word,size_word]; dsimp only; omega⟩)
  let v := (smooth (Easy.identity (X:=Toom.IW))).bill
  refine v.sequence ⟨v.budget,Toom.budget ∘ hail ∘ i,e,3,fun x=>?_⟩
  dsimp only [Function.comp_apply, i]
  unfold Toom.budget
  have C := roof (Code.size x)
  have H := tax_pos (Code.size x)
  unfold cost tax
  exact_mod_cast (show 2^hail (Code.size x)*tax (Code.size x)+1≤3*((Code.size x+1)*tax (Code.size x)) by nlinarith only [Nat.mul_le_mul_right (tax (size x)) C,H,Nat.zero_le (Code.size x),Nat.zero_le (Code.size x*tax (Code.size x))])
def signX (x : Sign × Sign) := xor x.1 x.2
theorem sign_r (a b) : tag (signX (a,b)) = tag a*tag b := by cases a <;> cases b <;> decide
def prod (x : S × S) : S :=
  (signX (x.1.1,x.2.1),Bits.product (x.1.2,x.2.2))
@[fun_prop] theorem pay_product : Charming prod := by
  unfold prod; have s := smooth (Easy.finite signX); fun_prop
theorem prod_exact (x y : S) :
    whole (prod (x,y))=whole x* whole y := by
  unfold prod whole; dsimp only
  rw [sign_r,Bits.exact_prod,Nat.cast_mul]
  ring
end Grid

end IntegerMultiplication
end Computability
end OAI
