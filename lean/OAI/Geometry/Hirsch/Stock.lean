import OAI.Geometry.Hirsch.Sizing

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Dials

variable (u : Dials)

def History : ℕ → Type
  | 0 => Unit
  | k+1 => (History k × u.Scale) × u.Bin

instance histories (k : ℕ) : Fintype (u.History k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((u.History k × u.Scale) × u.Bin))

theorem card_history (k : ℕ) : Fintype.card (u.History k) = (2^u.h*(u.J+1))^k := by
  induction k with
  | zero => change Fintype.card Unit = 1; exact Fintype.card_unique
  | succ k ih =>
    change Fintype.card ((u.History k × u.Scale) × u.Bin) = _
    simp [ih,Scale,Bin,pow_succ,mul_assoc]

abbrev Ticket := Σ k : Fin u.h, (u.History k × u.Scale) × Option u.Bin

def ticket {k : ℕ} (hk : k < u.h) (prev : u.History k) (c : u.Scale) (bin : Option u.Bin) : u.Ticket :=
  ⟨⟨k,hk⟩,(prev,c),bin⟩

def phase (a : u.Ticket) := 2*a.1.val + if a.2.2.isSome then 1 else 0

theorem phase_lt (a : u.Ticket) : u.phase a < 2*u.h := by
  have := a.1.isLt; unfold phase; split <;> omega

def east : ∀ k, u.History k → Bool
  | 0,_ => true
  | k+1,c => !(u.dir (east k c.1.1) c.2)

def side (a : u.Ticket) := u.east a.1 a.2.1.1

abbrev Cell (I : Type) := Fin (u.h+1) × (I ⊕ (Fin u.J × Finset I))

variable {I : Type} [Fintype I]

def stamp : Stamp (u.Cell I) I where
  age b := b.1
  keys b := b.2.elim (fun i => {i}) Prod.snd
  pin b := b.2.isLeft

def bias (b : u.Cell I) : ℝ :=
  match b.2 with
  | .inl _ => if b.1.val = 0 then u.p else u.z
  | .inr (j,s) => Real.exp ((-4*u.L/price u.t j)*u.rate (b.1.val-1)^s.card)

variable {u} (v : u.Valid)

def Valid.coin : Coins (u.Cell I) where
  bias := u.bias
  pos := by
    rintro ⟨k,i | ⟨j,s⟩⟩
    · simp only [bias]; split <;> first | exact v.initial | exact v.thin
    · exact Real.exp_pos _
  le_one := by
    rintro ⟨k,i | ⟨j,s⟩⟩
    · simp only [bias]; split <;> first | exact v.initial_le.trans v.target | exact v.thin_le
    apply Real.exp_le_one_iff.mpr
    apply mul_nonpos_of_nonpos_of_nonneg _ (pow_nonneg (v.rate_pos _).le _)
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [v.lambda]) (by linarith [price_low v.tpos j.val,v.tpos])

namespace Valid

def atom (k : Fin (u.h+1)) : (v.coin (I := I)).Raw I where
  bits i := {(k,.inl i)}
  rate := if k.val = 0 then u.p else u.z
  pos := by split <;> first | exact v.initial | exact v.thin
  weight i := by simp [Coins.weight,coin,bias]
  unique i j h := by simp [h]

omit [Fintype I] in
theorem tagged (k : Fin (u.h+1)) : u.stamp.Tagged (v.atom (I := I) k) k.val := by
  intro i b hb
  obtain rfl := Finset.mem_singleton.mp hb
  exact ⟨rfl,le_rfl,rfl⟩

def fresh {k : ℕ} (hk : k < u.h) := v.atom (I := I) ⟨k+1,by omega⟩

omit [Fintype I] in
theorem fresh_tag {k : ℕ} (hk : k < u.h) : u.stamp.Fresh (v.fresh (I := I) hk) k :=
  ⟨v.tagged _,fun _ _ hb => by rw [Finset.mem_singleton.mp hb]; rfl⟩

def foil {k : ℕ} (hk : k < u.h) {r : ℝ} (he : r = u.rate k) (j : Fin u.J) :
    Foil (v.coin (I := I)) u.stamp (k+1) r u.L (price u.t j) where
  index s := (⟨k+1,by omega⟩,.inr (j,s))
  age _ := rfl
  keys _ := rfl
  barrier _ := by simp [stamp]
  bias _ := by simp [coin,bias,he]
  positive := by linarith [price_low v.tpos j.val,v.tpos]
  nonneg := v.lambda

end Valid
end OAI.Geometry.Hirsch.Layer.Dials
