import OAI.Geometry.Hirsch.LocalTests

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Dials

variable {I : Type} (u : Dials) (e : Equiv.Perm I)

def cells : Equiv.Perm (u.Cell I) :=
  (Equiv.refl _).prodCongr (e.sumCongr ((Equiv.refl _).prodCongr e.finsetCongr))

def tables := (u.cells e).arrowCongr (Equiv.refl Bool)

theorem tables_apply (x : Table (u.Cell I)) (b : u.Cell I) : u.tables e x (u.cells e b) = x b := by
  simp [tables,Equiv.arrowCongr_apply]

theorem tables_id (x : Table (u.Cell I)) : u.tables (Equiv.refl I) x = x := by
  have h : u.cells (Equiv.refl I) = Equiv.refl _ := by
    apply Equiv.ext
    rintro ⟨k,i | ⟨j,s⟩⟩ <;> simp [cells]
  ext; simp [tables,h]

theorem bias_cells (b : u.Cell I) : u.bias (u.cells e b) = u.bias b := by
  rcases b with ⟨k,i | ⟨j,s⟩⟩
  · rfl
  · change Real.exp (_ * _ ^ (s.map e.toEmbedding).card) = _
    rw [Finset.card_map]; rfl

variable [Fintype I] {u} (v : u.Valid)

theorem Valid.invariant (E : Table (u.Cell I) → Prop) :
    v.coin.law.prob (fun x => E (u.tables e x)) = v.coin.law.prob E := by
  apply Law.preserve
  intro x
  change (∏ b, (v.coin.bit b).mass (u.tables e x b)) = ∏ b, (v.coin.bit b).mass (x b)
  rw [← Equiv.prod_comp (u.cells e)]
  simp only [tables_apply,Coins.bit,Valid.coin,bias_cells]

theorem Valid.atom_same (k : Fin (u.h+1)) (i : I) (x : Table (u.Cell I)) :
    i ∈ (v.atom k).pins.success x ↔ e i ∈ (v.atom k).pins.success (u.tables e x) := by
  simp only [Coins.Raw.mem,Valid.atom,Coins.All,Finset.mem_singleton,forall_eq]
  exact iff_of_eq (congrArg (· = true) (u.tables_apply e x (k,.inl i)).symm)

end OAI.Geometry.Hirsch.Layer.Dials

namespace OAI.Geometry.Hirsch.Layer.Pins

variable {I Ω : Type} [Fintype Ω] {p : Law Ω} {pins pins' : Pins p I}
  {e : Equiv.Perm I} {f : Equiv.Perm Ω}

structure Equivariant (pins pins' : Pins p I) (e : Equiv.Perm I) (f : Equiv.Perm Ω) : Prop where
  rate : pins.rate = pins'.rate
  law : ∀ E, p.prob (fun x => E (f x)) = p.prob E
  success : ∀ i x, i ∈ pins.success x ↔ e i ∈ pins'.success (f x)

namespace Equivariant

variable (h : pins.Equivariant pins' e f)
include h

theorem weight (s : Finset I) : pins.weight s = pins'.weight (e.finsetCongr s) := by
  simp [Pins.weight,h.rate]

theorem mass (B : Finset (Finset I)) : pins.mass B = pins'.mass (e.finsetCongr.finsetCongr B) := by
  simp only [Pins.mass,Equiv.finsetCongr_apply,Finset.sum_map]
  exact Finset.sum_congr rfl fun s _ => h.weight s

theorem subset (s : Finset I) (x : Ω) :
    s ⊆ pins.success x ↔ e.finsetCongr s ⊆ pins'.success (f x) := by
  constructor
  · intro h' j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact (h.success _ _).mp (h' hi)
  · exact fun hh i hi => (h.success _ _).mpr (hh (by simpa using hi))

theorem given {E E' : Ω → Prop} (he : ∀ x, E x ↔ E' (f x)) (s : Finset I) :
    pins.given E s = pins'.given E' (e.finsetCongr s) := by
  unfold Pins.given Pins.joint
  rw [h.weight,← h.law (fun x => E' x ∧ e.finsetCongr s ⊆ pins'.success x)]
  exact congrArg (· / _) (p.eq_prob fun x => and_congr (he x) (h.subset s x))

theorem screen {K : ℕ} (t : Thresholds K) {E E' : Ω → Prop} (he : ∀ x, E x ↔ E' (f x)) (x : Ω) :
    pins.Screen t E x ↔ pins'.Screen t E' (f x) := by
  unfold Screen Compatible
  rw [he x]
  apply and_congr_right
  intro _
  constructor
  · intro hh s hs hk
    obtain ⟨s,rfl⟩ := e.finsetCongr.surjective s
    have card : (e.finsetCongr s).card = s.card := Finset.card_map _
    rw [card,← h.given he]
    exact hh _ ((h.subset _ x).mpr hs) (card ▸ hk)
  · intro hh s hs hk
    have card : (e.finsetCongr s).card = s.card := Finset.card_map _
    rw [h.given he s,← card]
    exact hh _ ((h.subset _ x).mp hs) (card.symm ▸ hk)

end Equivariant
end OAI.Geometry.Hirsch.Layer.Pins
