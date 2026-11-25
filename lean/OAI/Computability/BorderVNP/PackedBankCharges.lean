import OAI.Computability.BorderVNP.PackedBankBoxWords
import OAI.Computability.BorderVNP.PackedBankRecords
import OAI.Computability.BorderVNP.ShortenStaticRowsAccess
import OAI.Computability.BorderVNP.ShortenEpochSewnRecords

/-! # Charging the concrete seed-site directories to physical tile records

The spoke at an origin pays for its rectangular staging area. At a terminal the
incoming spoke and the outgoing compact feeders pay for the whole padded
assignment, including the original input area. A paid-term site is charged at
its own multiplicity. All charges stay at the site being tested, even for a
nonlocal cable with its other end in a different tile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCharges

open Crossing Crossing.Profile.Cell Shortening Shortening.CombiningStep Shortening.SeedIntervals
  Shortening.StaticRows Finset
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Local sparse rows, including fixed ties to physical incident words. For a
paid site there is one staging equality per lane and one whole-cable tie per
incident bundle, including a zero-width bundle. Variable terminal hook rows are separate. -/
noncomputable def sparse : TemplateSite e → ℕ
  | .inl _ => 1 + 3*Fintype.card (Fin D × Bool)
  | .inr (.inl _) => (e.count+3) + (e.count+1)
  | .inr (.inr ⟨i,v⟩) =>
    let d := PaidBox.arity e i v
    d + 1 + Fintype.card (PaidBox.Bundle (e.net i) v)

/-- Bits of the actual padded origin/terminal assignment, or all allocated bits
and private factor visits of a repeated paid-term site. -/
noncomputable def volume (j : ℕ) (h : Fin e.count → ℕ) : TemplateSite e → ℕ
  | .inl _ => Fintype.card (Fin D × Bool) * (originLayout (Fin D × Bool) j e.count).stride
  | .inr (.inl _) => Fintype.card (Unit ⊕ Unit ⊕ Fin e.count) * (terminalLayout j m h).stride
  | .inr (.inr ⟨i,v⟩) => h i * (1 + 2*PaidBox.arity e i v)

private noncomputable def multiplier : TemplateSite e → ℕ
  | .inl _ => Fintype.card (Fin D × Bool) * Fintype.card (Fin D × Bool)
  | .inr (.inl _) => 2 * Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)
  | .inr (.inr ⟨i,v⟩) => 1 + 2*PaidBox.arity e i v

/-- A common multiplier fixed by the paid identity, before any public branch
or tested output tile. -/
noncomputable def bound := (∑ v : TemplateSite e, sparse e v) + ∑ v : TemplateSite e, multiplier e v

private theorem sparse_le (v : TemplateSite e) : sparse e v ≤ bound e :=
  (single_le_sum (fun z _ => Nat.zero_le (sparse e z)) (mem_univ v)).trans (Nat.le_add_right _ _)

private theorem multiplier_le (v : TemplateSite e) : multiplier e v ≤ bound e :=
  (single_le_sum (fun z _ => Nat.zero_le (multiplier e z)) (mem_univ v)).trans (Nat.le_add_left _ _)

/-- Physical cost summed at just one end of each incident cable. -/
private noncomputable def endAt {E V : Type*} [Fintype E] (w : E → ℕ) (endSite : E → V) (v : V) :=
  ∑ z, if endSite z = v then w z else 0

private theorem endAt_sum {E V : Type*} [Fintype E] [Fintype V] (w : E → ℕ)
    (endSite : E → V) (test : V → Prop) :
    testedWidth (endAt w endSite) test = testedWidth w (fun z => test (endSite z)) := by
  unfold testedWidth endAt
  calc
    _ = ∑ v, ∑ z, if endSite z = v then (if test v then w z else 0) else 0 := by
      apply sum_congr rfl
      intro v _
      by_cases h : test v <;> simp [h]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro z _
      simp

private theorem tested_add {E : Type*} [Fintype E] (f g : E → ℕ) (p : E → Prop) :
    testedWidth (fun x => f x + g x) p = testedWidth f p + testedWidth g p := by
  unfold testedWidth
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  by_cases h : p x <;> simp [h]

private theorem tested_mul {E : Type*} [Fintype E] (c : ℕ) (f : E → ℕ) (p : E → Prop) :
    testedWidth (fun x => c * f x) p = c * testedWidth f p := by
  unfold testedWidth
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  by_cases h : p x <;> simp [h]

private theorem sub_sum {I E : Type*} [Fintype I] [Fintype E] (f : I ↪ E) (w : E → ℕ) :
    ∑ i, w (f i) ≤ ∑ z, w z := by
  rw [← sum_map univ f w]
  exact sum_le_sum_of_subset (subset_univ _)

variable [NeZero D] {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
  {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev L := (output e p bin perm positive first q).layout
private noncomputable abbrev matched := blocks p.layout bin perm m

/-- Physical charge of the newly emitted sites alone. All variable hook ranges
and any retained input directories may be charged separately. -/
noncomputable def charge (ex : Bool) : (L e p bin perm positive first q).Site → ℕ
  | .inl _ => 0
  | .inr ⟨a,v⟩ => sparse e v + if ex then volume e (matched (m := m) p bin perm a) (q a).val v else 0

omit [Fintype P] in
private theorem spoke_le (a : A) (u : Fin D × Bool) :
    let G := L e p bin perm positive first q
    matched (m := m) p bin perm a * Nat.clog 2 e.count ≤ endAt (fun z => recordCost true (G.width z))
      G.src (.inr ⟨a,.inl ()⟩) ∧
    matched (m := m) p bin perm a * Nat.clog 2 e.count ≤ endAt (fun z => recordCost true (G.width z))
      G.dst (.inr ⟨a,.inr (.inl u)⟩) := by
  let G := L e p bin perm positive first q
  let z : G.Edge := .inr (.inr ⟨a,.inl u⟩)
  have atEnd (get : G.Edge → G.Site) : G.width z ≤ endAt (fun z => recordCost true (G.width z)) get (get z) := by
    have h := single_le_sum (fun x _ => Nat.zero_le
      (if get x = get z then recordCost true (G.width x) else 0)) (mem_univ z)
    exact (Nat.le_add_left _ 1).trans (by simpa only [endAt,ite_true,recordCost] using h)
  exact ⟨atEnd G.src,atEnd G.dst⟩

omit [Fintype P] in
private theorem feeders_le (a : A) (u : Fin D × Bool) :
    let G := L e p bin perm positive first q
    matched (m := m) p bin perm a * m ≤ endAt (fun z => recordCost true (G.width z))
      G.src (.inr ⟨a,.inr (.inl u)⟩) := by
  let G := L e p bin perm positive first q
  let v : G.Site := .inr ⟨a,.inr (.inl u)⟩
  let f : Fin e.count ↪ G.Edge := ⟨fun i => .inr (.inr ⟨a,.inr (.inl (i,u))⟩), by
    intro i k h
    have hk := congrArg (fun z : G.Edge => match z with
      | .inr (.inr ⟨_,.inr (.inl (t,_))⟩) => some t | _ => none) h
    exact Option.some.inj hk⟩
  let cost (z : G.Edge) := if G.src z = v then recordCost true (G.width z) else 0
  have hval (i : Fin e.count) : (q a).val i * m ≤ cost (f i) := by
    change _ ≤ if v = v then 1 + (q a).val i * m else 0
    simp
  rw [← profileCounts_total e (matched (m := m) p bin perm) q a, sum_mul]
  exact (sum_le_sum (s := univ) fun i _ => hval i).trans (sub_sum f cost)

omit [Fintype P] in
private theorem volume_le (a : A) (v : TemplateSite e) :
    let G := L e p bin perm positive first q
    let u : G.Site := .inr ⟨a,v⟩
    volume e (matched (m := m) p bin perm a) (q a).val v ≤ bound e *
      (bankUses e (matched (m := m) p bin perm a) (q a).val v +
        endAt (fun z => recordCost true (G.width z)) G.src u +
        endAt (fun z => recordCost true (G.width z)) G.dst u) := by
  dsimp only
  let G := L e p bin perm positive first q
  let j := matched (m := m) p bin perm a
  let C := bound e
  rcases v with o | u | ⟨i,v⟩
  · cases o
    have hs := (spoke_le e p bin perm positive first q a first).1
    have hc := multiplier_le e (.inl ())
    rw [volume, originStride, ← Nat.mul_assoc (Fintype.card (Fin D × Bool)) (Fintype.card (Fin D × Bool))]
    apply Nat.mul_le_mul hc
    apply hs.trans
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  · let R := Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)
    let s := endAt (fun z => recordCost true (G.width z)) G.src (.inr ⟨a,.inr (.inl u)⟩)
    let d := endAt (fun z => recordCost true (G.width z)) G.dst (.inr ⟨a,.inr (.inl u)⟩)
    have hs : j*m ≤ s := feeders_le e p bin perm positive first q a u
    have hd : j*Nat.clog 2 e.count ≤ d := (spoke_le e p bin perm positive first q a u).2
    have hc : 2*R ≤ C := multiplier_le e (.inr (.inl u))
    change R * (terminalLayout j m (q a).val).stride ≤ C*(0+s+d)
    rw [terminalStride _ _ _ (profileCounts_total e _ q a), zero_add]
    have hslots : j*(Nat.clog 2 e.count + 2*m) ≤ 2*(s+d) := by
      rw [Nat.mul_add, Nat.mul_left_comm j 2]
      omega
    exact (Nat.mul_le_mul_left R hslots).trans
      ((by rw [← Nat.mul_assoc, Nat.mul_comm R 2] : R*(2*(s+d)) = (2*R)*(s+d)).le.trans
        (Nat.mul_le_mul_right _ hc))
  · have hc := multiplier_le e (.inr (.inr ⟨i,v⟩))
    rw [volume,Nat.mul_comm ((q a).val i)]
    exact Nat.mul_le_mul hc (by dsimp only [bankUses]; omega)

/-- For any tile test, the actual new record and bit budgets are bounded by a fixed
multiple of the corresponding physical local record count of the sewn output.
The expanded mode charges every box visit and its two allocated bit regions. -/
theorem tile_le (ex : Bool) (prior payload : p.layout.Site → ℕ)
    (test : (L e p bin perm positive first q).Site → Prop) :
    let G := L e p bin perm positive first q
    let hist := Sum.elim prior (fun _ => 0)
    let pay := Sum.elim payload (fun z => bankUses e (matched (m := m) p bin perm z.1) (q z.1).val z.2)
    testedWidth (charge e p bin perm positive first q ex) test ≤ bound e * localRecords G ex hist pay test := by
  let G := L e p bin perm positive first q
  let hist : G.Site → ℕ := Sum.elim prior (fun _ => 0)
  let pay : G.Site → ℕ := Sum.elim payload (fun z => bankUses e (matched (m := m) p bin perm z.1) (q z.1).val z.2)
  let boxes (v : G.Site) := boxCost ex (hist v) (pay v)
  let wc (z : G.Edge) := recordCost ex (G.width z)
  let mass (v : G.Site) := boxes v + endAt wc G.src v + endAt wc G.dst v
  have h (v : SiteShape e p A) : charge e p bin perm positive first q ex v ≤ bound e * mass v := by
    rcases v with old | ⟨a,v⟩
    · exact Nat.zero_le _
    · cases ex with
      | false =>
        simp only [charge, Bool.false_eq_true, ite_false, add_zero]
        apply (sparse_le e v).trans
        change bound e ≤ bound e * (1 + _ + _)
        exact Nat.le_mul_of_pos_right _ (by omega)
      | true =>
        have hvol := volume_le e p bin perm positive first q a v
        have hs := sparse_le e v
        let payloadHere := bankUses e (matched (m := m) p bin perm a) (q a).val v
        let c := fun z : G.Edge => recordCost true (G.width z)
        let s := endAt c G.src (.inr ⟨a,v⟩)
        let d := endAt c G.dst (.inr ⟨a,v⟩)
        refine (Nat.add_le_add hs hvol).trans_eq ?_
        change bound e + bound e*(payloadHere+s+d) = bound e*((0+(1+payloadHere))+s+d)
        ring
  have hm : testedWidth (charge e p bin perm positive first q ex) test ≤
      testedWidth (fun v => bound e * mass v) test := by
    apply sum_le_sum
    intro v _
    by_cases hv : test v <;> simp [hv,h v]
  rw [tested_mul] at hm
  apply hm.trans (Nat.mul_le_mul_left _ ?_)
  change testedWidth (fun v => boxes v + endAt wc G.src v + endAt wc G.dst v) test ≤ localRecords G ex hist pay test
  rw [tested_add,tested_add,endAt_sum,endAt_sum]
  exact Nat.le_add_right _ _

/-- Any metadata fixed by one template site can be charged to that site's compulsory
physical box record. The same bound applies to any set of tiles and either mode. -/
theorem static_tile_le (cost : TemplateSite e → ℕ) (ex : Bool)
    (prior payload : (L e p bin perm positive first q).Site → ℕ)
    (test : (L e p bin perm positive first q).Site → Prop) :
    let G := L e p bin perm positive first q
    testedWidth (Sum.elim (fun _ : p.layout.Site => 0) (fun z : Σ _ : A, TemplateSite e => cost z.2)) test ≤
      (∑ v : TemplateSite e, cost v) * localRecords G ex prior payload test := by
  let G := L e p bin perm positive first q
  let bo (v : G.Site) := boxCost ex (prior v) (payload v)
  let C := ∑ v : TemplateSite e, cost v
  have h (v : SiteShape e p A) : Sum.elim (fun _ => 0) (fun z : Σ _ : A, TemplateSite e => cost z.2) v
      ≤ C * bo v := by
    rcases v with v | ⟨a,v⟩
    · exact Nat.zero_le _
    · have hc : cost v ≤ C := single_le_sum (fun x _ => Nat.zero_le (cost x)) (mem_univ v)
      exact hc.trans (Nat.le_mul_of_pos_right _ (by dsimp [bo,boxCost,recordCost]; omega))
  have htest : testedWidth (Sum.elim (fun _ : p.layout.Site => 0) (fun z : Σ _ : A, TemplateSite e => cost z.2)) test ≤ testedWidth (fun v => C * bo v) test := by
    apply sum_le_sum
    intro v _
    by_cases hv : test v <;> simp [hv,h v]
  rw [tested_mul] at htest
  refine htest.trans (Nat.mul_le_mul_left _ ?_)
  change testedWidth bo test ≤ testedWidth bo test + _ + _ + _
  omega

/-- An individual seed site's complete expanded charge is bounded by the
uniform tile cap at its own location. -/
theorem site_le {T : Type*} (tile : (L e p bin perm positive first q).Site → T)
    (prior payload : p.layout.Site → ℕ) (M : ℕ)
    (cap : ∀ t, localRecords (L e p bin perm positive first q) true
      (Sum.elim prior (fun _ => 0))
      (Sum.elim payload (fun z => bankUses e (matched (m := m) p bin perm z.1) (q z.1).val z.2))
      (fun v => tile v = t) ≤ M)
    (a : A) (v : TemplateSite e) :
    sparse e v + volume e (matched (m := m) p bin perm a) (q a).val v ≤ bound e * M := by
  let G := L e p bin perm positive first q
  let u : G.Site := .inr ⟨a,v⟩
  let c := charge e p bin perm positive first q true
  have ht := tile_le e p bin perm positive first q true prior payload (fun z => tile z = tile u)
  have hu := single_le_sum (fun z _ => Nat.zero_le (if tile z = tile u then c z else 0)) (mem_univ u)
  exact (by simpa only [testedWidth,ite_true] using hu : c u ≤ testedWidth c (fun z => tile z = tile u)).trans
    (ht.trans (Nat.mul_le_mul_left _ (cap (tile u))))

end Packing.BankCharges

end BorderVNP
end Computability
end OAI
