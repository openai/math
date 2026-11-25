import OAI.LinearAlgebra.MatrixExponent.Processor.PacketNet
import OAI.LinearAlgebra.MatrixExponent.Processor.Guard
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Replay
import OAI.LinearAlgebra.MatrixExponent.Processor.Skip
import OAI.LinearAlgebra.MatrixExponent.Processor.Vector.Cases
import OAI.LinearAlgebra.MatrixExponent.Processor.AddressSize
import OAI.LinearAlgebra.MatrixExponent.Processor.DispatchSize
import OAI.LinearAlgebra.MatrixExponent.Diagonal.TemplateSize

/-! # Exact semantics of the worker's packet kernel -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel

open Diagonal Classical Finset
variable {F : Type} [Field F] {n h p w t r N d : ℕ} (A : Expansion F n h)
  {hn : 2 ≤ n} {R : A.Report r d} {c : Class r}

def agrees (e : MemberOrder A hn R c p) (mode : Mode) (x : Inputs A p w t → Bool)
    (z : A.Alphabet hn N R c) : Prop :=
  symbol A e z = raw A x ∧ (mode.share = true →
    ∀ j, A.alphabetCode hn N R c z j = compact A x (Fin.ofNat (2 ^ t) j.val))

def product (e : MemberOrder A hn R c p) (mode : Mode) (x : Inputs A p w t → Bool)
    (z : A.Alphabet hn N R c) : F :=
  ∏ j, modeValue A mode (z.1.val (e j)) R.1 (fun s => row A x j (.inl (false, s)))
    (fun s => row A x j (.inl (true, s))) (A.shared N R c) (z.2 (e j))

private theorem check_iff (e : MemberOrder A hn R c p) (mode : Mode) (x : Inputs A p w t → Bool)
    (z : A.Alphabet hn N R c) (hz : symbol A e z = raw A x)
    (hcut : mode.cut = A.shared N R c) (hcap : p * (prefixSize A + reserve A) ≤ 2 ^ t) :
    (mode.share = true → PackCode.Matches t (valueAt A x) (markAt A R.1 mode x) (compact A x)) ↔
      agrees A e mode x z := by
  simp only [agrees, hz, true_and]
  by_cases hm : mode.share = true
  · have hh : A.shared N R c = true := by rw [← hcut]; cases mode <;> simp_all [Mode.share, Mode.cut]
    have h := (symbol_width A e z).trans hcap
    have he (j : Fin (A.classWidth R c)) : Fin.ofNat (2 ^ t) j.val = Fin.castLE h j :=
      Fin.ext (Nat.mod_eq_of_lt (j.isLt.trans_le h))
    simp only [hm, true_implies, match_code A e z mode x hz hcut hh hcap, funext_iff,
      Function.comp_apply, he]
  · simp [hm]

/-- Each private code string represents at most one class symbol.
Ill-formed code strings contribute zero. -/
theorem kernel_eq (e : MemberOrder A hn R c p) (mode : Mode) (x : Inputs A p w t → Bool)
    (hcut : mode.cut = A.shared N R c) (hcap : p * (prefixSize A + reserve A) ≤ 2 ^ t)
    (he : ∀ s, expected A x s = (R.2 (c, s)).val) :
    kernel A R.1 mode x = ∑ z : A.Alphabet hn N R c, if agrees A e mode x z then product A e mode x z else 0 := by
  by_cases ht : ∃ z : A.Alphabet hn N R c, symbol A e z = raw A x
  · have hc := ((symbol_iff A e x).mpr ht).2
    obtain ⟨z, hz⟩ := ht
    rw [Fintype.sum_eq_single z]
    · simp only [kernel, he, hc, implies_true, true_and, check_iff A e mode x z hz hcut hcap]
      congr 1
      exact prod_congr rfl fun j _ => entry_encode A R.1 mode _ hcut _ _ _ (congrFun hz j).symm
    · intro z' hn
      exact ite_eq_right fun h => hn (symbol_injective A e (h.1.trans hz.symm))
  · have hall (z : A.Alphabet hn N R c) : ¬ agrees A e mode x z := fun hz => ht ⟨z, hz.1⟩
    simp only [hall, ite_false, sum_const_zero, kernel]
    split_ifs with hk
    · have hb : ¬∀ j, ok A R.1 mode.cut (raw A x j) := by
        intro hv
        apply ht
        apply (symbol_iff A e x).mp
        exact ⟨hcut ▸ hv, fun s => (hk.1 s).trans (he s)⟩
      obtain ⟨j, hj⟩ := not_forall.mp hb
      apply prod_eq_zero (mem_univ j)
      exact ite_eq_right hj
    · rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
end

/-!
# Summing the private records of a packet class

The external positions supply the packet data, the reported counts,
and the compacted stream. Each contributing symbol has exactly one
fixed-width encoding in the private positions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel

open Diagonal Classical Install
variable {F : Type} [Field F] {n h r d N p w t : ℕ} (A : Expansion F n h)
  {hn : 2 ≤ n} {R : A.Report r d} {c : Class r}

abbrev Given (p w t : ℕ) :=
  (Fin p × Bool × Spectral.Cube n × Fin h) ⊕ (A.I × Fin w) ⊕ PackCode.Index t
abbrev Private (p : ℕ) := Fin p × Code A

private def layout : Inputs A p w t ≃ Given A p w t ⊕ Private A p :=
  ((Equiv.prodSumDistrib _ _ _).sumCongr (.refl _)).trans
    ((Equiv.sumAssoc _ _ _).trans
      (((Equiv.refl _).sumCongr (Equiv.sumComm _ _)).trans (Equiv.sumAssoc _ _ _).symm))

def assemble (x : Given A p w t → Bool) (y : Private A p → Bool) : Inputs A p w t → Bool :=
  Sum.elim x y ∘ layout A

def closed (i : Fin n) (mode : Mode) (x : Given A p w t → Bool) : F :=
  ∑ y, kernel A i mode (assemble A x y)

theorem closed_net (i : Fin n) (pick : (Fin 2 → Bool) → Mode) (hp : p < 2 ^ w) :
    Weight F (fun x : Fin 2 ⊕ Given A p w (height A p) → Bool =>
      closed A i (pick (x ∘ Sum.inl)) (x ∘ Sum.inr))
      (rate A * (1 + p) * (1 + w) ^ 3 + p * Fintype.card (Code A)) := by
  let e := ((Equiv.refl (Fin 2)).sumCongr (layout (p := p) (w := w) (t := height A p) A)).trans
    (Equiv.sumAssoc _ _ _).symm
  have h := ((switched_net A i pick hp).rename e).sum_right
  rw [Fintype.card_prod, Fintype.card_fin] at h
  convert h using 1
  funext x
  unfold closed
  apply Finset.sum_congr rfl
  intro y _
  apply congrArg
  funext j
  change Sum.elim (x ∘ Sum.inr) y (layout A j) = Sum.elim x y ((Equiv.sumAssoc _ _ _).symm (.inr (layout A j)))
  cases layout A j <;> rfl

def stream (mode : Mode) (data : PackCode.Index t → Bool) (z : A.Alphabet hn N R c) : Prop :=
  mode.share = true → ∀ j, A.alphabetCode hn N R c z j = data (Fin.ofNat (2 ^ t) j.val)

def term (e : MemberOrder A hn R c p) (mode : Mode) (x : Given A p w t → Bool)
    (z : A.Alphabet hn N R c) : F :=
  ∏ j, modeValue A mode (z.1.val (e j)) R.1 (fun k => x (.inl (j, false, k)))
    (fun k => x (.inl (j, true, k))) (A.shared N R c) (z.2 (e j))

theorem closed_eq (e : MemberOrder A hn R c p) (mode : Mode) (x : Given A p w t → Bool)
    (hcut : mode.cut = A.shared N R c) (hcap : p * (prefixSize A + reserve A) ≤ 2 ^ t)
    (he : ∀ s, number (fun j => x (.inr (.inl (s, j)))) = (R.2 (c, s)).val) :
    closed A R.1 mode x = ∑ z : A.Alphabet hn N R c,
      if stream A mode (fun j => x (.inr (.inr j))) z then term A e mode x z else 0 := by
  have hh (y) := kernel_eq A e mode (assemble A x y) hcut hcap he
  unfold closed
  simp_rw [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.sum_eq_single (Function.uncurry (symbol A e z))]
  · have hs : symbol A e z = raw A (assemble A x (Function.uncurry (symbol A e z))) := rfl
    have he : agrees A e mode (assemble A x (Function.uncurry (symbol A e z))) z ↔
        stream A mode (fun j => x (.inr (.inr j))) z := by
      simp only [agrees, ← hs, true_and]
      rfl
    simp only [he]
    rfl
  · intro y hy
    apply ite_eq_right
    intro h
    exact hy (congrArg Function.uncurry h.1.symm)

end OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
end

/-!
# The packet contribution at one worker

Only data delivered to the worker can affect its factor. In particular
the remaining rows of the fixed layout may be filled with zeros.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel

open Finset Diagonal Classical
variable {F : Type} [Field F] {n h r d p w t : ℕ} (A : Expansion F n h)
  (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d) (u : Worker r)

abbrev Incident :=
  {c : Class r // A.src hn N R (.inr c) = u ∨ A.dst hn N R (.inr c) = u}

private def chooseMode (l : Bool) (left right u : Worker r) : Mode :=
  if l then if left = right then .both else .side (decide (right = u)) else .joint

def modeAt (c : Class r) : Mode :=
  chooseMode (A.shared N R c) (A.src hn N R (.inr c)) (A.dst hn N R (.inr c)) u

theorem modeAt_cut (c : Class r) : (modeAt A hn N R u c).cut = A.shared N R c := by
  unfold modeAt chooseMode
  split_ifs <;> simp_all [Mode.cut]

theorem modeAt_share (c : Class r) :
    (modeAt A hn N R u c).share = true ↔ A.src hn N R (.inr c) ≠ A.dst hn N R (.inr c) := by
  unfold modeAt chooseMode
  split_ifs <;> simp_all [Mode.share, Expansion.src, Expansion.dst]

private theorem pieces (s : A.I) (i : Fin n) (x y : Block n h) (l : Bool)
    (v : Fin (A.width s i l) → Bool) (left right : Worker r)
    (hl : l = false → left = right) (hu : left = u ∨ right = u) :
    (∏ b : Bool, if (if b then right else left) = u then A.piece s i x y b l v else 1) =
      modeValue A (chooseMode l left right u) s i x y l v := by
  cases l
  · obtain rfl := hl rfl
    have h := hu.elim id id
    simp [h, Expansion.piece, modeValue]
  · by_cases he : left = right
    · subst right
      have h := hu.elim id id
      simp [chooseMode, h, Expansion.piece, modeValue, Expansion.value, mul_comm]
    · rcases hu with rfl | rfl <;> simp [chooseMode, he, Ne.symm he, Expansion.piece, modeValue]

private def contribution (a : A.Assignment hn N R) (c : Class r) : F :=
  ∏ b, if A.worker hn N R c b = u then A.half a c b else 1

def supplied (a : A.Assignment hn N R) (c : Class r) (e : MemberOrder A hn R c p)
    (x : Given A p w t → Bool) : Prop :=
  ∀ j b k, A.dst hn N R (.inl (((e j).val, k), b)) = u →
    x (.inl (j, b, k)) = A.rows a b (e j).val k

private theorem term_eq (a : A.Assignment hn N R) (c : Incident A hn N R u)
    (e : MemberOrder A hn R c.val p) (x : Given A p w t → Bool)
    (hx : supplied A hn N R u a c.val e x) :
    contribution A hn N R u a c.val = term A e (modeAt A hn N R u c.val) x (a (.inr c.val)) := by
  let z := a (.inr c.val)
  let f (b : Bool) (j : Fin p) :=
    A.piece (z.1.val (e j)) R.1 (fun k => x (.inl (j, false, k))) (fun k => x (.inl (j, true, k))) b
      (A.shared N R c.val) (z.2 (e j))
  have hb (b : Bool) : (if A.worker hn N R c.val b = u then A.half a c.val b else 1) =
      ∏ j, if A.worker hn N R c.val b = u then f b j else 1 := by
    by_cases he : A.worker hn N R c.val b = u
    · simp only [he, ite_true, Expansion.half]
      rw [← e.toEquiv.prod_comp]
      apply prod_congr rfl
      intro j _
      apply A.piece_local
      · intro k hk
        exact (hx j false k ((A.row_dst hn N R c.val (e j) k false b hk).trans he)).symm
      · intro k hk
        have ht : A.shared N R c.val = true → (!(k.1 R.1)) = b := fun h =>
          (show ∀ x y : Bool, x ≠ y → (!x) = y by decide) _ _ (hk h)
        exact (hx j true k ((A.row_dst hn N R c.val (e j) k true b ht).trans he)).symm
    · simp [he]
  unfold contribution term
  simp only [hb]
  rw [prod_comm]
  apply prod_congr rfl
  intro j _
  apply pieces
  · intro hs
    simp [Expansion.src, Expansion.dst, hs]
  · exact c.property

private theorem product_contribution (a : A.Assignment hn N R) :
    A.factor a u = ∏ c : Incident A hn N R u, contribution A hn N R u a c.val := by
  let s := univ.filter (fun c => A.src hn N R (.inr c) = u ∨ A.dst hn N R (.inr c) = u)
  rw [← prod_subtype s (by simp [s])]
  symm
  apply prod_subset (subset_univ _)
  intro c _ hc
  simp only [s, mem_filter, mem_univ, true_and, not_or] at hc
  unfold contribution
  apply prod_eq_one
  intro b _
  cases b <;> simp [Expansion.worker, hc]

abbrev Family := (c : Incident A hn N R u) → A.Alphabet hn N R c.val

/-- Private summation in the class kernels computes exactly the worker's
sum over incident symbols, constrained by the received physical bits.
Slots whose destination is another worker are unrestricted. -/
theorem product_eq
    (e : (c : Incident A hn N R u) → MemberOrder A hn R c.val p)
    (x : Incident A hn N R u → Given A p w t → Bool)
    (a : Family A hn N R u → A.Assignment hn N R)
    (hcap : p * (prefixSize A + reserve A) ≤ 2 ^ t)
    (he : ∀ c s, number (fun j => x c (.inr (.inl (s, j)))) = (R.2 (c.val, s)).val)
    (ha : ∀ z c, a z (.inr c.val) = z c)
    (hx : ∀ z c, supplied A hn N R u (a z) c.val (e c) (x c)) :
    (∏ c, closed A R.1 (modeAt A hn N R u c.val) (x c)) =
      ∑ z : Family A hn N R u,
        if ∀ c, stream A (modeAt A hn N R u c.val) (fun j => x c (.inr (.inr j))) (z c)
        then A.factor (a z) u else 0 := by
  have hh (c) := closed_eq A (e c) (modeAt A hn N R u c.val) (x c)
    (modeAt_cut A hn N R u c.val) hcap (he c)
  simp_rw [hh]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro z _
  have hf : A.factor (a z) u = ∏ c, term A (e c) (modeAt A hn N R u c.val) (x c) (z c) := by
    rw [product_contribution]
    apply prod_congr rfl
    intro c _
    rw [term_eq A hn N R u (a z) c _ _ (hx z c), ha]
  simp only [prod_ite_zero, mem_univ, forall_const, hf]

end OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
end

section
/-! # Network cost of checking the physical link schedule -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed

open Coloring Diagonal.Links
variable {F S I : Type} [Field F] [Fintype I] {w R N c : ℕ} {inp : S → I → Bool}

private def test (u low sender relay mate idx limit here there : ℕ) :=
  let off := if u = low then (if here = 0 then 1 else 0) else 1
  let on := if relay = u then (if mate = u then 1 else (if here = there then 1 else 0)) else 1
  if sender = mate then off else if idx < limit then on else off

private theorem test_le (u l a v b k q x y : ℕ) : test u l a v b k q x y ≤ 1 := by
  simp only [test]
  split_ifs <;> decide

private theorem test_eq (u : Fin R) (q : Fin R → Fin R → ℕ) (t : ℕ → Bool) (p : Slot R N) :
    test u.val p.1.val.1.val (sender p).val (relay p).val (mate q p).val
      (Diagonal.Links.index q p) (q (sender p) (mate q p)) (t (address p).val).toNat
        (t (peer q p)).toNat = 1 ↔ relayCheck q u t p := by
  simp only [test, relayCheck, active, ← Fin.ext_iff]
  cases t (address p).val <;> cases t (peer q p) <;> simp <;> grind

private theorem test_net {u l a v b k q x y : Array S w}
    (hu : packed (U := raw I) F inp u c) (hl : packed (U := raw I) F inp l c)
    (ha : packed (U := raw I) F inp a c) (hv : packed (U := raw I) F inp v c)
    (hb : packed (U := raw I) F inp b c) (hk : packed (U := raw I) F inp k c)
    (hq : packed (U := raw I) F inp q c) (hx : packed (U := raw I) F inp x c)
    (hy : packed (U := raw I) F inp y c) (hu' : fits u) (hl' : fits l) (ha' : fits a)
    (hv' : fits v) (hb' : fits b) (hk' : fits k) (hq' : fits q) (hx' : fits x) (hy' : fits y) :
    packed (U := raw I) F inp (fun s i =>
      test (u s i) (l s i) (a s i) (v s i) (b s i) (k s i) (q s i) (x s i) (y s i)) (c + 114) := by
  have c0 := const (U := raw I) F inp (fun _ => 0) hu.width
  have c1 := const (U := raw I) F inp (fun _ => 1) hu.width
  have off := hu.choose_eq hl (hx.choose_eq c0 c1 c0 hx' (fun _ _ => Nat.two_pow_pos _)) c1 hu' hl'
  have on := hv.choose_eq hu (hb.choose_eq hu c1 (hx.choose_eq hy c1 c0 hx' hy') hb' hu') c1 hv' hu'
  exact (ha.choose_eq hb off (hk.select hq on off hk' hq') ha' hb').mono (by omega)

open Classical in
/-- A single circuit checks all unused-slot pins and relay equalities.
The pair counts, skip offsets and current processor may vary with the
input. The link tape is selected by a fixed list of bit names. -/
theorem valid [NeZero R] {q : S → Fin R → Fin R → ℕ} {u : S → Fin R}
    (hr : 2 ≤ R) (hn : 64 * R ^ 2 ≤ N) (hw : N ≤ 2 ^ w)
    (hs : ∀ s a b, q s a b = q s b a) (hq : ∀ s a, ∑ b, q s a b ≤ N / 64)
    (hcount : packed (U := raw I) F inp (matrix w q) c)
    (hskip : packed (U := raw I) F inp (matrix w (fun s => Diagonal.Links.skip (q s))) c)
    (hu : packed (U := raw I) F inp (fun s (_ : B w) => (u s).val) c)
    (t : Fin (N / 4) → I) :
    ∃ b : (I → Bool) → Unit → Bool, Install.BNet F b (2 ^ w * (100 + w) ^ (c + 416)) ∧
      ∀ s, b (inp s) () = decide (Diagonal.Links.valid (hs s) (hq s) hn (u s) (inp s ∘ t)) := by
  have hr' : R ≤ R ^ 2 := Nat.le_pow (by decide)
  have h2 : 1 < 2 ^ w := by omega
  have h1 : 1 ≤ w := Nat.one_le_iff_ne_zero.mpr (fun h => by simp [h] at h2)
  let _ : NeZero (N / 4) := ⟨by omega⟩
  let ix (j : B w) := t (Fin.ofNat (N / 4) j.val)
  let tape (s : S) (j : ℕ) := inp s (ix (Fin.ofNat (2 ^ w) j))
  have ht (s : S) : (fun i : Fin (N / 4) => tape s i.val) = inp s ∘ t := by
    funext i
    have hi : i.val < 2 ^ w := by omega
    have he : Fin.ofNat (N / 4) (Fin.ofNat (2 ^ w) i.val).val = i :=
      Fin.ext (by simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt i.isLt])
    simp only [tape, ix, he, Function.comp_apply]
  obtain ⟨p, hp, hcover, ha, hrelay, hj, hlo, haddr⟩ := relay_lanes hr hn hw hu
  obtain ⟨hm, hk, hlen, hpeer⟩ :=
    decode_slot hn hw hq (hcount.mono (by omega)) (hskip.mono (by omega)) ha hrelay hj
  have hbit := named F inp ix hu.width
  have hx := hbit.lookup haddr
  have hy := hbit.lookup hpeer
  have fit (a : S → B w → Fin R) : fits (fun s i => (a s i).val) :=
    fun s i => (a s i).isLt.trans_le (by omega)
  have hkey : fits (fun s i => Diagonal.Links.index (q s) (p s i)) :=
    fun _ _ => (index_lt_of_size _).trans_le hw
  have hq' (s) (a b : Fin R) : q s a b < 2 ^ w := by
    have hg := (Finset.single_le_sum (fun i _ => Nat.zero_le (q s a i)) (Finset.mem_univ b)).trans (hq s a)
    omega
  have hb (b : Bool) : b.toNat < 2 ^ w := by cases b <;> simp [h2]
  let f (s : S) (i : B w) :=
    let j := p s i
    test (u s).val j.1.val.1.val (sender j).val (relay j).val (mate (q s) j).val
      (Diagonal.Links.index (q s) j) (q s (sender j) (mate (q s) j)) (tape s (address j).val).toNat
      (tape s (peer (q s) j)).toNat
  have hf : packed (U := raw I) F inp f (c + 300 + 114) :=
    test_net (hu.mono (by omega)) (hlo.mono (by omega)) (ha.mono (by omega))
      (hrelay.mono (by omega)) (hm.mono (by omega)) (hk.mono (by omega))
      (hlen.mono (by omega)) (hx.mono (by omega)) (hy.mono (by omega))
      (fit _) (fit _) (fit _) (fit _) (fit _) hkey (fun s _ => hq' s _ _)
      (fun _ _ => hb _) (fun _ _ => hb _)
  obtain ⟨b, hb, he⟩ := conjunction h1 hf (fun s i => (test_le ..).trans_lt h2)
  refine ⟨b, hb, fun s => ?_⟩
  rw [he, decide_eq_decide, ← ht, valid_iff_check]
  constructor
  · intro h p' hp'
    obtain ⟨i, rfl⟩ := hcover s p' hp'
    exact (test_eq ..).mp (h i)
  · intro h i
    exact (test_eq ..).mpr (h _ (hp s i))

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

/-!
# Pair lengths and processor offsets for accepted reports

The register bound need only hold at the guaranteed input reports.
All circuit statements still involve a single computation independent
of the report.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Classical Diagonal Install Coloring
variable {F S I : Type} [Field F] [Fintype I] {N l n h r d w : ℕ}
  [LinearOrder (Name n r)] (A : Expansion F n h) (hn : 2 ≤ n)
  (fa : Machine.Ports N l l → Label n r)

/-- Bounds with slack so all addresses in the table fit in a register. -/
structure Limits (A : Expansion F n h) (N r d w : ℕ) : Prop where
  large : 100000000 ≤ w
  cube : 2 ^ n ≤ w
  bits : N ≤ 2 ^ w
  pos : 0 < r
  power : r ^ (16 * n) ≤ 2 ^ w
  pairs : (3 * r) ^ 5 ≤ 2 ^ w
  selectors : Fintype.card A.I ≤ w
  charge : ∀ i z, 512 * A.chargeBits i z ≤ w
  packets : Fintype.card (Packet n r d) < (2 ^ w) ^ 8
  queries : Fintype.card (Query n r) ≤ 2 ^ w
  counts : Fintype.card (A.CountBit r d) ≤ 2 ^ w

private theorem capacity_bound {X Y Z w : ℕ} (hX : X ≤ 2 ^ w) (hY : Y ≤ 2 ^ w) (hZ : Z ≤ 2 ^ w) :
    X + 4 * 2 ^ w * w + Z * w + (X + 2 * Y + 2 ^ w * w ^ 48) ≤ 2 ^ w * (100 + w) ^ 49 := by
  have he : 1 + w ≤ (100 + w) ^ 48 :=
    (by omega : 1 + w ≤ 100 + w) |>.trans (Nat.le_pow (by decide : 0 < 48))
  have hp : w ^ 48 ≤ (100 + w) ^ 48 := by gcongr; omega
  calc
    _ ≤ 2 ^ w + 4 * 2 ^ w * w + 2 ^ w * w + (2 ^ w + 2 * 2 ^ w + 2 ^ w * w ^ 48) := by gcongr
    _ = 2 ^ w * (4 + 5 * w + w ^ 48) := by ring
    _ ≤ 2 ^ w * ((100 + w) ^ 48 * 6) := by apply Nat.mul_le_mul_left; omega
    _ ≤ _ := by rw [show (100 + w) ^ 49 = (100 + w) ^ 48 * (100 + w) from pow_succ ..]; gcongr; omega

theorem packed_lengths (hw : Limits A N r d w) (hi : Fintype.card I ≤ 2 ^ w)
    (inp : S → I → Bool) (idx : A.CountBit r d → I) (rep : S → A.Report r d) (i : Fin n)
    (hc : ∀ s, (rep s).1 = i) (he : ∀ s, inp s ∘ idx = A.countBits (rep s))
    (q : B w → Query n r) :
    Vector.packed (U := Vector.raw I) F inp
      (fun s j => addressSum A hn fa (rep s).1 (q j) (A.countBits (rep s))) 49 := by
  have hg := (addresses_size A hn fa i hw.large hw.bits hw.pos hw.power hw.cube hw.selectors
    (hw.charge i) hw.packets).1.pull idx
  refine Vector.packed.reshape _ q hg (capacity_bound hi hw.counts hw.queries) ?_
  intro s j b
  rw [he, hc]
  rfl

variable [Fintype F] {t B : ℕ} {P : Processor.Format N l t n r h}
  {M : Bank (Fin n)} {A hn} (C : Controller P A hn M B)

namespace Controller

def pairCount (R : P.Reports A hn B) : Fin (3 * r) → Fin (3 * r) → ℕ :=
  Links.count (Encoded.left (A.extraSrc hn N R.1 (Worker.index r) (Pin.src (P.route A hn B R)))
    (A.extraDst hn N R.1 (Worker.index r) (Pin.dst (P.route A hn B R))) (A.extraSize R.1))
    (Encoded.right (A.extraSrc hn N R.1 (Worker.index r) (Pin.src (P.route A hn B R)))
    (A.extraDst hn N R.1 (Worker.index r) (Pin.dst (P.route A hn B R))) (A.extraSize R.1))

omit [LinearOrder (Name n r)] in
include C in
theorem pairSum (R : P.Reports A hn B) (u : Fin (3 * r)) :
    ∑ v, pairCount R u v ≤ N / 64 :=
  Encoded.count_bound _ _ _
    (A.extra_bound hn N R.1 (Worker.index r) R.2.2 _ _ (C.pins R.1)) u

variable [NeZero (3 * r)] (hw : Limits A N r (B * P.count) w) (hi : Fintype.card I ≤ 2 ^ w)
  (inp : S → I → Bool) (idx : A.CountBit r (B * P.count) → I)
  (rep : S → P.Reports A hn B) (i : Fin n)
  (hc : ∀ s, (rep s).1.1 = i) (he : ∀ s, inp s ∘ idx = A.countBits (rep s).1)

omit [Fintype F] in
include hw hi hc he in
theorem packed_count :
    Vector.packed (U := Vector.raw I) F inp (Vector.matrix w (fun s => pairCount (rep s))) 49 := by
  let get (u : Coloring.B w) : Query n r :=
    ((Vector.atPair (3 * r) u).1, (Vector.atPair (3 * r) u).2, none)
  have hp := packed_lengths A hn P.colors hw hi inp idx (fun s => (rep s).1) i hc he get
  convert hp using 1
  funext s j
  unfold Vector.matrix get
  rw [addressSum_total]
  exact (grouping P.colors A hn (rep s).1).channels.count _ _

include C hw hi hc he in
theorem packed_skip :
    Vector.packed (U := Vector.raw I) F inp (Vector.matrix w (fun s => Links.skip (pairCount (rep s)))) 62 := by
  apply (packed_count hw hi inp idx rep i hc he).skip hw.pairs
  intro s u v
  have ht : pairCount (rep s) u v ≤ N / 64 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)).trans (C.pairSum _ u)
  have := Nat.lt_two_pow_self (n := w)
  have := hw.large
  have := hw.bits
  omega

end Controller
end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-! # Inspecting arbitrary endpoint metadata in parallel -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Classical Diagonal Install

variable {F S I : Type} [Field F] [Fintype I] {N l n h r d w : ℕ}
  [LinearOrder (Name n r)] (A : Expansion F n h) (hn : 2 ≤ n)
  (fa : Machine.Ports N l l → Label n r)

include fa in
theorem packed_observe (hw : Limits A N r d w) (hi : Fintype.card I ≤ 2 ^ w)
    (inp : S → I → Bool) (idx : A.CountBit r d → I) (rep : S → A.Report r d) (i : Fin n)
    (hc : ∀ s, (rep s).1 = i) (he : ∀ s, inp s ∘ idx = A.countBits (rep s))
    (keys : Coloring.B w → Name n r) (f : Coloring.B w → Worker r → Worker r → ℕ) :
    Vector.packed (U := Vector.raw I) F inp (fun s j =>
      f j (descriptor A hn N (rep s) (keys j)).1 (descriptor A hn N (rep s) (keys j)).2.1) 49 := by
  let read (t : Fin r → Bool) (p : Coloring.B w × slots (word w)) :=
    let q := pairOf hn i t (keys p.1)
    digits w (f p.1 q.1 q.2) p.2
  have hr : Depends read 3 := by
    intro p
    obtain ⟨T, hT, h⟩ := support hn i (keys p.1)
    exact ⟨T, hT, fun x y he => by unfold read; rw [h x y he]⟩
  have hg := (addresses_size A hn fa i hw.large hw.bits hw.pos hw.power hw.cube hw.selectors
    (hw.charge i) hw.packets).2.pull idx
  apply Vector.packed.of_net _ (hg.comp (hr.bnet F))
  · have h₁ : r ≤ 2 ^ w := (Nat.le_pow (by omega : 0 < 16 * n)).trans hw.power
    have h₂ : 5 + 135 * w ≤ (100 + w) ^ 48 := by
      refine le_trans ?_ (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 48))
      ring_nf
      omega
    have h₃ : w ^ 48 ≤ (100 + w) ^ 48 := by gcongr; omega
    simp only [Fintype.card_prod (Coloring.B w), Fintype.card_fin, card_slots, wd_word]
    calc
      _ ≤ 2 ^ w + 2 ^ w * w + (2 ^ w + 2 * 2 ^ w + 2 ^ w * w ^ 48 + (2 ^ w + 134 * (2 ^ w * w))) := by
        change _ + _ + (_ + 2 * Fintype.card (A.CountBit r d) + _ + (_ + 134 * _)) ≤ _
        have := hw.counts
        gcongr
      _ = 2 ^ w * (5 + 135 * w + w ^ 48) := by ring
      _ ≤ 2 ^ w * ((100 + w) ^ 48 * 2) := by apply Nat.mul_le_mul_left; omega
      _ ≤ _ := by rw [pow_succ (100 + w) 48]; gcongr; omega
  · intro s j k
    change read (A.groupFlags N i (inp s ∘ idx)) (j, k) = _
    simp only [read, he, ← hc s, pairOf_report]

end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-! # Checking relay consistency directly from the public input bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Diagonal Install Classical OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l d B n r h w : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B)

structure Invocation (i : Fin n) where
  site : Fin (3 * r)
  script : M.Bits F → Bool
  report : P.Reports A hn B
  physical : Fin (N / 4) → Bool
  cut : report.val.1 = i
  feasible : A.feasible hn report.val

variable {i : Fin n}

def input (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i) :
    Machine.Ports N l l → Bool :=
  Sum.elim (C.code (some (s.site, s.script)))
    (Sum.elim (A.encodeReport hn N r (B * P.count) l C.fits (some s.report)) s.physical)

def countPort (c : A.CountBit r (B * P.count)) : Machine.Ports N l l :=
  .inr (.inl (A.reportPort _ _ _ C.fits (.inr (.inr c))))

theorem counts_eq (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i) :
    C.input s ∘ C.countPort = A.countBits s.report.val :=
  funext fun j => A.encodeReport_count _ _ _ _ _ _ _ j

theorem worker_net (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w)
    (hr : 3 * r ≤ 2 ^ w) :
    packed (U := raw _) F (C.input (i := i)) (fun s (_ : Coloring.B w) => s.site.val) 5 := by
  let read : Fin (3 * r) → Machine.Ports N l l :=
    fun j => .inl (M.literalPort F l r C.literal (.inr (.inl j)))
  let f (x : Machine.Ports N l l → Bool) (t : Unit × slots (word w)) :=
    digits w (∑ j, if x (read j) then j.val else 0) t.2
  have hn := (BNet.pull (Register.weighted F w (fun j : Fin (3 * r) => j.val)) read).rename
    (.refl _) (Equiv.uniqueProd _ Unit).symm
  apply packed.reshape f (fun _ => ()) hn
  · simp only [Fintype.card_unit, Fintype.card_fin]
    have he : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by decide)
    have hs : 50000 * (w + 1) ≤ (100 + w) ^ 5 := by ring_nf; omega
    have hc := Nat.mul_le_mul_left (2 ^ w) hs
    nlinarith only [hc, hr, hi, he, Nat.mul_le_mul_right w hr, Nat.mul_le_mul_right w he]
  · intro s j b
    simp only [f, input, read, Sum.elim_inl, code, Bank.literalCode_worker, decide_eq_true_eq,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit [Fintype F] in
theorem pairSymm (R : P.Reports A hn B) (u v : Fin (3 * r)) : pairCount R u v = pairCount R v u :=
  Links.count_symm _ _ _ _

variable [NeZero (3 * r)] [LinearOrder (Name n r)]

def relay (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i) :=
  Links.valid (pairSymm s.report) (C.pairSum s.report) C.links s.site s.physical

/-- One circuit works for all feasible reports, processor identifiers
and scripts at this cut. It pins unused slots and checks every relay. -/
theorem relay_net (hw : Limits A N r (B * P.count) w)
    (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w) (i : Fin n) :
    ∃ t : (Machine.Ports N l l → Bool) → Unit → Bool,
      BNet F t (2 ^ w * (100 + w) ^ (62 + 416)) ∧ ∀ s, t (C.input (i := i) s) () = decide (C.relay s) := by
  let X := Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i
  have hg := packed_count hw hi C.input C.countPort (fun s : X => s.report) i Invocation.cut (C.counts_eq)
  have hs := C.packed_skip hw hi C.input C.countPort (fun s : X => s.report) i Invocation.cut (C.counts_eq)
  have hr := hw.pos
  have he := C.worker_net (i := i) hi ((Nat.le_pow (by decide : 0 < 5)).trans hw.pairs)
  obtain ⟨f, hf, hf'⟩ := packed.valid (u := fun s : X => s.site) (c := 62) (by omega)
    C.links hw.bits (fun s : X => pairSymm s.report) (fun s : X => C.pairSum s.report)
    (hg.mono (by decide)) hs (he.mono (by decide)) (fun j => .inr (.inr j))
  exact ⟨f, hf, fun s => hf' s⟩

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# Separating bit and class symbols at one worker

A shared bit has exactly one specified physical address. Private
bits and class symbols remain independent summation variables.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Classical Diagonal
variable {F : Type} [Field F] [Fintype F] {N l n d r h B : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) {i : Fin n}

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

abbrev Bit (P : Format N l d n r h) (B : ℕ) := Pin N l l r ⊕ (Position n r (B * P.count) h × Bool)
abbrev Edge (P : Format N l d n r h) (B : ℕ) := Pin N l l r ⊕ Expansion.Edge n r (B * P.count) h

def wrap : Bit P B → Edge P B
  | .inl q => .inl q
  | .inr q => .inr (.inl q)

abbrev source (s : X) := A.extraSrc hn N s.report.1 (Worker.index r) (Pin.src (P.route A hn B s.report))
abbrev target (s : X) := A.extraDst hn N s.report.1 (Worker.index r) (Pin.dst (P.route A hn B s.report))
abbrev width (s : X) : Edge P B → ℕ := A.extraSize s.report.1
abbrev workerAt (s : X) := (Worker.index r).symm s.site
abbrev incident (s : X) (e : Edge P B) := source s e = s.site ∨ target s e = s.site

def receive (s : X) (z : Encoded.Bits (source s) (target s) (width s)) (he : incident s z.1.val) :=
  s.physical (Encoded.location (source s) (target s) (width s)
    (A.extra_bound hn N s.report.1 (Worker.index r) s.report.2.2 _ _ (C.pins s.report.1))
    C.links (C.number s.report) s.site z he)

def physicalBit (s : X) (e : Edge P B) (j : ℕ) : Bool :=
  if h : source s e ≠ target s e ∧ incident s e ∧ j < width s e then
    C.receive s ⟨⟨e, h.1⟩, ⟨j, h.2.2⟩⟩ h.2.1 else false

abbrev LocalBit (s : X) := {q : Bit P B // incident s (wrap q)}

def fullBit (s : X) (x : LocalBit s → Bool) (q : Bit P B) :=
  if h : incident s (wrap q) then x ⟨q, h⟩ else false

def Matches (s : X) (x : LocalBit s → Bool) : Prop :=
  ∀ q, source s (wrap q.val) ≠ target s (wrap q.val) → x q = C.physicalBit s (wrap q.val) 0

abbrev Classes (s : X) := PacketKernel.Incident A hn N s.report.1 (workerAt s)
abbrev Symbols (s : X) := PacketKernel.Family A hn N s.report.1 (workerAt s)
abbrev Local (s : X) :=
  Encoded.Local (source s) (target s) (A.ExtraSymbol hn N s.report.1) s.site

omit [Fintype F] in
theorem class_here (s : X) (c : Class r) : incident s (.inr (.inr c)) ↔
    A.src hn N s.report.1 (.inr c) = workerAt s ∨ A.dst hn N s.report.1 (.inr c) = workerAt s := by
  simp only [workerAt, incident, source, target, Expansion.extraSrc, Expansion.extraDst,
    Function.comp_apply, Sum.elim_inr, Equiv.eq_symm_apply]

def localEquiv (s : X) : (LocalBit s → Bool) × Symbols s ≃ Local s where
  toFun y
    | ⟨.inl j, h⟩ => y.1 ⟨.inl j, h⟩
    | ⟨.inr (.inl j), h⟩ => y.1 ⟨.inr j, h⟩
    | ⟨.inr (.inr c), h⟩ => y.2 ⟨c, (class_here s c).mp h⟩
  invFun x := (fun
    | ⟨.inl j, h⟩ => x ⟨.inl j, h⟩
    | ⟨.inr j, h⟩ => x ⟨.inr (.inl j), h⟩,
    fun c => x ⟨.inr (.inr c.val), (class_here s _).mpr c.property⟩)
  left_inv y := by
    apply Prod.ext
    · funext k; rcases k with ⟨j|j, h⟩ <;> rfl
    · rfl
  right_inv x := by funext k; rcases k with ⟨j|j|j, h⟩ <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# A fixed-size table of potentially incident slot keys

A home or station worker uses just its coordinate slice of the
possible endpoints. A packet worker instead uses the auxiliary
coordinate of the first template label. The size is the same for
all three roles, regardless of the heavy set.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Diagonal Spectral Classical Finset
abbrev SlotKey (n r : ℕ) := Template n r × Cube n × Bool

namespace SlotKey
variable {n r h t : ℕ}

def key (p : Position n r t h × Bool) : SlotKey n r := (p.1.1.1, p.1.2.1, p.2)
def atRow (k : SlotKey n r) (i : Fin t) (j : Fin h) : Position n r t h × Bool :=
  (((k.1, i), k.2.1, j), k.2.2)

def label (k : SlotKey n r) := corner k.1 (if k.2.2 then Cube.flip univ k.2.1 else k.2.1)

variable (hn : 2 ≤ n) (i : Fin n)

def focus (u : Worker r) (k : SlotKey n r) : Fin r :=
  match u with
  | .home _ => k.label i
  | .station _ => k.label (other hn i)
  | .packet _ => k.1.1 (other hn i)

abbrev Visible (u : Worker r) := {k : SlotKey n r // focus hn i u k = Layout.symbol u}

private theorem template_uniform (j : Fin n) (b : Bool) (g : Fin r) :
    multiplicity (fun t : Template n r => group t j b) g * r = Fintype.card (Template n r) := by
  have h := group_uniform (d := 1) j b g
  let e := Equiv.prodUnique (Template n r) (Fin 1)
  have hf : multiplicity (fun t : Packet n r 1 => group t.1 j b) g =
      multiplicity (fun t : Template n r => group t j b) g :=
    Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))
  rwa [hf, Fintype.card_congr e] at h

theorem visible_uniform (u : Worker r) :
    Fintype.card (Visible hn i u) * r = Fintype.card (SlotKey n r) := by
  have h (x : Cube n × Bool) :
      multiplicity (fun t : Template n r => focus hn i u (t, x)) (Layout.symbol u) * r =
        Fintype.card (Template n r) := by
    cases u with
    | home g => exact template_uniform i ((if x.2 then Cube.flip univ x.1 else x.1) i) g
    | station g =>
      exact template_uniform (other hn i)
          ((if x.2 then Cube.flip univ x.1 else x.1) (other hn i)) g
    | packet g => exact template_uniform (other hn i) false g
  have he : Fintype.card (Visible hn i u) =
      ∑ x : Cube n × Bool, multiplicity (fun t : Template n r => focus hn i u (t, x)) (Layout.symbol u) := by
    simp only [Visible, Diagonal.multiplicity, Fintype.card_subtype]
    have hw (p : SlotKey n r → Prop) [DecidablePred p] :
        (univ.filter p).card = ∑ x, if p x then 1 else 0 := by simp
    rw [hw, Fintype.sum_prod_type, sum_comm]
    simp
  rw [he, sum_mul]
  simp only [h, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]
  rw [Fintype.card_prod (Template n r), mul_comm]

def count (n r : ℕ) := Fintype.card (SlotKey n r) / r

def enumerate (u : Worker r) : Fin (count n r) ≃ Visible hn i u :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, count, ← visible_uniform hn i u]
    exact Nat.mul_div_cancel _ (Layout.symbol u).pos)

variable {F : Type} [Field F] (A : Expansion F n h) (N : ℕ) (R : A.Report r t)

theorem visible_src (q : Position n r t h × Bool) :
    let u := A.src hn N R (.inl q)
    focus hn R.1 u (key q) = Layout.symbol u := by
  rcases q with ⟨p, b⟩
  simp only [Expansion.src, Expansion.owner]
  split <;> rfl

theorem visible_dst (q : Position n r t h × Bool) :
    let u := A.dst hn N R (.inl q)
    focus hn R.1 u (key q) = Layout.symbol u := by
  rcases q with ⟨p, b⟩
  simp only [Expansion.dst]
  split
  · exact visible_src hn A N R (p, b)
  · rfl

end SlotKey
end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-! # Separating the bit and class checks in the physical input -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Classical Diagonal
variable {F : Type} [Field F] [Fintype F] {N l n d r h B : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) {i : Fin n}
  (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i)

abbrev Received (v : Local s) :=
  Encoded.receives (source s) (target s) (A.ExtraSymbol hn N s.report.1) (width s)
    (A.extraCode hn N s.report.1)
    (A.extra_bound hn N s.report.1 (Worker.index r) s.report.2.2 _ _ (C.pins s.report.1))
    C.links (C.number s.report) s.site s.physical v

private theorem received_iff (v : Local s) :
    C.Received s v ↔ ∀ (e : Edge P B) (he : incident s e), source s e ≠ target s e →
      ∀ j, A.extraCode hn N s.report.1 e (v ⟨e, he⟩) j = C.physicalBit s e j.val := by
  have atBit (e : Edge P B) (hi : incident s e) (he : source s e ≠ target s e)
      (j : Fin (width s e)) : C.physicalBit s e j.val = C.receive s ⟨⟨e, he⟩, j⟩ hi := by
    rw [physicalBit, dite_eq_left ⟨he, hi, j.isLt⟩]
  constructor
  · intro h e hi he j
    rw [atBit e hi he j]
    exact h ⟨e, he⟩ hi j
  · rintro h ⟨e, he⟩ hi j
    exact (h e hi he j).trans (atBit e hi he j)

def streams (z : Symbols s) : Prop :=
  ∀ c : Classes s, A.src hn N s.report.1 (.inr c.val) ≠ A.dst hn N s.report.1 (.inr c.val) →
    ∀ j, A.alphabetCode hn N s.report.1 c.val (z c) j = C.physicalBit s (.inr (.inr c.val)) j.val

theorem received_split (x : LocalBit s → Bool) (z : Symbols s) :
    C.Received s (localEquiv s (x, z)) ↔ C.Matches s x ∧ C.streams s z := by
  rw [received_iff]
  constructor
  · intro h
    constructor
    · rintro ⟨e|e, hi⟩ he
      · exact h (.inl e) hi he (0 : Fin 1)
      · exact h (.inr (.inl e)) hi he (0 : Fin 1)
    · intro c he j
      exact h (.inr (.inr c.val)) ((class_here s _).mpr c.2) ((Worker.index r).injective.ne he) j
  · rintro ⟨hx, hz⟩ (e|e|c) hi he j
    · change Fin 1 at j
      rw [Fin.eq_zero j]
      exact hx ⟨.inl e, hi⟩ he
    · change Fin 1 at j
      rw [Fin.eq_zero j]
      exact hx ⟨.inr e, hi⟩ he
    · exact hz ⟨c, (class_here s c).mp hi⟩ (fun h => he (congrArg (Worker.index r) h)) j

omit [Fintype F] in
theorem symbols_exist :
    Nonempty ((e : Edge P B) → A.ExtraSymbol hn N s.report.1 e) :=
  (A.feasible_symbols hn s.report.1 N).mp s.feasible

/-- This is the extension in the localization of a vertex table. -/
def extendLocal (x : LocalBit s → Bool) (z : Symbols s) (e : Edge P B) :
    A.ExtraSymbol hn N s.report.1 e :=
  if he : incident s e then localEquiv s (x, z) ⟨e, he⟩ else (choice (symbols_exist s)) e

def localAssignment (x : LocalBit s → Bool) (z : Symbols s) : A.Assignment hn N s.report.1 :=
  fun e => extendLocal s x z (.inr e)

omit [Fintype F] in
theorem assigned_class (x : LocalBit s → Bool) (z : Symbols s) (c : Classes s) :
    localAssignment s x z (.inr c.val) = z c := by
  unfold localAssignment extendLocal
  rw [dite_eq_left ((class_here s c.val).mpr c.2)]
  rfl

omit [Fintype F] in
theorem fullBit_at (x : LocalBit s → Bool) (q : Bit P B) (he : incident s (wrap q)) :
    fullBit s x q = x ⟨q, he⟩ := by rw [fullBit, dite_eq_left he]

omit [Fintype F] in
theorem assigned_row (x : LocalBit s → Bool) (z : Symbols s) (p : Position n r (B * P.count) h × Bool)
    (hp : incident s (.inr (.inl p))) :
    localAssignment s x z (.inl p) = fullBit s x (.inr p) := by
  unfold localAssignment extendLocal
  rw [dite_eq_left hp, fullBit_at s x (.inr p) hp]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end
