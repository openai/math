import OAI.Geometry.Hirsch.Endpoints

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

variable {I Ω : Type} [Fintype Ω] [Fintype I] {p : Law Ω} {pins : Pins p I}
  {n K : ℕ} {w : Board I n} {gamma alpha : ℝ} (gate : Trial.Gates pins w.place K gamma alpha)

structure Depths (K : ℕ) where
  step : ℕ
  pos : 1 ≤ step

namespace Depths

variable (D : Depths K)

def low := (K+2)*D.step
def near := D.low+1
def limit := (3*K+6)*D.near
def band := D.limit + (K+2)*D.step
def max := D.band+1+(K+2)*D.step

theorem order : D.step ≤ D.low ∧ 1 ≤ D.near ∧ 4*D.near ≤ D.limit ∧ D.limit ≤ D.band ∧ D.band < D.max := by
  have h := Nat.mul_le_mul_right D.step (by omega : 1 ≤ K+2)
  have h' := Nat.mul_le_mul_right D.near (by omega : 4 ≤ 3*K+6)
  simp only [low,near,limit,band,max] at *
  omega

end Depths

structure Ledger (old : w.Round) (area : Set ℕ) (d : Bool) (D : Depths K) (M A : ℝ) : Prop where
  link : 0 ≤ A
  mass : 0 ≤ M
  available : ∀ x g, w.place g ∈ area → ¬gate.bad g x →
    ∃ l ∈ old.test area (!d) (flat D.step) g, ∀ j ∈ l, j ∈ gate.pass x → w.place j = w.place g
  bounds : ∀ r : w.Round, r.Finer old → ∀ i, w.place i ∈ area → ∀ a b : Budget,
    a ≤ flat D.max → a + flat D.step ≤ b →
    gate.Bounds (gate.cuts (r.test area (!d) a i) (r.test area (!d) b i)) M A

namespace Ledger

variable {gate} {old r q : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}

def tests (hr : r.Finer old) (i : I) (a b : Budget) (he : a ≤ flat D.max) (hb : a + flat D.step ≤ b) :
    Trial.Tests w.place D.max D.step :=
  { r.tests area (!d) i a b _ _ he hb with
    next := fun g => if w.place g ∈ area then old.test area (!d) (flat D.step) g else {[]}
    transfer := by
      rintro pre g rest ⟨j,_,ht⟩ s hc hn hg
      have hi := (ht.member (by simp : g ∈ pre ++ g :: rest)).1
      simp only [ite_eq_left hi]
      exact hr.test le_rfl _ (Round.transfers _ hb pre g rest ⟨j,ht⟩ s hc hn hg)
    nextBound := by
      intro g
      split
      · exact fun l ⟨_,_,ht⟩ x => ht.bound x
      · rintro l rfl x; simp [Trial.keysAt] }

omit [Fintype I] in
theorem serves (hr : r.Finer old) (i : I) (a b : Budget) (he : a ≤ flat D.max) (hb : a + flat D.step ≤ b)
    (hav : ∀ x g, w.place g ∈ area → ¬gate.bad g x →
      ∃ l ∈ old.test area (!d) (flat D.step) g, ∀ j ∈ l, j ∈ gate.pass x → w.place j = w.place g) :
    gate.Serves (tests (area := area) (d := d) hr i a b he hb) := by
  intro x g hh
  simp only [tests]
  split
  · exact hav x g ‹_› hh
  · exact ⟨[],rfl,by simp⟩

theorem make {U : ℝ} (hg : 0 < gamma) (ha : 0 ≤ alpha) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (change : ∀ z, Nonempty (gate.Resample z))
    (hm : (Trial.Tests.capacity K D.max D.step : ℝ)*U ≤ gamma*M)
    (hl : (Trial.Tests.capacity K D.max D.step : ℝ)*(alpha+(K*D.max+D.step+1)*pins.rate) ≤ gamma*A)
    (hav : ∀ x g, w.place g ∈ area → ¬gate.bad g x →
      ∃ l ∈ old.test area (!d) (flat D.step) g, ∀ j ∈ l, j ∈ gate.pass x → w.place j = w.place g)
    (cap : ∀ i, w.place i ∈ area → p.prob (fun x => (old.test area (!d) (flat D.step) i).Covers (gate.pass x)) ≤ U) :
    Ledger gate old area d D M A := by
  refine ⟨hA,hM,hav,fun r hr i hi a b he hb => ?_⟩
  apply Trial.Gates.bounds (serves hr i a b he hb hav) hg ha change _ hm hl
  exact (p.mono fun x h => hr.test (le_add_self.trans hb) _ h).trans (cap i hi)

variable (L : Ledger gate old area d D M A) {i : I} {f : ℕ} {b : Budget} {s : Finset I}

def book (_L : Ledger gate old area d D M A) (r : w.Round) (i : I) (b : Budget) :=
  gate.cuts (r.test area (!d) (flat D.near) i) (r.test area (!d) b i)

theorem mem : s ∈ L.book r i b ↔ s.card ≤ K ∧ (r.test area (!d) b i).Covers s ∧
    (r.test area (!d) (flat D.near) i).Minimal s ∧ gate.Possible s := gate.mem_cuts

theorem sub {a : Budget} (h : a ≤ b) : L.book r i b ⊆ L.book r i a := by
  intro s hs
  obtain ⟨hk,hc,hm,hp⟩ := L.mem.mp hs
  exact L.mem.mpr ⟨hk,Round.test_mono _ _ _ _ h _ hc,hm,hp⟩

def loss (_L : Ledger gate old area d D M A) := (K+1)*A*M
def key (_L : Ledger gate old area d D M A) := (1+A)*pins.rate
def beta := 2*M * (K*(L.key+L.loss))

theorem positive : 0 ≤ L.loss ∧ 0 ≤ L.key ∧ 0 ≤ L.beta := by
  have := L.link
  have := L.mass
  have := pins.pos
  unfold beta key loss
  constructor
  · positivity
  constructor <;> positivity

theorem bound (hr : r.Finer old) (hi : w.place i ∈ area) (hb : flat (2*D.near) ≤ b) :
    gate.Bounds (L.book r i b) M A := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := D.order
  apply L.bounds r hr i hi
  · exact fun _ => show D.near ≤ D.max by omega
  · apply le_trans _ hb
    intro x; simp only [Pi.add_apply,flat,Depths.near]; omega

theorem discard {B : Finset (Finset I)} (hb : gate.Bounds B M A) (hr : r.Finer old)
    (hi : w.place i ∈ area) (hf : D.low ≤ f) :
    pins.mass (B.filter fun t => ¬(r.test area (!d) (flat f) i).Minimal t) ≤ L.loss := by
  let paths := fun j => r.test area (!d) (flat ((j+1)*D.step)) i
  apply le_trans _ (hb.loss L.link paths (by
    intro j hj
    apply Trial.Gates.Bounds.mass (L.bounds r hr i hi _ _ ?_ ?_)
    · have := Nat.mul_le_mul_right D.step (by omega : j+1 ≤ K+2)
      exact fun _ => show (j+1)*D.step ≤ D.max by unfold Depths.max; omega
    · intro x; simp only [Pi.add_apply,flat,add_mul,one_mul]; omega))
  apply pins.mass_mono
  intro s hs
  obtain ⟨hs,hn⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_filter.mpr ⟨hs,fun hm => hn fun t ht hc =>
    hm _ ht (Round.test_mono _ _ _ _ (fun _ => hf) _ hc)⟩

def core (_L : Ledger gate old area d D M A) (r : w.Round) (hi : w.place i ∈ area)
    (hf : 2*D.near ≤ f) := r.core area d D.near f i hi D.order.2.1 hf

theorem cut (hi : w.place i ∈ area) (hf : 2*D.near ≤ f) (hs : s ∈ L.book r i (flat f)) :
    (L.core r hi hf).Cut s := ⟨(L.mem.mp hs).2.1,(L.mem.mp hs).2.2.1⟩

theorem bad (hr : r.Finer old) (hi : w.place i ∈ area) (hf : 2*D.near ≤ f)
    {B C : Finset (Finset I)} (hB : B ⊆ L.book r i (flat f)) (hC : C ⊆ L.book r i (flat f)) :
    pins.pairMass B C (fun s t => ¬(L.core r hi hf).Good s t) ≤ L.beta := by
  let c := L.core r hi hf
  let list := L.book r i (flat f)
  have hb := L.bound hr hi (show flat (2*D.near) ≤ flat f from fun _ => hf)
  have hs : ∀ s ∈ list, ∀ g ∈ s, w.place g ∈ area := fun _ h _ hg =>
    Round.keys_inside (c.refines _ (L.cut hi hf h).1) (L.cut hi hf h).2 hg
  have hbad := c.bad_pairs pins list L.positive.2.1 L.positive.1
    (fun _ h => (L.mem.mp h).1) hb.key
    (fun g hg => L.discard hb hr (by obtain ⟨s,h,hg⟩ := hg; exact hs s h g hg) (Nat.le_succ _))
  refine ((pins.pair_mono hB hC (fun _ _ _ _ h => h)).trans hbad).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb.mass (by norm_num))
    (mul_nonneg (by positivity) (add_nonneg L.positive.2.1 L.positive.1))

end Ledger
end OAI.Geometry.Hirsch.Layer.Board
