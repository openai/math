import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Processor.DispatchSize
import OAI.LinearAlgebra.MatrixExponent.Processor.Vector.Cases

/-! # Numbering a pair's virtual bits by whole channels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Diagonal
variable {R : ℕ} {E J : Type} {src dst : E → Fin R}

/-- The bits with any one key have identical endpoints. -/
structure Channels (src dst : E → Fin R) (J : Type) where
  width : J → ℕ
  left : J → Fin R
  right : J → Fin R
  label : E ≃ (Σ j, Fin (width j))
  src_eq : ∀ e, src e = left (label e).1
  dst_eq : ∀ e, dst e = right (label e).1

namespace Channels

variable [Fintype E] [Fintype J] [LinearOrder J] (c : Channels src dst J)

def widthAt (u v : Fin R) (j : J) : ℕ :=
  if c.left j = u ∧ c.right j = v ∨ c.left j = v ∧ c.right j = u then c.width j else 0

abbrev Block (u v : Fin R) := Lex (Σ j, Fin (c.widthAt u v j))

private def send {u v : Fin R} (i : Links.Between src dst u v) : c.Block u v :=
  ⟨(c.label i).1, ⟨(c.label i).2.val, by
    have h := i.property
    rw [c.src_eq, c.dst_eq] at h
    rw [widthAt, ite_eq_left h]
    exact (c.label i).2.isLt⟩⟩

omit [Fintype J] [LinearOrder J] in
private theorem sigma_eq {w : J → ℕ} {x y : (Σ j, Fin (w j))}
    (hf : x.1 = y.1) (hs : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨i, v⟩
  rcases y with ⟨j, u⟩
  change i = j at hf
  subst j
  rw [show v = u from Fin.ext hs]

private def blockEquiv (u v : Fin R) : Links.Between src dst u v ≃ c.Block u v :=
  Equiv.ofBijective (c.send (u := u) (v := v)) ⟨by
    intro x y h
    apply Subtype.ext
    apply c.label.injective
    have ha := congrArg Sigma.fst h
    have hb := congrArg (fun z => z.2.val) h
    exact sigma_eq ha hb, by
    intro t
    let j := t.1
    have hl : t.2.val < c.widthAt u v j := t.2.isLt
    unfold widthAt at hl
    split at hl
    · rename_i h
      let e := c.label.symm ⟨j, ⟨t.2.val, hl⟩⟩
      have he : c.label e = ⟨j, ⟨t.2.val, hl⟩⟩ := c.label.apply_symm_apply _
      have hp : src e = u ∧ dst e = v ∨ src e = v ∧ dst e = u := by
        rw [c.src_eq, c.dst_eq, he]
        exact h
      have ha := congrArg Sigma.fst he
      have hb := congrArg (fun z => z.2.val) he
      exact ⟨⟨e, hp⟩, sigma_eq ha hb⟩
    · omega⟩

theorem count (u v : Fin R) : Links.count src dst u v = ∑ j, c.widthAt u v j := by
  rw [Links.count, Fintype.card_congr (c.blockEquiv u v)]
  simp [Block]

def serial : Links.Numbering src dst :=
  fun u v => (Fintype.orderIsoFinOfCardEq (c.Block u v)
    (Fintype.card_congr (c.blockEquiv u v).symm)).toEquiv.trans (c.blockEquiv u v).symm

theorem serial_value {u v : Fin R} (x : Links.Between src dst u v) :
    ((c.serial u v).symm x).val =
      start (c.widthAt u v) (c.label x).1 + (c.label x).2.val :=
  serial_rank _ _ (c.blockEquiv u v x)

end Channels
end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-! # Arithmetic form of the physical address at either end of a link -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Links

variable {R N : ℕ}

def skip (q : Fin R → Fin R → ℕ) (u v : Fin R) := ∑ j ∈ Finset.Iio v, (q u j / R + 1)

/-- The parity bit identifies the endpoint and the position modulo
the processor count identifies the relay. -/
def wireAddress (R N u k base : ℕ) :=
  2 * base + 2 * (k / R) + (if u < k % R then 0 else 1) + (N / (4 * R)) * ((u + k % R) % R)

variable {q : Fin R → Fin R → ℕ} (hs : ∀ u v, q u v = q v u)
  (hq : ∀ u, ∑ v, q u v ≤ N / 64) (hn : 64 * R ^ 2 ≤ N)

theorem address_leg (l : Leg q) :
    (address (slot hs hq hn l)).val =
      wireAddress R N l.2.val.val l.1.2.val (skip q l.2.val (other l)) := by
  have he : (link l).val.1 + (link l).val.2 = l.2.val + via l.1 := by
    unfold link
    split
    · rfl
    · exact add_comm _ _
  change position l + N / (4 * R) * ((link l).val.1 + (link l).val.2).val = _
  rw [he]
  unfold position wireAddress
  rw [Nat.mul_add]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Links

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring Diagonal.Links

variable {F S : Type} [Field F] {w : ℕ} {U : Coloring.Format}
  {inp : S → U.obj} {u k b : Array S w} {R N c : ℕ}

theorem wire_address (hR : 0 < R) (hR' : 2 * R ≤ 2 ^ w)
    (hu : packed F inp u c) (hk : packed F inp k c) (hb : packed F inp b c)
    (hu' : ∀ s i, u s i < R) (hk' : fits k) (hb' : fits b) :
    packed F inp (fun s i => wireAddress R N (u s i) (k s i) (b s i)) (c + 64) := by
  let via (s : S) (i : B w) := k s i % R
  have hv' : fits via := by intro s i; have := Nat.mod_lt (k s i) hR; unfold via; omega
  have hu'' : fits u := by intro s i; have := hu' s i; omega
  have hplus : fits (fun s i => u s i + via s i) := by
    intro s i
    have := hu' s i
    have := Nat.mod_lt (k s i) hR
    change u s i + k s i % R < _
    omega
  have hv := hk.unary hk' (fun t => t % R)
  have hh := ((hu.add hv).unary hplus (fun x => (N / (4 * R)) * (x % R)))
  have ix := (hb.unary hb' (2*·)).add (hk.unary hk' (fun x => 2 * (x / R)))
  have bit := hu.select hv (const F inp (fun _ => 0) hu.width) (const F inp (fun _ => 1) hu.width)
    hu'' hv'
  exact ((ix.add bit).add hh).mono (by omega)

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-!
# Inverting the physical link schedule

Parity recovers the sending endpoint. Prefix intervals identify its
partner. The quotient inside the interval and the relay identify the
virtual bit. Unused positions, including holes at interval boundaries,
are rejected by the final index check.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Links

open Finset
variable {R N : ℕ} (q : Fin R → Fin R → ℕ)

theorem skip_step (u : Fin R) {a b : Fin R} (hab : a < b) :
    skip q u a + (q u a / R + 1) ≤ skip q u b := by
  have h : insert a (Iio a) ⊆ Iio b := by
    intro c hc
    simp only [mem_insert, mem_Iio] at hc ⊢
    omega
  have hh := sum_le_sum_of_subset (f := fun c => q u c / R + 1) h
  rw [sum_insert (by simp)] at hh
  exact (Nat.add_comm ..).le.trans hh

private theorem candidates (a : Fin R) (i : ℕ) :
    (univ.filter (fun b => skip q a b ≤ i)).Nonempty := by
  let b : Fin R := ⟨0, a.pos⟩
  have hb : Iio b = ∅ := by ext t; simp [b, Fin.lt_def]
  exact ⟨b, mem_filter.mpr ⟨mem_univ _, by simp [skip, hb]⟩⟩

def partner (a : Fin R) (i : ℕ) : Fin R :=
  (univ.filter (fun b => skip q a b ≤ i)).max' (candidates q a i)

theorem partner_spec (a : Fin R) (i : ℕ) :
    skip q a (partner q a i) ≤ i ∧ ∀ b, skip q a b ≤ i → b ≤ partner q a i :=
  ⟨(mem_filter.mp (max'_mem _ (candidates q a i))).2,
    fun b h => le_max' _ b (mem_filter.mpr ⟨mem_univ _, h⟩)⟩

theorem le_partner (a b : Fin R) (i : ℕ) : b ≤ partner q a i ↔ skip q a b ≤ i := by
  obtain ⟨hi, h⟩ := partner_spec q a i
  refine ⟨fun hb => ?_, h b⟩
  rcases hb.eq_or_lt with rfl | hb
  · exact hi
  · exact (Nat.le_add_right ..).trans ((skip_step q a hb).trans hi)

private theorem partner_at (a b : Fin R) (k : ℕ) (hk : k < q a b) :
    partner q a (skip q a b + k / R) = b := by
  obtain ⟨hi, h⟩ := partner_spec q a (skip q a b + k / R)
  apply le_antisymm _ (h b (Nat.le_add_right ..))
  by_contra! h'
  have := skip_step q a h'
  have := Nat.div_le_div_right (c := R) hk.le
  omega

def sender (p : Slot R N) : Fin R :=
  if p.2.val % 2 = 0 then p.1.val.1 else p.1.val.2

def relay (p : Slot R N) : Fin R :=
  if p.2.val % 2 = 0 then p.1.val.2 else p.1.val.1

def mate (p : Slot R N) : Fin R := partner q (sender p) (p.2.val / 2)

def index (p : Slot R N) : ℕ :=
  R * (p.2.val / 2 - skip q (sender p) (mate q p)) + (relay p).val

def active (p : Slot R N) : Prop :=
  sender p ≠ mate q p ∧ index q p < q (sender p) (mate q p)

variable {q} (hs : ∀ u v, q u v = q v u) (hq : ∀ u, ∑ v, q u v ≤ N / 64)
  (hn : 64 * R ^ 2 ≤ N)

include hs in
private theorem key (l : Leg q) : l.2.val ≠ other l ∧ l.1.2.val < q l.2.val (other l) := by
  have hp := l.1.1.property
  unfold other
  split
  · rename_i he
    rw [he]
    exact ⟨hp.ne, l.1.2.isLt⟩
  · rename_i he
    rw [l.2.property.1.resolve_left he]
    exact ⟨hp.ne', l.1.2.isLt.trans_eq (hs _ _)⟩

theorem read_slot (l : Leg q) :
    let p := slot hs hq hn l
    sender p = l.2.val ∧ relay p = via l.1 ∧ mate q p = other l ∧ index q p = l.1.2.val := by
  intro p
  have hpair : sender p = l.2.val ∧ relay p = via l.1 := by
    unfold sender relay p slot link position
    split <;> simp_all
  have hp : p.2.val / 2 = skip q l.2.val (other l) + l.1.2.val / R := by
    change (2 * (skip q l.2.val (other l) + l.1.2.val / R) + _) / 2 = _
    split <;> omega
  have hm : mate q p = other l := by
    rw [mate, hpair.1, hp, partner_at q _ _ _ (key hs l).2]
  refine ⟨hpair.1, hpair.2, hm, ?_⟩
  rw [index, hpair.1, hpair.2, hm, hp, Nat.add_sub_cancel_left]
  exact (Nat.add_comm ..).trans (Nat.mod_add_div ..)

private theorem sender_ne (p : Slot R N) : sender p ≠ relay p := by
  unfold sender relay
  split <;> have := p.1.property <;> omega

theorem mod_index (p : Slot R N) : index q p % R = (relay p).val := by
  simp [index, Nat.add_mod, Nat.mod_eq_of_lt (relay p).isLt]

private theorem slot_ext {p t : Slot R N} (ha : sender p = sender t) (hb : relay p = relay t)
    (hm : mate q p = mate q t) (hi : index q p = index q t) : p = t := by
  have hv (z : Slot R N) : skip q (sender z) (mate q z) ≤ z.2.val / 2 :=
    (partner_spec q _ _).1
  have hd := hv p
  have he := hv t
  rw [index, index, ha, hb, hm] at hi
  rw [ha, hm] at hd
  have hhalf := Nat.eq_of_mul_eq_mul_left (sender p).pos (Nat.add_right_cancel hi)
  have hp := p.1.property
  have ht := t.1.property
  unfold sender at ha
  unfold relay at hb
  split_ifs at ha hb <;> exact Prod.ext (Subtype.ext (Prod.ext (by omega) (by omega))) (by omega)

include hs in
private theorem make_leg (a b : Fin R) (k : ℕ)
    (hne : a ≠ b) (hk : k < q a b) (hv : a.val ≠ k % R) :
    ∃ l : Leg q, l.2.val = a ∧ other l = b ∧ l.1.2.val = k := by
  have hh (v : Virtual q) (he : v.2.val = k) : a ≠ via v := by
    intro h
    apply hv
    exact (congrArg Fin.val h).trans (congrArg (· % R) he)
  rcases lt_or_gt_of_ne hne with h | h
  · let v : Virtual q := ⟨⟨(a, b), h⟩, ⟨k, hk⟩⟩
    let l : Leg q := ⟨v, a, .inl rfl, hh v rfl⟩
    exact ⟨l, rfl, by simp [l, v, other], rfl⟩
  · let v : Virtual q := ⟨⟨(b, a), h⟩, ⟨k, hk.trans_eq (hs a b)⟩⟩
    let l : Leg q := ⟨v, a, .inr rfl, hh v rfl⟩
    exact ⟨l, rfl, by simp [l, v, other, hne], rfl⟩

/-- An arithmetic decoder recognizes exactly the occupied slots. -/
theorem active_iff (p : Slot R N) : active q p ↔ p ∈ Set.range (slot hs hq hn) := by
  constructor
  · intro h
    have hv : (sender p).val ≠ index q p % R := by
      rw [mod_index]
      exact fun h => sender_ne p (Fin.ext h)
    obtain ⟨l, ha, hb, hk⟩ := make_leg hs _ _ _ h.1 h.2 hv
    obtain ⟨h₁, h₂, h₃, h₄⟩ := read_slot hs hq hn l
    refine ⟨l, slot_ext (h₁.trans ha) ?_ (h₃.trans hb) (h₄.trans hk)⟩
    rw [h₂]
    exact Fin.ext ((congrArg (· % R) hk).trans (mod_index p))
  · rintro ⟨l, rfl⟩
    obtain ⟨h₁, _, h₃, h₄⟩ := read_slot hs hq hn l
    rw [active, h₁, h₃, h₄]
    exact key hs l

private theorem legs {l k : Leg q} (hl : l.1 = k.1) :
    l = k ∨ other l = k.2.val ∧ other k = l.2.val := by
  rcases l with ⟨v, a, ha, ha'⟩
  rcases k with ⟨w, b, hb, hb'⟩
  change v = w at hl
  subst w
  by_cases he : a = b
  · left; subst b; rfl
  · right
    unfold other
    dsimp only
    grind

private theorem opposite_leg (l : Leg q) (h : other l ≠ via l.1) :
    ∃ k : Leg q, k.1 = l.1 ∧ k.2.val = other l ∧ other k = l.2.val := by
  have he : other l = l.1.1.val.1 ∨ other l = l.1.1.val.2 := by
    unfold other
    split <;> simp
  let k : Leg q := ⟨l.1, other l, he, h⟩
  rcases legs (l := l) (k := k) rfl with hh | hh
  · have hh' : l.2.val = other l := congrArg (fun z : Leg q => z.2.val) hh
    have := l.2.property.1
    have := l.1.1.property
    unfold other at hh'
    grind
  · exact ⟨k, rfl, rfl, hh.2⟩

/-- At a relay the peer leg has the same bit index and reversed endpoints. -/
def peer (q : Fin R → Fin R → ℕ) (p : Slot R N) :=
  wireAddress R N (mate q p).val (index q p) (skip q (mate q p) (sender p))

private theorem peer_leg {l k : Leg q} (hv : l.1 = k.1)
    (ha : other l = k.2.val) (hb : other k = l.2.val) :
    peer q (slot hs hq hn l) = (address (slot hs hq hn k)).val := by
  obtain ⟨h₁, _, h₃, h₄⟩ := read_slot hs hq hn l
  have hi := congrArg (fun b : Virtual q => b.2.val) hv
  rw [peer, h₁, h₃, h₄, ha, ← hb, hi, address_leg]

/-- The tape may be extended arbitrarily outside its valid addresses.
Only an active relay with a second leg reads the peer address. -/
def relayCheck (q : Fin R → Fin R → ℕ) (u : Fin R) (t : ℕ → Bool) (p : Slot R N) : Prop :=
  (¬active q p → u = p.1.val.1 → t (address p).val = false) ∧
  (active q p → relay p = u → mate q p ≠ u → t (address p).val = t (peer q p))

theorem valid_iff_check (u : Fin R) (t : ℕ → Bool) :
    valid hs hq hn u (fun i => t i.val) ↔ ∀ p : Slot R N, sees u p.1 → relayCheck q u t p := by
  constructor
  · intro h p _
    constructor
    · intro he hu
      exact h.2 p (fun hp => he ((active_iff hs hq hn p).mpr hp)) hu
    · intro ha hr hm
      obtain ⟨l, rfl⟩ := (active_iff hs hq hn p).mp ha
      obtain ⟨_, hv, he, _⟩ := read_slot hs hq hn l
      rw [hv] at hr
      rw [he, ← hr] at hm
      obtain ⟨k, hk, h₁, h₂⟩ := opposite_leg l hm
      rw [peer_leg hs hq hn hk.symm h₁.symm h₂]
      exact h.1 l k hk.symm hr
  · intro h
    constructor
    · intro l k hv hu
      rcases legs hv with rfl | ⟨ha, hb⟩
      · rfl
      · let p := slot hs hq hn l
        have hh := (h p ((incident l u).mpr (.inr hu.symm))).2
        have he := read_slot hs hq hn l
        have hm : mate q p ≠ u := by rw [he.2.2.1, ha, ← hu, hv]; exact k.2.property.2
        have ht := hh ((active_iff hs hq hn p).mpr ⟨l, rfl⟩) (he.2.1.trans hu) hm
        rwa [peer_leg hs hq hn hv ha hb] at ht
    · intro p hp hu
      exact (h p (.inl hu)).1 (fun h => hp ((active_iff hs hq hn p).mp h)) hu

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Links
end

section
/-! # Batched binary search on prefix intervals -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed

open Coloring Diagonal.Links
variable {F S : Type} [Field F] {w R : ℕ} {U : Coloring.Format} {inp : S → U.obj}

private def state (inp : S → U.obj) (x : Array S w) (s : S) : (U.pair (Perm w)).obj :=
  (inp s, fun i => Fin.ofNat (2 ^ w) (x s i))

/-- Each step gets the unchanged input and the current vector. Track
actual gate counts to avoid raising the cost exponent at every step. -/
private theorem evolve (z : ℕ → Array S w) {c : ℕ} (init : packed F inp (z 0) c)
    (next : ∀ k < w, packed F (state inp (z k)) (z (k + 1)) c) :
    packed F inp (z w) (c + 2) := by
  let T := 2 ^ w * (100 + w) ^ c
  have hi := init.width
  have run (k : ℕ) (hk : k ≤ w) : ∃ g m, Circuit F U (Perm w) g m ∧
      U.width + (Perm w).width + m ≤ (1 + 7 * k) * T ∧
      ∀ s i, g (inp s) i = Fin.ofNat (2 ^ w) (z k s i) := by
    induction k with
    | zero =>
      obtain ⟨g, ⟨m, hg, hm⟩, he⟩ := init
      exact ⟨g, m, hg, by simpa [T] using hm, he⟩
    | succ k ih =>
      obtain ⟨g, m, hg, hm, he⟩ := ih (by omega)
      obtain ⟨f, ⟨n, hf, hn⟩, he'⟩ := next k (by omega)
      refine ⟨_, _, ((Circuit.id F U).pair hg).comp hf, ?_, ?_⟩
      · rw [show (1 + 7 * (k + 1)) * T = (1 + 7 * k) * T + 7 * T by ring]
        omega
      · intro s i
        change f (inp s, g (inp s)) i = _
        rw [funext (he s)]
        exact he' s i
  obtain ⟨g, m, hg, hm, he⟩ := run w le_rfl
  refine ⟨g, ⟨m, hg, hm.trans ?_⟩, he⟩
  rw [mul_comm (1 + 7 * w), pow_add, ← mul_assoc (2 ^ w)]
  apply Nat.mul_le_mul_left
  nlinarith

private theorem state_width {c : ℕ} (hi : U.width ≤ 2 ^ w * (100 + w) ^ c) :
    (U.pair (Perm w)).width ≤ 2 ^ w * (100 + w) ^ (c + 2) := by
  rw [Coloring.Format.width_pair, Coloring.Format.width_vec, Coloring.Format.width_addr]
  have hp : 1 ≤ (100 + w) ^ c := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ 2 ^ w * ((100 + w) ^ c + w) := by rw [mul_add]; omega
    _ ≤ _ := by
      rw [pow_add]
      apply Nat.mul_le_mul_left
      have he := Nat.mul_le_mul_right w hp
      have hh := Nat.mul_le_mul_left ((100 + w) ^ c) (show 1 + w ≤ (100 + w) ^ 2 by nlinarith)
      rw [mul_add] at hh
      omega

private theorem old {x y : Array S w} {c : ℕ} (hf : packed F inp x c) :
    packed F (state inp y) x (c + 5) := by
  have hp := (Cheap.id F (state_width hf.width)).fst
  obtain ⟨g, hg, he⟩ := hf
  exact ⟨_, (hp.comp hg).mono (by omega), he⟩

private theorem current (x : Array S w) {c : ℕ} (hi : U.width ≤ 2 ^ w * (100 + w) ^ c) :
    packed F (state inp x) x (c + 5) :=
  ⟨_, (Cheap.id F (state_width hi)).snd.mono (by omega), fun _ _ => rfl⟩

variable [NeZero R] {a b : S → B w → Fin R} {q : S → Fin R → Fin R → ℕ} {c : ℕ}

theorem entry (hw : R ^ 2 ≤ 2 ^ w) (hq : packed F inp (matrix w q) c)
    (ha : packed F inp (fun s i => (a s i).val) c)
    (hb : packed F inp (fun s i => (b s i).val) c) :
    packed F inp (fun s i => q s (a s i) (b s i)) (c + 30) := by
  have hf : fits (fun s i => (a s i).val) :=
    fun s i => (a s i).isLt.trans_le ((Nat.le_pow (by decide : 0 < 2)).trans hw)
  have h := (hq.lookup ((ha.unary hf (· * R)).add hb)).mono (n := c + 30) (by omega)
  simpa only [matrix_index hw] using h

private def approx (w p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let y := approx w p k + 2 ^ (w - (k + 1))
    if y ≤ p then y else approx w p k

private theorem approx_le (w p k : ℕ) : approx w p k ≤ p := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => simp only [approx]; split <;> assumption

private theorem approx_eq {w p : ℕ} (hp : p < 2 ^ w) : approx w p w = p := by
  have up (k : ℕ) (hk : k ≤ w) : p < approx w p k + 2 ^ (w - k) := by
    induction k with
    | zero => simpa [approx] using hp
    | succ k ih =>
      have h := ih (by omega)
      rw [show w - k = (w - (k + 1)) + 1 by omega, pow_succ] at h
      simp only [approx]
      split <;> omega
  have := up w le_rfl
  have := approx_le w p w
  simp only [Nat.sub_self, pow_zero] at *
  omega

/-- Find the last prefix offset not exceeding each query. The circuit
tests one candidate per lane per bit of the partner index. -/
theorem search {j : Array S w} (hw : R ^ 2 ≤ 2 ^ w)
    (hskip : packed F inp (matrix w (fun s => skip (q s))) c)
    (ha : packed F inp (fun s i => (a s i).val) c) (hj : packed F inp j c)
    (hb : ∀ s u v, skip (q s) u v < 2 ^ w) (hfit : fits j) :
    packed F inp (fun s i => (partner (q s) (a s i) (j s i)).val) (c + 64) := by
  let p s i := partner (q s) (a s i) (j s i)
  have hR : R ≤ 2 ^ w := (Nat.le_pow (by decide : 0 < 2)).trans hw
  let z (k : ℕ) (s : S) (i : B w) := approx w (p s i).val k
  have hz k s i : z k s i < R := (approx_le ..).trans_lt (p s i).isLt
  have init : packed F inp (z 0) (c + 62) :=
    (const F inp (fun _ => 0) ha.width).mono (by omega)
  have next (k : ℕ) (_ : k < w) : packed F (state inp (z k)) (z (k + 1)) (c + 62) := by
    let f x := if x + 2 ^ (w - (k + 1)) < R then x + 2 ^ (w - (k + 1)) else x
    let b (s : S) (i : B w) : Fin R := ⟨f (z k s i), by
      unfold f
      split
      · assumption
      · exact hz k _ _⟩
    have hcur := current (inp := inp) (F := F) (z k) ha.width
    have hc : packed F (state inp (z k)) (fun s i => (b s i).val) (c + 17) :=
      hcur.unary (fun s i => (hz k s i).trans_le hR) f
    have hcost := entry hw ((old hskip).mono (by omega)) ((old ha).mono (by omega)) hc
    have hnew := (old hj).select hcost hcur hc hfit (fun s i => hb s _ _)
    convert hnew.mono (n := c + 62) (by omega) using 1
    funext s i
    have hi := le_partner (q s) (a s i) (b s i) (j s i)
    change (b s i).val ≤ (p s i).val ↔ _ at hi
    have hp := (p s i).isLt
    change (if z k s i + 2 ^ (w - (k + 1)) ≤ (p s i).val then z k s i + 2 ^ (w - (k + 1))
      else z k s i) = _
    have he : (b s i).val = f (z k s i) := rfl
    unfold f at he
    split_ifs at he ⊢ <;> omega
  have he : z w = (fun s i => (p s i).val) :=
    funext fun s => funext fun i => approx_eq ((p s i).isLt.trans_le hR)
  have h := evolve z init next
  rwa [he] at h

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-! # Reading a link when a worker is itself the intermediate processor -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Links
variable {R N : ℕ} {q : Fin R → Fin R → ℕ}

def endAddress (R N u a b k x y : ℕ) :=
  let left := wireAddress R N a k x
  let right := wireAddress R N b k y
  if u = k % R then (if u = a then right else left) else (if u = a then left else right)

theorem endpoint_address (hs : ∀ u v, q u v = q v u)
    (hq : ∀ u, ∑ v, q u v ≤ N / 64) (hn : 64 * R ^ 2 ≤ N)
    (z : Virtual q) (u : Fin R) (hu : sees u z.1) :
    let a := z.1.val.1
    let b := z.1.val.2
    (address (slot hs hq hn (endpointLeg z u hu))).val =
      endAddress R N u.val a.val b.val z.2.val (skip q a b) (skip q b a) := by
  intro a b
  rw [address_leg]
  have hv (u : Fin R) : u.val = z.2.val % R ↔ u = via z := ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩
  unfold endAddress
  simp only [hv, ← Fin.ext_iff]
  have hne : z.1.val.2 ≠ z.1.val.1 := z.1.property.ne'
  unfold endpointLeg
  by_cases h : u = via z
  · rw [dite_eq_right (not_ne_iff.mpr h), ite_eq_left h]
    rcases hu with rfl | rfl
    · rw [dite_eq_left rfl]; simp [other, a, b, hne]
    · rw [dite_eq_right hne]; simp [other, a, b, hne]
  · rw [dite_eq_left h, ite_eq_right h]
    rcases hu with rfl | rfl
    · simp [other, a, b]
    · simp [other, a, b, hne]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Links

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
open Coloring Diagonal.Links
variable {F S : Type} [Field F] {w : ℕ} {U : Coloring.Format}
  {inp : S → U.obj} {f g u a b k x y : Array S w} {R N c d e t : ℕ}

theorem choose_eq (hf : packed F inp f c) (hg : packed F inp g d)
    (hx : packed F inp x e) (hy : packed F inp y t) (hf' : fits f) (hg' : fits g) :
    packed F inp (fun s i => if f s i = g s i then x s i else y s i)
      (max (max c d) (max e t) + 24) := by
  have h := hf.select hg hy (hg.select hf hy hx hg' hf') hf' hg'
  convert h.mono (n := max (max c d) (max e t) + 24) (by omega) using 1
  funext s i
  split_ifs <;> omega

theorem end_address (hR : 0 < R) (hR' : 2 * R ≤ 2 ^ w)
    (hu : packed F inp u c) (ha : packed F inp a c) (hb : packed F inp b c)
    (hk : packed F inp k c) (hx : packed F inp x c) (hy : packed F inp y c)
    (hu' : fits u) (ha' : ∀ s i, a s i < R) (hb' : ∀ s i, b s i < R)
    (hk' : fits k) (hx' : fits x) (hy' : fits y) :
    packed F inp (fun s i => endAddress R N (u s i) (a s i) (b s i) (k s i) (x s i) (y s i))
      (c + 128) := by
  have ha'' : fits a := by intro s i; have := ha' s i; omega
  have hm := hk.unary hk' (· % R)
  have hm' : fits (fun s i => k s i % R) := by
    intro s i
    exact (Nat.mod_lt _ hR).trans_le (by omega)
  have hl := wire_address (N := N) hR hR' ha hk hx ha' hk' hx'
  have hr := wire_address (N := N) hR hR' hb hk hy hb' hk' hy'
  exact (hu.choose_eq hm (hu.choose_eq ha hr hl hu' ha'') (hu.choose_eq ha hl hr hu' ha'')
    hu' hm').mono (by omega)

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

section
/-! # Simultaneous decoding of occupied positions on physical links -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Links

variable {R N : ℕ} {q : Fin R → Fin R → ℕ}

theorem skip_lt_of_load (hq : ∀ u, ∑ v, q u v ≤ N / 64) (hn : 64 * R ^ 2 ≤ N) (u v : Fin R) :
    skip q u v < N := by
  calc
    _ ≤ ∑ z, (q u z / R + 1) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ ∑ z, (q u z + 1) := Finset.sum_le_sum (fun z _ => Nat.add_le_add_right (Nat.div_le_self ..) 1)
    _ ≤ N / 64 + R := by simp [Finset.sum_add_distrib, hq]
    _ < N := by have := u.pos; have := Nat.le_pow (a := R) (by decide : 0 < 2); omega

theorem index_lt_of_size (p : Slot R N) : index q p < N := by
  have h := (Nat.mul_le_mul_left R p.2.isLt).trans (show R * (N / (4 * R)) ≤ N / 4 by
    rw [← Nat.div_div_eq_div_mul]
    exact Nat.mul_div_le _ _)
  have h' := Nat.mul_le_mul_left R
    (show p.2.val / 2 - skip q (sender p) (mate q p) ≤ p.2.val by omega)
  rw [Nat.mul_succ] at h
  unfold index
  omega

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Links

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed

open Coloring Diagonal.Links
variable {F S : Type} [Field F] {w R N c : ℕ} {U : Coloring.Format} {inp : S → U.obj}

/-- Subtract ordered operands by modular addition. -/
theorem sub {f g : Array S w} {m n : ℕ}
    (hf : packed F inp f m) (hg : packed F inp g n) (hfit : fits g)
    (hle : ∀ s i, g s i ≤ f s i) :
    packed F inp (fun s i => f s i - g s i) (max m n + 20) := by
  obtain ⟨a, ha, he⟩ := hf.add (hg.unary hfit (fun k => 2 ^ w - k))
  refine ⟨a, ha.mono (by omega), fun s i => ?_⟩
  rw [he]
  apply Fin.ext
  change (f s i + (2 ^ w - g s i)) % 2 ^ w = (f s i - g s i) % 2 ^ w
  have := hle s i
  have := hfit s i
  rw [show f s i + (2 ^ w - g s i) = f s i - g s i + 2 ^ w by omega, Nat.add_mod_right]

variable [NeZero R] {q : S → Fin R → Fin R → ℕ} {p : S → B w → Slot R N}

/-- Compute the partner, index, length and peer address for each lane.
A peer address is used only when the partner leg exists. -/
theorem decode_slot (hn : 64 * R ^ 2 ≤ N) (hw : N ≤ 2 ^ w)
    (hq : ∀ s u, ∑ v, q s u v ≤ N / 64)
    (hcount : packed F inp (matrix w q) c)
    (hskip : packed F inp (matrix w (fun s => skip (q s))) c)
    (ha : packed F inp (fun s i => (sender (p s i)).val) c)
    (hb : packed F inp (fun s i => (relay (p s i)).val) c)
    (hj : packed F inp (fun s i => (p s i).2.val / 2) c) :
    packed F inp (fun s i => (mate (q s) (p s i)).val) (c + 200) ∧
    packed F inp (fun s i => Diagonal.Links.index (q s) (p s i)) (c + 200) ∧
    packed F inp (fun s i => q s (sender (p s i)) (mate (q s) (p s i))) (c + 200) ∧
    packed F inp (fun s i => peer (q s) (p s i)) (c + 200) := by
  have hr : R ^ 2 ≤ 2 ^ w := by omega
  have hr' : 2 * R ≤ 2 ^ w := by have he : R ≤ R ^ 2 := Nat.le_pow (by decide); omega
  have hfit (s) (u v : Fin R) : skip (q s) u v < 2 ^ w := (skip_lt_of_load (hq s) hn u v).trans_le hw
  have hj' : fits (fun s i => (p s i).2.val / 2) := by
    intro s i
    have := (p s i).2.isLt
    have := Nat.div_le_self N (4 * R)
    dsimp
    omega
  let b s i := mate (q s) (p s i)
  let a s i := sender (p s i)
  have hm : packed F inp (fun s i => (b s i).val) (c + 64) := search hr hskip ha hj hfit hj'
  have askip := hskip.mono (n := c + 64) (by omega)
  have asrc := ha.mono (n := c + 64) (by omega)
  have hl := entry hr askip asrc hm
  have hrgt := entry hr askip hm asrc
  have hc := entry hr (hcount.mono (by omega)) asrc hm
  have hk := hj.sub hl (fun s i => hfit s _ _) (fun s i => (partner_spec _ _ _).1)
  have hk' : fits (fun s i => (p s i).2.val / 2 - skip (q s) (a s i) (b s i)) :=
    fun s i => (Nat.sub_le ..).trans_lt (hj' s i)
  have hidx : packed F inp (fun s i => Diagonal.Links.index (q s) (p s i)) (c + 136) :=
    ((hk.unary hk' (R * ·)).add hb).mono (by omega)
  exact ⟨hm.mono (by omega), hidx.mono (by omega), hc.mono (by omega),
    wire_address (NeZero.pos R) hr' (hm.mono (by omega)) hidx (hrgt.mono (by omega))
      (fun s i => (b s i).isLt) (fun s i => (index_lt_of_size _).trans_le hw) (fun s i => hfit s _ _)⟩

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

/-! # Enumerating the incident links of one processor in parallel -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed

open Coloring Diagonal.Links

variable {F S : Type} [Field F] {w R N c : ℕ} {U : Coloring.Format} {inp : S → U.obj}

/-- Repeated lanes are harmless in a conjunction. Assign the diagonal
of the processor-pair matrix to any existing link at the processor. -/
private def fan (hr : 2 ≤ R) (u v : Fin R) : Link R :=
  if h : u < v then ⟨(u, v), h⟩ else if h : v < u then ⟨(v, u), h⟩
  else if h : u.val = 0 then ⟨(u, ⟨1, by omega⟩), by change u.val < 1; omega⟩
  else ⟨(⟨0, by omega⟩, u), by change 0 < u.val; omega⟩

private theorem fan_sees (hr : 2 ≤ R) (u v : Fin R) : sees u (fan hr u v) := by
  unfold fan
  split_ifs <;> simp [sees]

private theorem fan_covers (hr : 2 ≤ R) (u : Fin R) (p : Link R) (hu : sees u p) :
    ∃ v, fan hr u v = p := by
  rcases hu with rfl|rfl
  · exact ⟨p.val.2, by simp [fan, p.property]⟩
  · exact ⟨p.val.1, by simp [fan, p.property, p.property.not_gt]⟩

private theorem exists_lanes (hr : 2 ≤ R) (hn : 64 * R ^ 2 ≤ N) (hw : N ≤ 2 ^ w) :
    ∃ f : B w → Fin R × Fin (N / (4 * R)), Function.Surjective f := by
  have hc : R * (N / (4 * R)) ≤ 2 ^ w := by
    rw [← Nat.div_div_eq_div_mul]
    exact (Nat.mul_div_le ..).trans ((Nat.div_le_self ..).trans hw)
  have h : 0 < N / (4 * R) := Nat.div_pos (by nlinarith) (by omega)
  let _ : NeZero (R * (N / (4 * R))) := ⟨by positivity⟩
  refine ⟨fun i => finProdFinEquiv.symm (Fin.ofNat _ i.val), fun p => ?_⟩
  refine ⟨Fin.castLE hc (finProdFinEquiv p), ?_⟩
  apply finProdFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext (Nat.mod_eq_of_lt (finProdFinEquiv p).isLt)

/-- The fixed lane index specifies a peer and a byte. A small matrix
indexed by the worker and peer supplies link-specific metadata. -/
theorem relay_lanes [NeZero R] {u : S → Fin R} (hr : 2 ≤ R)
    (hn : 64 * R ^ 2 ≤ N) (hw : N ≤ 2 ^ w) (hu : packed F inp (fun s (_ : B w) => (u s).val) c) :
    ∃ p : S → B w → Slot R N,
      (∀ s i, sees (u s) (p s i).1) ∧ (∀ s t, sees (u s) t.1 → ∃ i, p s i = t) ∧
      packed F inp (fun s i => (sender (p s i)).val) (c + 64) ∧
      packed F inp (fun s i => (relay (p s i)).val) (c + 64) ∧
      packed F inp (fun s i => (p s i).2.val / 2) (c + 64) ∧
      packed F inp (fun s i => (p s i).1.val.1.val) (c + 64) ∧
      packed F inp (fun s i => (address (p s i)).val) (c + 64) := by
  obtain ⟨f, hf⟩ := exists_lanes hr hn hw
  let p (s : S) (i : B w) : Slot R N := (fan hr (u s) (f i).1, (f i).2)
  have hmeta (g : Link R → ℕ) : packed F inp (fun s i => g (p s i).1) (c + 32) := by
    have hg : packed F inp (matrix w (fun _ a b => g (fan hr a b))) (c + 2) :=
      const F inp (fun j => g (fan hr (atPair R j).1 (atPair R j).2)) hu.width
    exact entry (by omega) hg (hu.mono (by omega)) (const F inp (fun j => (f j).1.val) hu.width)
  have lo := hmeta (fun p => p.val.1.val)
  have hi := hmeta (fun p => p.val.2.val)
  have bit := const F inp (fun i => (f i).2.val % 2) hu.width
  have zero := const F inp (fun _ => 0) hu.width
  have hbit : fits (fun (_ : S) i => (f i).2.val % 2) := by
    intro s i
    have := Nat.le_pow (a := R) (by decide : 0 < 2)
    dsimp; omega
  have hz : fits (fun (_ : S) (_ : B w) => 0) := fun _ _ => Nat.two_pow_pos w
  refine ⟨p, fun s i => fan_sees hr _ _, ?_, ?_, ?_,
    (const F inp (fun i => (f i).2.val / 2) hu.width).mono (by omega), lo.mono (by omega), ?_⟩
  · intro s t ht
    obtain ⟨v, hv⟩ := fan_covers hr _ _ ht
    obtain ⟨i, he⟩ := hf (v, t.2)
    exact ⟨i, by simp [p, he, hv]⟩
  · convert (bit.choose_eq zero lo hi hbit hz).mono (n := c + 64) (by omega) using 1
    funext s i
    unfold sender p
    split <;> rfl
  · convert (bit.choose_eq zero hi lo hbit hz).mono (n := c + 64) (by omega) using 1
    funext s i
    unfold relay p
    split <;> rfl
  · have hp := hmeta (fun p => N / (4 * R) * (p.val.1 + p.val.2).val)
    exact ((const F inp (fun i => (f i).2.val) hu.width).add hp).mono (by omega)

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector.packed
end

/-! # Reading the incident bits of numbered channels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Diagonal
variable {R N : ℕ}

def routeAddress (N : ℕ) (q : Fin R → Fin R → ℕ) (u a b : Fin R) (k : ℕ) :=
  Links.endAddress R N u.val a.val b.val k (Links.skip q a b) (Links.skip q b a)

private theorem symmetric (q : Fin R → Fin R → ℕ) (u a b : Fin R) (k : ℕ)
    (hne : a ≠ b) (hu : a = u ∨ b = u) :
    routeAddress N q u a b k = routeAddress N q u b a k := by
  unfold routeAddress Links.endAddress
  have hab : a.val ≠ b.val := fun h => hne (Fin.ext h)
  rcases hu with rfl | rfl
  · simp only [hab, ite_false, ite_true]
  · simp only [hab.symm, ite_false, ite_true]

namespace Channels

variable {E J : Type} {src dst : E → Fin R} [Fintype E] [Fintype J] [LinearOrder J]
  (c : Channels src dst J)

omit [Fintype E] [Fintype J] [LinearOrder J] in
theorem widthAt_symm (u v : Fin R) : c.widthAt u v = c.widthAt v u := by
  funext j
  simp only [widthAt, or_comm]

def address (e : E) :=
  start (c.widthAt (src e) (dst e)) (c.label e).1 + (c.label e).2.val

theorem token_address (e : E) (he : src e ≠ dst e) :
    (Links.token src dst c.serial e he).2.val = c.address e := by
  unfold Links.token address
  by_cases h : src e < dst e
  · rw [dite_eq_left h]
    exact c.serial_value _
  · rw [dite_eq_right h, widthAt_symm c (src e) (dst e)]
    exact c.serial_value _

theorem location_eq (hq : ∀ u, ∑ v, Links.count src dst u v ≤ N / 64)
    (hn : 64 * R ^ 2 ≤ N) (u : Fin R) (e : E) (he : src e ≠ dst e) (hu : src e = u ∨ dst e = u) :
    (Links.location src dst c.serial hq hn u e he hu).val =
      routeAddress N (Links.count src dst) u (src e) (dst e) (c.address e) := by
  unfold Links.location
  rw [Links.endpoint_address, token_address]
  unfold Links.token
  split
  · rfl
  · exact (symmetric _ u _ _ _ he hu).symm

end Channels

namespace Vector.packed

open Coloring
variable {F S : Type} [Field F] {w c : ℕ} {U : Coloring.Format} [NeZero R]
  {inp : S → U.obj} {q : S → Fin R → Fin R → ℕ} {u a b : S → B w → Fin R}
  {k x : Array S w}

theorem read_channel (hr : 2 ≤ R) (hw : R ^ 2 ≤ 2 ^ w)
    (hs : packed F inp (matrix w (fun s => Links.skip (q s))) c)
    (hu : packed F inp (fun s i => (u s i).val) c)
    (ha : packed F inp (fun s i => (a s i).val) c)
    (hb : packed F inp (fun s i => (b s i).val) c)
    (hk : packed F inp k c) (hx : packed F inp x c)
    (hf : ∀ s u v, Links.skip (q s) u v < 2 ^ w) (hfit : fits k) :
    packed F inp (fun s i => x s (Fin.ofNat (2 ^ w)
      (routeAddress N (q s) (u s i) (a s i) (b s i) (k s i)))) (c + 168) := by
  have hle : 2 * R ≤ 2 ^ w := (by nlinarith : 2 * R ≤ R ^ 2) |>.trans hw
  have hu' : fits (fun s i => (u s i).val) := fun s i => (u s i).isLt.trans_le (by omega)
  have hm : c ≤ c + 30 := by omega
  have ht := end_address (N := N) (NeZero.pos R) hle (hu.mono hm) (ha.mono hm) (hb.mono hm)
    (hk.mono hm) (entry hw hs ha hb) (entry hw hs hb ha)
    hu' (fun _ _ => Fin.isLt _) (fun _ _ => Fin.isLt _) hfit (fun _ _ => hf _ _ _) (fun _ _ => hf _ _ _)
  exact (hx.lookup ht).mono (by omega)

end Vector.packed
end OAI.LinearAlgebra.MatrixExponent.Processor
end

section
/-! # Prefix offsets in the physical relay schedule -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Vector

open Install Diagonal.Links
variable {F S I : Type} [Field F] [Fintype I] {R w c : ℕ} [NeZero R]
  {inp : S → I → Bool} {q : S → Fin R → Fin R → ℕ}

private theorem size_bound (hw : R ^ 5 ≤ 2 ^ w) (hi : Fintype.card I ≤ 2 ^ w * (100 + w) ^ c) :
    Fintype.card I + 4 * 2 ^ w * w + Fintype.card (Pair R) * w +
      (2 ^ w * (100 + w) ^ (c + 12) + 3 * Fintype.card (Pair R) * w + 100000 * R ^ 5 * (w + 1)) ≤
        2 ^ w * (100 + w) ^ (c + 13) := by
  have hp : Fintype.card (Pair R) ≤ 2 ^ w := by
    simp only [Fintype.card_prod, Fintype.card_fin, ← pow_two]
    exact (Nat.pow_le_pow_right (NeZero.pos R) (by decide : 2 ≤ 5)).trans hw
  have he (j : ℕ) (hj : j ≤ c + 12) : (100 + w) ^ j ≤ (100 + w) ^ (c + 12) :=
    Nat.pow_le_pow_right (by omega) hj
  have h₁ := he c (by omega)
  have h₂ : 100008 * (w + 1) ≤ (100 + w) ^ (c + 12) :=
    le_trans (by ring_nf; omega) (he 4 (by omega))
  calc
    _ ≤ 2 ^ w * (100 + w) ^ c + 4 * 2 ^ w * w + 2 ^ w * w +
      (2 ^ w * (100 + w) ^ (c + 12) + 3 * 2 ^ w * w + 100000 * 2 ^ w * (w + 1)) := by gcongr
    _ ≤ 2 ^ w * ((100 + w) ^ c + (100 + w) ^ (c + 12) + 100008 * (w + 1)) := by ring_nf; omega
    _ ≤ 2 ^ w * ((100 + w) ^ (c + 12) * 3) := by
      have H (a b c : ℕ) (ha : a ≤ b) (hc : c ≤ b) : a + b + c ≤ b * 3 := by omega
      exact Nat.mul_le_mul_left _ (H _ _ _ h₁ h₂)
    _ ≤ _ := by rw [show c + 13 = (c + 12) + 1 by omega, pow_succ (100 + w) (c + 12)]; gcongr; omega

theorem packed.skip (h : packed (U := raw I) F inp (matrix w q) c)
    (hsize : R ^ 5 ≤ 2 ^ w) (hbound : ∀ s u v, q s u v + 1 < 2 ^ w) :
    packed (U := raw I) F inp (matrix w (fun s => Diagonal.Links.skip (q s))) (c + 13) := by
  have ht : R ^ 2 ≤ 2 ^ w := (Nat.pow_le_pow_right (NeZero.pos R) (by decide : 2 ≤ 5)).trans hsize
  have hx : fits (matrix w q) := fun s _ => (Nat.lt_succ_self _).trans (hbound s _ _)
  have hu := h.unary hx (fun k => k / R + 1)
  obtain ⟨g, hg, he⟩ := hu.unpack (index (R := R) w)
  have ho (s : S) (p : Pair R) (k) : g (inp s) (p, k) = digits w (q s p.1 p.2 / R + 1) k := by
    simpa only [matrix, pair_index ht, raw, Equiv.refl_apply] using he s p k
  have hv := hg.comp (prefixWords_net (F := F) (R := R) (w := w))
  apply packed.reshape _ (atPair R) hv (size_bound hsize h.width)
  intro s j b
  change digits w (prefixWords (g (inp s)) (atPair R j)) b = _
  rw [prefixWords_eq _ _ _ (ho s) (fun p => by
    exact lt_of_le_of_lt (Nat.add_le_add_right (Nat.div_le_self _ _) 1) (hbound s p.1 p.2))]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Vector
end
