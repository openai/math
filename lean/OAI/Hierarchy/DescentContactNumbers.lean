import OAI.Hierarchy.DescentBaseReservations
import OAI.Hierarchy.DescentColonies
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Candidate contacts for the exceptional routes through two endpoint trees -/

namespace Hierarchy.DescentContacts
open DescentBaseProfile DescentColonies
open scoped BigOperators Classical
noncomputable section

/-- All possible ancestor and descendant IDs at one neighboring position,
before deciding which dyadic leaves are actually used by a summand. -/
def possible (d id up down : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (up+1)).image (fun s => (d-s,id/2^(d-(d-s)))) ∪
  (Finset.range (down+1)).biUnion (fun s =>
    (touching d (d+s) id).image (fun j => (d+s,j)))

private theorem geometric (D : ℕ) : (∑s∈Finset.range (D+1),2^s)+1=2^(D+1) := by
  induction D with
  | zero => decide
  | succ d ih =>
    rw [Finset.sum_range_succ,pow_succ (2:ℕ) (d+1)]
    omega

theorem possible_card (d id up down : ℕ) : (possible d id up down).card≤up+1+2*2^down := by
  apply (Finset.card_union_le ..).trans
  apply Nat.add_le_add
  · exact Finset.card_image_le.trans (Finset.card_range _).le
  · apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑s∈Finset.range (down+1),2^s := Finset.sum_le_sum fun s _ =>
        Finset.card_image_le.trans (by simp [touching_card])
      _ ≤ _ := by have := geometric down; rw [pow_succ] at this; omega

theorem possible_of_touch {d e id j up down : ℕ} (upper : d≤e+up) (lower : e≤d+down)
    (touch : j∈touching d e id) : (e,j)∈possible d id up down := by
  by_cases deep : d≤e
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    have eq : d+(e-d)=e := by omega
    refine ⟨e-d,Finset.mem_range.mpr (by omega),?_⟩
    simpa only [eq] using Finset.mem_image_of_mem (fun t => (e,t)) touch
  · apply Finset.mem_union_left
    have eq : d-(d-e)=e := by omega
    have old : j=id/2^(d-e) := by simpa [touching,deep] using touch
    exact Finset.mem_image.mpr ⟨d-e,Finset.mem_range.mpr (by omega),by rw [eq,old]⟩

theorem possible_meeting {k d e up down : ℕ} (dK : d≤k) (eK : e≤k)
    (upper : d≤e+up) (lower : e≤d+down) (x : Block k) :
    (e,group e x)∈possible d (group d x) up down :=
  possible_of_touch upper lower (actual_touch dK eK x)

/-- When the merged-hub length is at least F and a nonhub leaf has
length at most P*F, the possible merged hub IDs at that neighboring
position number at most P. -/
theorem touched_hubs {k d f g D : ℕ} (fg : f≤g) (dk : d≤k)
    (leaf : width k d≤2^D*2^f) (id : ℕ) :
    (touching d (k-g) id).card≤2^D := by
  have exp : k-d≤D+f := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    (by simpa only [width,pow_add] using leaf)
  rw [touching_card]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The same constraint viewed from the merged hub, now taking account
of every dyadic nonhub length from F to P*F. -/
theorem hub_meeting {k e f g D : ℕ} (fg : f≤g) (gk : g≤k) (ek : e≤k)
    (small : 2^f≤width k e) (large : width k e≤2^D*2^f) (x : Block k) :
    (e,group e x)∈possible (k-g) (group (k-g) x) D (g-f) := by
  have atLeast : f≤k-e := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp small
  have atMost : k-e≤D+f := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    (by simpa only [width,pow_add] using large)
  exact possible_meeting (Nat.sub_le ..) ek (by omega) (by omega) x

variable {V : Type*} [DecidableEq V]
abbrev Endpoint (Y : ℕ) := (ℕ × ℕ) × Option (Fin Y)

def terminals (Y : ℕ) (keys : Finset (ℕ × ℕ)) : Finset (Endpoint Y) :=
  (keys ×ˢ (Finset.univ : Finset (Fin Y))).image (fun p => (p.1,some p.2))

theorem terminal_count (Y : ℕ) (keys : Finset (ℕ × ℕ)) :
    (terminals Y keys).card≤keys.card*Y := Finset.card_image_le.trans (by simp)

theorem terminal_mem {Y : ℕ} {keys : Finset (ℕ×ℕ)} {p : ℕ×ℕ} (member : p∈keys) (j : Fin Y) :
    (p,some j)∈terminals Y keys := Finset.mem_image.mpr ⟨(p,j),Finset.mem_product.mpr
      ⟨member,Finset.mem_univ j⟩,rfl⟩

/-- For a nonhub input terminal, its neighbor either has Y input terminals
per possible dyadic leaf or is a merged hub with one stem per hub interval. -/
def fromNonhub (Y d id D h : ℕ) (hub : Bool) : Finset (Endpoint Y) :=
  if hub then if h≤d+D then (touching d h id).image (fun j => ((h,j),none)) else ∅
  else terminals Y (possible d id D D)

theorem fromNonhub_card (Y d id D h : ℕ) (hub : Bool) :
    (fromNonhub Y d id D h hub).card≤(D+1+2*2^D)*Y+2^D := by
  cases hub with
  | false => exact (terminal_count Y _).trans ((Nat.mul_le_mul_right Y (possible_card ..)).trans (Nat.le_add_right _ _))
  | true =>
    simp only [fromNonhub,ite_true]
    split
    next hwin =>
      apply Finset.card_image_le.trans
      rw [touching_card]
      exact (Nat.pow_le_pow_right (by decide) (by omega : h-d≤D)).trans (Nat.le_add_left _ _)
    next => simp

theorem nonhub_nonhub_mem {Y k d e D h : ℕ} (dk : d≤k) (ek : e≤k) (up : d≤e+D)
    (down : e≤d+D) (x : Block k) (j : Fin Y) :
    ((e,group e x),some j)∈fromNonhub Y d (group d x) D h false :=
  terminal_mem (possible_meeting dk ek up down x) j

theorem nonhub_hub_mem {Y k d f g D : ℕ} (fg : f≤g) (dk : d≤k)
    (large : width k d≤2^D*2^f) (x : Block k) :
    ((k-g,group (k-g) x),none)∈fromNonhub Y d (group d x) D (k-g) true := by
  have exp : k-d≤D+f := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    (by simpa only [width,pow_add] using large)
  simp only [fromNonhub,ite_true,ite_eq_left (show k-g≤d+D by omega)]
  exact Finset.mem_image.mpr ⟨_,actual_touch dk (Nat.sub_le ..) x,rfl⟩

/-- Distinct neighboring sites have disjoint prefixes; each names its
own dyadic interval and actual optional input-terminal ordinal. -/
def names (near : Finset V) {Y : ℕ} (f : V → Finset (Endpoint Y)) :
    Finset (V × Endpoint Y) :=
  near.biUnion (fun w => (f w).image (fun p => (w,p)))

theorem names_mem (near : Finset V) {Y : ℕ} (f : V → Finset (Endpoint Y))
    {w : V} (nw : w∈near) {p : Endpoint Y} (hp : p∈f w) : (w,p)∈names near f :=
  Finset.mem_biUnion.mpr ⟨w,nw,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩

theorem names_card (near : Finset V) {Y Δ c : ℕ} (degree : near.card≤Δ) (f : V → Finset (Endpoint Y))
    (bound : ∀w∈near,(f w).card≤c) : (names near f).card≤Δ*c := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑_w∈near,c := Finset.sum_le_sum fun w hw => Finset.card_image_le.trans (bound w hw)
    _ ≤ _ := by simpa using Nat.mul_le_mul_right c degree

theorem nonhub_names (near : Finset V) {Δ : ℕ} (degree : near.card≤Δ)
    (Y d id D h : ℕ) (isHub : V → Bool) :
    (names near (fun w => fromNonhub Y d id D h (isHub w))).card ≤
      Δ*((D+1+2*2^D)*Y+2^D) :=
  names_card _ degree _ (fun _w _ => fromNonhub_card _ _ _ _ _ _)

theorem hub_names (near : Finset V) {Δ : ℕ} (degree : near.card≤Δ)
    (Y k id D f g : ℕ) :
    (names near (fun _ => terminals Y (possible (k-g) id D (g-f)))).card ≤
      Δ*((D+1+2*2^(g-f))*Y) :=
  names_card _ degree _ (fun _ _ => (terminal_count Y _).trans (Nat.mul_le_mul_right Y (possible_card ..)))

/-- Substituting D=32 ceil(log₂(2Δ)) gives an absolute logarithmic upper
bound on an exceptional core relay at a nonhub terminal. Neither the
base scale nor the merged-hub length enters this bound. -/
theorem nonhub_height (near : Finset V) {Δ Y : ℕ} (branch : 0<Δ) (rows : 0<Y)
    (degree : near.card≤Δ) (d id h : ℕ) (isHub : V → Bool) :
    let D := 32*Nat.clog 2 (2*Δ)
    Nat.clog 2 (names near (fun w => fromNonhub Y d id D h (isHub w))).card≤
      36*Nat.clog 2 (2*Δ*Y) := by
  let D := 32*Nat.clog 2 (2*Δ)
  let Q := 2^D
  let L := Nat.clog 2 (2*Δ*Y)
  have two : 1<2 := by decide
  have X : 2*Δ≤2*Δ*Y := Nat.le_mul_of_pos_right _ rows
  have Yle : Y≤2*Δ*Y := Nat.le_mul_of_pos_left _ (by omega)
  have Δle : Δ≤2^L := (show Δ≤2*Δ*Y by omega).trans (Nat.le_pow_clog two _)
  have Ypow : Y≤2^L := Yle.trans (Nat.le_pow_clog two _)
  have layer : D≤32*L := Nat.mul_le_mul_left 32 (Nat.clog_mono_right 2 X)
  have Lpos : 0<L := Nat.clog_pos two (by omega)
  have plus : D+1≤Q := Nat.lt_two_pow_self
  have bound : (D+1+2*Q)*Y+Q≤4*Q*Y := by
    calc _≤(Q+2*Q)*Y+Q*Y := Nat.add_le_add (Nat.mul_le_mul_right Y (by omega)) (Nat.le_mul_of_pos_right _ rows)
         _=_ := by ring
  have total := (nonhub_names near degree Y d id D h isHub).trans (Nat.mul_le_mul_left Δ bound)
  apply (Nat.clog_le_iff_le_pow two).2
  apply total.trans
  calc
    Δ*(4*Q*Y)≤2^L*(4*Q*2^L) := Nat.mul_le_mul Δle (Nat.mul_le_mul_left _ Ypow)
    _ = 2^(L+2+D+L) := by simp only [pow_add,Q];ring
    _ ≤ 2^(36*L) := Nat.pow_le_pow_right (by decide) (by omega)

end
end Hierarchy.DescentContacts

end OAI
