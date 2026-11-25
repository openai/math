import OAI.Hierarchy.DescentContactNumbers

namespace OAI
/-! # A common bounded-degree directory for colonies reached by the motif -/

namespace Hierarchy.DescentHostDirectory
open DescentContacts DescentColonies
open scoped BigOperators Classical
noncomputable section
variable {V : Type*} [DecidableEq V]

abbrev Key (V : Type*) := V × (ℕ × ℕ) × ℕ

/-- The address is independent of traffic, grouping, affine color and summand. -/
def next (near : V → Finset V) (D slots : ℕ) (key : Key V) : Finset (Key V) :=
  (insert key.1 (near key.1)) ×ˢ ((possible key.2.1.1 key.2.1.2 D D) ×ˢ Finset.range slots)

def directory (near : V → Finset V) (D slots : ℕ) : ℕ → Key V → Finset (Key V)
  | 0,key => {key}
  | hops+1,key => (directory near D slots hops key).biUnion (next near D slots)

theorem one_hop {near : V → Finset V} {D slots k : ℕ} {v u : V} {d e m n : ℕ}
    (site : u=v ∨ u∈near v) (dk : d≤k) (ek : e≤k)
    (up : d≤e+D) (down : e≤d+D) (slot : n<slots) (x : Block k) :
    (u,(e,group e x),n)∈next near D slots (v,(d,group d x),m) :=
  Finset.mem_product.mpr ⟨Finset.mem_insert.mpr site,Finset.mem_product.mpr
    ⟨possible_meeting dk ek up down x,Finset.mem_range.mpr slot⟩⟩

/-- Each hop can use a distinct common block. The intermediate position's
leaf address can consequently meet the following hop at a different block. -/
theorem colony_hop {near : V → Finset V} {k D a B slots : ℕ}
    (load : V → Block k → ℕ) (limit : ∀v i,load v i≤B) {v u : V}
    (adj : u∈near v) (rev : v∈near u) (x : Block k) (m n : ℕ) (hn : n<slots) :
    let depthAt := depth load (fun p q => q∈near p) D a B limit
    (u,(depthAt u x,group (depthAt u x) x),n)∈
      next near D slots (v,(depthAt v x,group (depthAt v x) x),m) := by
  dsimp only
  apply one_hop (.inr adj) _ _ _ _ hn x
  · exact (depth_le ..).trans (Nat.sub_le ..)
  · exact (depth_le ..).trans (Nat.sub_le ..)
  · exact neighbor_depth load _ D a B limit adj x
  · exact neighbor_depth load _ D a B limit rev x

theorem pad {near : V → Finset V} {D slots : ℕ} (key : Key V) (room : key.2.2<slots) :
    key∈next near D slots key := by
  obtain ⟨v,⟨d,i⟩,m⟩ := key
  apply Finset.mem_product.mpr ⟨Finset.mem_insert_self ..,Finset.mem_product.mpr ⟨?_,Finset.mem_range.mpr room⟩⟩
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨0,by simp,by simp⟩

theorem extend {near : V → Finset V} {D slots hops : ℕ} {x y z : Key V}
    (reached : y∈directory near D slots hops x) (step : z∈next near D slots y) :
    z∈directory near D slots (hops+1) x := Finset.mem_biUnion.mpr ⟨y,reached,step⟩

theorem allow_extra {near : V → Finset V} {D slots h H : ℕ} {x y : Key V}
    (reached : y∈directory near D slots h x) (space : y.2.2<slots) (atMost : h≤H) :
    y∈directory near D slots H x := by
  induction H, atMost using Nat.le_induction with
  | base => exact reached
  | succ n hn ih => exact extend ih (pad y space)

theorem next_card (near : V → Finset V) (D slots Δ : ℕ) (degree : ∀v,(near v).card≤Δ)
    (key : Key V) : (next near D slots key).card≤(Δ+1)*(D+1+2*2^D)*slots := by
  have old := (Finset.card_insert_le key.1 (near key.1)).trans (Nat.add_le_add_right (degree key.1) 1)
  rw [next,Finset.card_product,Finset.card_product,Finset.card_range,Nat.mul_assoc]
  exact Nat.mul_le_mul old (Nat.mul_le_mul_right _ (possible_card ..))

theorem directory_card (near : V → Finset V) (D slots Δ : ℕ) (degree : ∀v,(near v).card≤Δ)
    (h : ℕ) (key : Key V) :
    (directory near D slots h key).card≤((Δ+1)*(D+1+2*2^D)*slots)^h := by
  induction h with
  | zero => simp [directory]
  | succ n ih =>
    let s := directory near D slots n key
    let cap := (Δ+1)*(D+1+2*2^D)*slots
    calc
      _ ≤ ∑y∈s,(next near D slots y).card := Finset.card_biUnion_le
      _ ≤ ∑_y∈s,cap := Finset.sum_le_sum fun y _ => next_card near D slots Δ degree y
      _ = s.card*cap := by simp
      _ ≤ _ := by rw [pow_succ];exact Nat.mul_le_mul_right cap ih

/-- All dyadic addresses at an old position, including the root and units. -/
def codes : ℕ → Finset (ℕ × ℕ)
  | 0 => {(0,0)}
  | k+1 => codes k ∪ (Finset.range (2^(k+1))).image (fun j => (k+1,j))

theorem mem_codes {k d j : ℕ} (depthOk : d≤k) (idOk : j<2^d) : (d,j)∈codes k := by
  induction k with
  | zero => simp_all [codes]
  | succ k ih =>
    by_cases eq : d=k+1
    · subst d
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr idOk,rfl⟩)
    · exact Finset.mem_union_left _ (ih (by omega))

theorem group_lt {k d : ℕ} (fit : d≤k) (x : Block k) : group d x<2^d := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
  change x.val<2^d*2^(k-d)
  rw [←pow_add,Nat.add_sub_of_le fit]
  exact x.isLt

theorem codes_card (k : ℕ) : (codes k).card+1 ≤ 2^(k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have total := Finset.card_union_le (codes k) ((Finset.range (2^(k+1))).image (fun j => (k+1,j)))
    have add : ((Finset.range (2^(k+1))).image (fun j => (k+1,j))).card≤2^(k+1) :=
      Finset.card_image_le.trans (Finset.card_range _).le
    change (codes k ∪ _).card+1 ≤ _
    rw [pow_succ (2:ℕ) (k+1)]
    omega

def keys [Fintype V] (k slots : ℕ) : Finset (Key V) :=
  Finset.univ ×ˢ (codes k ×ˢ Finset.range slots)

omit [DecidableEq V] in
theorem key_mem [Fintype V] {k d slots o : ℕ} (v : V) (x : Block k) (hd : d≤k) (ho : o<slots) :
    (v,(d,group d x),o)∈keys (V:=V) k slots := Finset.mem_product.mpr
      ⟨Finset.mem_univ _,Finset.mem_product.mpr ⟨mem_codes hd (group_lt hd x),Finset.mem_range.mpr ho⟩⟩

omit [DecidableEq V] in
theorem keys_card [Fintype V] (k slots : ℕ) :
    (keys (V:=V) k slots).card≤ Fintype.card V*2^(k+1)*slots := by
  simp only [keys,Finset.card_product,Finset.card_univ,Finset.card_range,Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by have := codes_card k;omega))

end
end Hierarchy.DescentHostDirectory

end OAI
