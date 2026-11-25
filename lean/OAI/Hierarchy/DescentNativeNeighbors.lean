import OAI.Hierarchy.DescentColoredHost

namespace OAI
/-! # Sparse occupied destination bins for the actual old core cables -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentHostDirectory DescentColonies DescentContacts
open scoped BigOperators Classical
noncomputable section
variable {V C : Type} [DecidableEq V] [Fintype C] [DecidableEq C]

def oneNeighbor (near : V→Finset V) (D : ℕ) (col : C ↪ V×(ℕ×ℕ)) (c : C) : Finset C :=
  Finset.univ.filter fun b => col b∈(insert (col c).1 (near (col c).1)) ×ˢ
    possible (col c).2.1 (col c).2.2 D D

omit [DecidableEq C] in
theorem oneNeighbor_self (near : V→Finset V) (D : ℕ) (col : C ↪ V×(ℕ×ℕ)) (c : C) :
    c∈oneNeighbor near D col c := by
  have h := pad (near:=near) (D:=D) (slots:=1) ((col c).1,(col c).2,0) (show 0 < 1 by decide)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
    ⟨(Finset.mem_product.mp h).1,(Finset.mem_product.mp (Finset.mem_product.mp h).2).1⟩⟩

omit [DecidableEq C] in
theorem oneNeighbor_card (near : V→Finset V) (D Δ : ℕ) (col : C ↪ V×(ℕ×ℕ))
    (cap : ∀v,(near v).card≤Δ) (c : C) :
    (oneNeighbor near D col c).card≤(Δ+1)*(D+1+2*2^D) := by
  let dir := (insert (col c).1 (near (col c).1)) ×ˢ possible (col c).2.1 (col c).2.2 D D
  have sub : (oneNeighbor near D col c).map col ⊆ dir := by
    rintro _ h
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp h
    exact (Finset.mem_filter.mp hb).2
  calc
    _ = ((oneNeighbor near D col c).map col).card := (Finset.card_map _).symm
    _ ≤ dir.card := Finset.card_le_card sub
    _ ≤ _ := by
      rw [Finset.card_product]
      exact Nat.mul_le_mul ((Finset.card_insert_le ..).trans (Nat.add_le_add_right (cap _) 1)) (possible_card ..)

variable {n k : ℕ} {P : Type*} {bits : P→ℕ} (N : Network n P bits)
variable (B : ℕ) (near : V→Finset V) (D a : ℕ) (load : V→Block k→ℕ) (small : ∀v x,load v x≤B)
variable (position : N.Site→V) (block : N.Site→Block k)
local notation "Col" => occupied N B near D a load small position block
local notation "home" => colonyOf N B near D a load small position block
local notation "col" => occupiedAddress N B near D a load small position block

theorem actual_neighbor {u v : N.Site} (adj : position v∈near (position u))
    (rev : position u∈near (position v)) (same : block v=block u) :
    home v∈oneNeighbor near D col (home u) := by
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  simp only [occupiedAddress_colonyOf]
  apply Finset.mem_product.mpr ⟨Finset.mem_insert_of_mem adj,?_⟩
  change (depthAt B near D a load small (position v) (block v),
    DescentColonies.group (depthAt B near D a load small (position v) (block v)) (block v))∈_
  rw [same]
  exact possible_meeting ((depth_le ..).trans (Nat.sub_le ..)) ((depth_le ..).trans (Nat.sub_le ..))
    (neighbor_depth load _ D a B small adj _) (neighbor_depth load _ D a B small rev _) _

/-- Each positive traffic bin yields an actual old cable with that source
and occupied dyadic destination, so empty remote bins do not contribute loss. -/
theorem positive_neighbor (core : Finset N.Edge)
    (adj : ∀e∈core,position (N.dst e)∈near (position (N.src e)))
    (rev : ∀e∈core,position (N.src e)∈near (position (N.dst e)))
    (same : ∀e∈core,block (N.src e)=block (N.dst e)) (u : N.Site) (c : Col)
    (positive : 0<nativeTraffic N core home u c) :
    c∈oneNeighbor near D col (home u) := by
  obtain ⟨⟨e,es,et⟩⟩ := Fintype.card_pos_iff.mp positive
  change N.src e.val=u at es
  change home (N.dst e.val)=c at et
  rw [←es,←et]
  exact actual_neighbor N B near D a load small position block (adj e.val e.2) (rev e.val e.2) (same e.val e.2).symm

theorem thick_support (core : Finset N.Edge) (color : N.Site→Bool)
    (adj : ∀e∈core,position (N.dst e)∈near (position (N.src e)))
    (rev : ∀e∈core,position (N.src e)∈near (position (N.dst e)))
    (same : ∀e∈core,block (N.src e)=block (N.dst e)) (c dest : Col)
    (positive : 0<Fintype.card (ThickPool (nativeTraffic N core home) (thickList home color c) dest)) :
    dest∈oneNeighbor near D col c := by
  obtain ⟨⟨j,w⟩⟩ := Fintype.card_pos_iff.mp positive
  have h := (mem_colorSites home color true c _).mp (List.get_mem (thickList home color c) j)
  rw [←h.1]
  exact positive_neighbor N B near D a load small position block core adj rev same _ dest (Nat.zero_lt_of_lt w.isLt)

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
