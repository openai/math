import OAI.ThreeFlat.Diagonal.CompressorLocalIncidence
import OAI.ThreeFlat.Diagonal.ShrinkGraph

namespace OAI
/-! # Building sorted incoming and outgoing slot lists by a bounded local scan

Only candidate slots in the immediate bounded child lists are enumerated.
The filter checks the desired endpoint and the finite set removes repeated
discoveries of a motif. Sorting these lists gives the same slot numbering
as the graph on retained demand edges.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Local
open Computability.VPVNP.Compression
open scoped BigOperators Classical
variable {V H Tag L : Type*} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

def roleLayout (layout : Bool) : Role → Bool
  | .a => false
  | .b => true
  | .d => layout

theorem covers_role (layout : Bool) (role : Role) (m : Rooted P) :
    ∃ i, rooted P (roleLayout layout role) (base (siteOf P layout role m.val)) i = some m := by
  cases role with
  | a => exact covers_A_root P m
  | b => exact covers_B_root P m
  | d => exact covers_D_root P layout m

abbrev EdgeIndex (d c : ℕ) (count : Fin 4 → ℕ) := Σ e : Fin 4, Index d c × Fin (count e)

def slotCandidate (layout : Bool) (role : Fin 4 → Role) (count : Fin 4 → ℕ) (b : V × Tag)
    (i : EdgeIndex d c count) : Option (ShrinkEdge P count) :=
  (rooted P (roleLayout layout (role i.1)) b i.2.1).map fun m => ⟨i.1,m,i.2.2⟩

theorem covers_slot (layout : Bool) (role : Fin 4 → Role) (count : Fin 4 → ℕ)
    (e : ShrinkEdge P count) :
    ∃ i, slotCandidate P layout role count (base (slotSite P layout role e)) i = some e := by
  rcases e with ⟨k,m,j⟩
  obtain ⟨i,hi⟩ := covers_role P layout (role k) m
  refine ⟨⟨k,i,j⟩,?_⟩
  simp only [slotCandidate,slotSite,hi,Option.map_some]

variable [Fintype V] [Fintype Tag] [Fintype H] [Fintype L]

/-- Applied with the source and target roles separately. -/
noncomputable def localSlots (layout : Bool) (role : Fin 4 → Role) (count : Fin 4 → ℕ)
    (b : V × Tag) : Finset (ShrinkEdge P count) :=
  (Finset.univ.biUnion fun i : EdgeIndex d c count =>
    (slotCandidate P layout role count b i).toFinset).filter fun e => base (slotSite P layout role e) = b

theorem localSlots_eq (layout : Bool) (role : Fin 4 → Role) (count : Fin 4 → ℕ)
    (b : V × Tag) : localSlots P layout role count b =
      CompressorRegularize.incident (fun e => base (slotSite P layout role e)) b := by
  ext e
  simp only [localSlots,CompressorRegularize.incident,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_biUnion,Option.mem_toFinset]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨i,hi⟩ := covers_slot P layout role count e
    exact ⟨⟨i,by simpa [h] using hi⟩,h⟩

theorem index_cost (count : Fin 4 → ℕ) :
    Fintype.card (EdgeIndex d c count) = (4*d^2*2^c) * ∑ e, count e := by
  simp [EdgeIndex,Fintype.card_sigma,Fintype.card_prod,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ThreeFlat.Diagonal.CompressorPacking.Local

end OAI
