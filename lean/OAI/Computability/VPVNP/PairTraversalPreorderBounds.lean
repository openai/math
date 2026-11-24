import OAI.Computability.VPVNP.PairTraversalArena
import OAI.Computability.VPVNP.PairTraversalNodeBounds
import OAI.Computability.VPVNP.PairTraversalReadFootprint

/-!
# Physical child-list bounds for every selected DFS visit

Each node in the final preorder originates in a row of its own compression
level. Reading that row gives its actual child pointer and length. Both
header reads and the entire child list fit in the allocated descriptor arena.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open BurstRAM LocalHistory NetworkKernel Compression DFS
open scoped Fin.CommRing
open private row_end_le from OAI.Computability.VPVNP.PairTraversalRows
open private addTree from OAI.Computability.VPVNP.PairTraversalHistory

variable {w : ℕ} {A : Type*} [CommRing A] {Label : Type} [Fintype Label]
variable {κ : Label → A} {N Y : Network}

private def rowBounds (m : Memory w) (limit node : ℕ) : Prop :=
  node+2 ≤ limit ∧ (m node).val + (m (node+1)).val ≤ limit

private theorem layer_bounds {m : Memory w} {cap previous base limit : ℕ} {l : Layer}
    (rows : l.Rows w m cap previous base) (capacity : ∀ i, (l.ids i).length ≤ cap)
    (space : endPos cap base l ≤ limit) (i : Fin l.count) :
    rowBounds m limit (address cap base i.val) := by
  let node := address cap base i.val
  obtain ⟨_, _, fit, ptr, len, _⟩ := rows i
  have small := (row_end_le cap base l i).trans space
  change node+2+(childWords w cap previous l i).length < 2^w at fit
  change m node = ((node+2 : ℕ) : Word w) at ptr
  change m (node+1) = ((childWords w cap previous l i).length : Word w) at len
  have maxLen := capacity i
  simp only [childWords,List.length_map] at fit len
  unfold rowBounds
  change node+2 ≤ limit ∧ (m node).val + (m (node+1)).val ≤ limit
  rw [ptr, len, Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : node+2 < 2^w),
    Nat.mod_eq_of_lt (by omega : (l.ids i).length < 2^w)]
  change node+(cap+2) ≤ limit at small
  omega

private theorem chain_bounds (c : TermChain A N Y) (r : ChainParsers κ c)
    (ords : ChainOrders c) (initial : Order N.Site) (cap previous base limit : ℕ)
    (m : Memory w) (trees : N.Site → VertexTree)
    (rows : AllRows w m cap previous base (stepLayers c r ords initial))
    (capacity : ∀ l ∈ stepLayers c r ords initial, ∀ i, (l.ids i).length ≤ cap)
    (space : base + words cap (stepLayers c r ords initial) ≤ limit)
    (old : ∀ v, ∀ x ∈ (trees v).preorder, rowBounds m limit x) :
    ∀ v, ∀ x ∈ (chainTrees c r (chainPointers cap c ords base) trees v).preorder,
      rowBounds m limit x := by
  induction c generalizing previous base with
  | done => exact old
  | more t data tail ih =>
    let l := stepLayer initial ords.1 r.1
    let ls := stepLayers tail r.2 ords.2 ords.1
    change base + words cap (l :: ls) ≤ limit at space
    have next : endPos cap base l + words cap ls ≤ limit := by
      simpa only [endPos,address,words,List.map_cons,List.sum_cons,Nat.mul_add,Nat.add_assoc] using space
    apply ih r.2 ords.2 ords.1 base (endPos cap base l)
      (addTree r.1 (sitePointers cap base ords.1) trees) rows.2
      (fun L h => capacity L (List.mem_cons_of_mem _ h)) next
    intro v x hx
    change x ∈ (sitePointers cap base ords.1 v).1 ::
      (List.ofFn (fun i => (trees ((r.1.order.children v).entries i).val).preorder)).flatten at hx
    rcases List.mem_cons.mp hx with rfl | hk
    · exact layer_bounds rows.1 (capacity l List.mem_cons_self) ((Nat.le_add_right _ _).trans next) (ords.1.entries.symm v)
    · obtain ⟨xs, hi, hm⟩ := List.mem_flatten.mp hk
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hi
      exact old _ _ hm

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (f : B.Entry → A) (hf : B.IsSolution f) {n : ℕ} (T : ℕ)
variable (hT : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices) (base limit : ℕ) (m : Memory w)
local notation "ls" => selectedLayers B f hf T hT X z
local notation "trees" => selectedTrees B f hf T hT X z base

/-- The two scalar reads and every child-word read in each selected
placement tree lie below the given exclusive bound. -/
theorem selected_preorder_row_bounds (rows : AllRows w m B.recordLimit base base (ls))
    (space : base + words B.recordLimit (ls) ≤ limit) :
    ∀ v, ∀ x ∈ (trees v).preorder,
      x+2 ≤ limit ∧ (m x).val + (m (x+1)).val ≤ limit := by
  let E := B.execute f hf T hT X
  let c := E.termChain (B.records f hf T hT X) z
  let r := selectedParsers B f hf T hT X z
  let ords := branchOrders E (B.records f hf T hT X) z
  let initial := siteOrder X
  let leaf := leafLayer initial
  let rest := stepLayers c r ords initial
  have cap := selected_capacity B f hf T hT X z
  change base + words B.recordLimit (leaf :: rest) ≤ limit at space
  have next : endPos B.recordLimit base leaf + words B.recordLimit rest ≤ limit := by
    simpa only [endPos,address,words,List.map_cons,List.sum_cons,Nat.mul_add,Nat.add_assoc] using space
  apply chain_bounds c r ords initial B.recordLimit base (endPos B.recordLimit base leaf) limit m
    (fun u => leafTree (sitePointers B.recordLimit base initial u)) rows.2
    (fun l hl => cap l (List.mem_cons_of_mem _ hl)) next
  intro v x hx
  change x ∈ [(sitePointers B.recordLimit base initial v).1] at hx
  rw [List.mem_singleton] at hx
  exact hx ▸ layer_bounds rows.1 (cap leaf List.mem_cons_self) ((Nat.le_add_right _ _).trans next) (initial.entries.symm v)

/-- Word-encoded visits in the DFS event log recover the same bounds. -/
theorem selected_preorder_word_bounds (rows : AllRows w m B.recordLimit base base (ls))
    (space : base + words B.recordLimit (ls) ≤ limit) (fit : limit ≤ 2^w) :
    ∀ v, ∀ node ∈ (trees v).preorder.map (fun n : ℕ => (n : Word w)),
      node.val+2 ≤ limit ∧ (m node.val).val + (m (node.val+1)).val ≤ limit := by
  intro v node h
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp h
  have bounds := selected_preorder_row_bounds B f hf T hT X z base limit m rows space v n hn
  rwa [Fin.val_natCast,Nat.mod_eq_of_lt (by omega : n < 2^w)]

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
