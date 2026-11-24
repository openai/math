import OAI.Computability.VPVNP.PairTreeFrontier
import OAI.Computability.VPVNP.PairSelectedPacketOrders
import OAI.Computability.VPVNP.PairTraversalDisjoint

/-!
# Descendant address lists of the actual selected descriptor rows

Each new layer uses a fresh interval of row addresses. Assign its placed
children's complete preorders there, while keeping all earlier row values.
This gives one address-indexed function for all leaves and intermediate
rows, valid for every assignment of the private half-wire packets.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open DFS NetworkKernel CompressorRecords LocalHistory NodeArguments Compression TraversalRows
open private ptr_bounds ptr_injective from OAI.Computability.VPVNP.PairTraversalDisjoint
open private addTree from OAI.Computability.VPVNP.PairTraversalHistory

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {f : L → R} {N Y : Network}

/-- Concatenate each selected child's root address and descendants in the local parser's child
order. -/
def childAddresses {t : Term R N} (r : TermParsers f t) (addr : N.Site → ℕ)
    (desc : ℕ → List ℕ) (v : t.output.Site) : List ℕ :=
  (List.ofFn fun i => let u := (r.order.children v).entries i; addr u.val :: desc (addr u.val)).flatten

/-- These are the descendant addresses in precisely the native child
packet list, independently of its guessed half-wire values. -/
theorem children_addresses {t : Term R N} (r : TermParsers f t) (before : Packets N)
    (addr : N.Site → ℕ) (num : ∀ v z, (before v z).node = addr v)
    (desc : ℕ → List ℕ) (v : t.output.Site) (a : Placed t.place N.Half v) :
    (children r before v a).flatMap (subtreeAddresses desc) = childAddresses r addr desc v := by
  simp [children,childAddresses,List.flatMap_def,subtreeAddresses,Function.comp_def,num]

/-- At every selected layer, a parent's descendant list is exactly the concatenation of its
ordered child subtrees. -/
def DescLayers {N Y : Network} (c : TermChain R N Y) (r : ChainParsers f c)
    (ptr : RowPointers c) (addr : N.Site → ℕ) (desc : ℕ → List ℕ) : Prop :=
  match c with
  | .done _ => True
  | .more _ _ tail => (∀ v, desc (ptr.1 v).1 = childAddresses r.1 addr desc v) ∧
      DescLayers tail r.2 ptr.2 (fun v => (ptr.1 v).1) desc

private theorem extendLayers (c : TermChain R N Y) (r : ChainParsers f c)
    (orders : ChainOrders c) (cap base : ℕ) (addr : N.Site → ℕ) (below : ∀ v, addr v < base)
    (old : ℕ → List ℕ) :
    ∃ desc, (∀ k < base, desc k = old k) ∧ DescLayers c r (chainPointers cap c orders base) addr desc := by
  induction c generalizing base old with
  | done => exact ⟨old,fun _ _ => rfl,trivial⟩
  | more t rec tail ih =>
    let o := orders.1
    let row := fun v => (sitePointers cap base o v).1
    let top := address cap base o.length
    let table := Function.extend row (childAddresses r.1 addr old) old
    have hit (v : t.output.Site) : table (row v) = childAddresses r.1 addr old v :=
      (ptr_injective o cap base).extend_apply _ _ v
    have under (k : ℕ) (hk : k < base) : table k = old k :=
      Function.extend_apply' _ _ _ (by rintro ⟨v,rfl⟩; exact hk.not_ge (ptr_bounds o cap base v).1)
    have bounds (v : t.output.Site) : base ≤ row v ∧ row v < top := ptr_bounds o cap base v
    obtain ⟨desc,earlier,tailRows⟩ := ih r.2 orders.2 top row (fun v => (bounds v).2) table
    have low (k : ℕ) (hk : k < base) : desc k = old k := by
      have ht : base ≤ top := Nat.le_add_right _ _
      exact (earlier k (hk.trans_le ht)).trans (under k hk)
    refine ⟨desc,low,⟨?_,tailRows⟩⟩
    intro v
    change desc (row v) = childAddresses r.1 addr desc v
    rw [earlier _ (bounds v).2,hit]
    simp [childAddresses,fun u => low (addr u) (below u)]

theorem descendant_preorder (c : TermChain R N Y) (r : ChainParsers f c) (ptr : RowPointers c)
    (addr : N.Site → ℕ) (desc : ℕ → List ℕ) (trees : N.Site → VertexTree)
    (old : ∀ v, (trees v).preorder = addr v :: desc (addr v)) (rows : DescLayers c r ptr addr desc) :
    ∀ v, ((chainTrees c r ptr trees) v).preorder =
      lastRowAddresses c ptr addr v :: desc (lastRowAddresses c ptr addr v) := by
  induction c with
  | done => exact old
  | more t rec tail ih =>
    apply ih r.2 ptr.2 (fun v => (ptr.1 v).1) (addTree r.1 ptr.1 trees) _ rows.2
    intro v
    change (ptr.1 v).1 :: (List.ofFn fun i => (trees ((r.1.order.children v).entries i).val).preorder).flatten =
      (ptr.1 v).1 :: desc (ptr.1 v).1
    rw [rows.1]
    simp [childAddresses,old]

/-- A single consistent descendant lookup suffices for the frozen selected
execution. It gives empty leaf lists and the full root preorder on all rows. -/
theorem selected_descendants {k : Type*} [Field k] {S : BlockSchedule k}
    (B : S.Templates) (κ : B.Entry → R) (hκ : B.IsSolution κ) {n : ℕ} (T : ℕ)
    (hT : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute κ hκ T hT X).Choices) (base : ℕ) :
    let E := B.execute κ hκ T hT X
    let records := B.records κ hκ T hT X
    let c := E.termChain records z
    let r := selectedParsers B κ hκ T hT X z
    let first := sitePointers B.recordLimit base (siteOrder X)
    let ptr := chainPointers B.recordLimit c (branchOrders E records z)
      (address B.recordLimit base (siteOrder X).length)
    let roots := lastRowAddresses c ptr (fun v => (first v).1)
    ∃ desc, (∀ v, desc (first v).1 = []) ∧ DescLayers c r ptr (fun v => (first v).1) desc ∧
      ∀ v, ((chainTrees c r ptr (fun u => leafTree (first u))) v).preorder = roots v :: desc (roots v) ∧
        (roots v :: desc (roots v)).Nodup := by
  intro E records c r first ptr roots
  obtain ⟨desc,initial,rows⟩ := extendLayers c r (branchOrders E records z) B.recordLimit
    (address B.recordLimit base (siteOrder X).length) (fun v => (first v).1)
    (fun v => (ptr_bounds (siteOrder X) B.recordLimit base v).2) (fun _ => [])
  have leaf (v : X.network.Site) : desc (first v).1 = [] :=
    initial _ (ptr_bounds (siteOrder X) B.recordLimit base v).2
  have eqn := descendant_preorder c r ptr (fun v => (first v).1) desc (fun v => leafTree (first v))
    (fun v => by rw [leaf]; rfl) rows
  refine ⟨desc,leaf,rows,fun v => ⟨eqn v,?_⟩⟩
  rw [← eqn v]
  exact (selected_preorders B κ hκ T hT X z base).1 v

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
