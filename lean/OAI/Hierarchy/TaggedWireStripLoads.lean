import OAI.Hierarchy.TaggedWireStripNative

namespace OAI
/-! # The exact native widths charged by a signed one-ball operator -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ProbeStage CoreBoard AdaptiveProbe Strip WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical BigOperators
variable {n k K N : ℕ} {A B T : Type} [Fintype A] [Fintype B] [Fintype T]
private abbrev LoadRole (n k : ℕ) (A B : Type) := ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k
variable (extra : A⊕B→DistinctPair (TreeSite n k)) (place : T×TreeSite n k↪Fin K) (u : T)
    (b : Board) (stock : A→Fin N) (new : Fin b.rows→Fin N) (idx : LoadRole n k A B→Fin b.rows)
    (mate : TreeColumn n→Fin k→Fin b.rows)

omit [Fintype A] [Fintype B] [Fintype T] in
/-- The order within the two-hop catalyst path may be reversed. Its true
physical IDs survive unchanged in the multiset used by the paid histogram. -/
theorem option_count (r : LoadRole n k A B) (v : Fin N) :
    (StripPaths.links (horizontal n) extra place u (primaryRow (b:=b) stock new idx) (fun c j=>new (mate c j)) r).count v = (if primaryRow (b:=b) stock new idx r=v then 1 else 0)+
      (match r with | .catalyst c j=>if new (mate c j)=v then 1 else 0 | _=>0) := by
  cases r <;> exact StripPaths.counts (horizontal n) extra place u (primaryRow (b:=b) stock new idx) (fun c j=>new (mate c j)) _ v

omit [Fintype T] in
/-- Each row contribution is split between an original inventory slot or
paid primary, the second paid radius, and the actually reported selector
tree. The sums retain all repeated printed IDs and zero-width rows. -/
theorem stream_load (option : LoadRole n k A B→ℕ) (broadcast : TreeLink n k→ℕ) (v : Fin N) :
    (∑z : LoadRole n k A B⊕TreeLink n k, ((Sum.elim (StripPaths.links (horizontal n) extra place u (primaryRow (b:=b) stock new idx) (fun c j=>new (mate c j))) (fun j=>[new (idx (treeRole n k j))])) z).count v *
      (Sum.elim option broadcast z)) =
      (∑r : LoadRole n k A B,(if primaryRow (b:=b) stock new idx r=v then option r else 0))+
      (∑r : LoadRole n k A B, match r with
        | .catalyst c j=>if new (mate c j)=v then option r else 0
        | _=>0)+
      (∑j : TreeLink n k,if new (idx (treeRole n k j))=v then broadcast j else 0) := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,option_count,List.count_cons,List.count_nil]
  rw [←Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro r _
    cases r <;> simp only [add_mul,ite_mul,one_mul,zero_mul,Nat.add_zero]
  · apply Finset.sum_congr rfl
    intro j _
    by_cases yes:new (idx (treeRole n k j))=v
    · subst v; simp
    · simp [yes,beq_iff_eq]

omit [Fintype A] [Fintype B] in
/-- Distinct virtual stocks and paid physical rows occupy disjoint address
ranges. Thus the out-of-range primary field of an inventory role contributes
no fictitious paid width. -/
theorem paid_primary_count (r : LoadRole n k A B) (v : Fin b.rows) (inject : Function.Injective new)
    (apart : ∀a e,stock a≠new e) :
    (if primaryRow (b:=b) stock new idx r=new v then 1 else 0)=if paidRole r ∧ idx r=v then 1 else 0 := by
  cases r with
  | catalyst c j=>simp [primaryRow,paidRole,inject.eq_iff]
  | radius c j side=>simp [primaryRow,paidRole,inject.eq_iff]
  | cross c axes b d=>simp [primaryRow,paidRole,inject.eq_iff]
  | horizontal f l=>simp [primaryRow,paidRole,inject.eq_iff]
  | extra x=>cases x with
    | inl a=>simp [primaryRow,paidRole,apart]
    | inr c=>simp [primaryRow,paidRole,inject.eq_iff]

omit [Fintype A] [Fintype B] in
theorem inventory_count (r : LoadRole n k A B) (v : A) (inject : Function.Injective stock)
    (apart : ∀a e,stock a≠new e) :
    (if primaryRow (b:=b) stock new idx r=stock v then 1 else 0) =
      match r with
      | .extra (.inl a)=>if a=v then 1 else 0
      | _=>0 := by
  have disj (a e):new e≠stock a:=Ne.symm (apart a e)
  cases r with
  | catalyst c j=>simp [primaryRow,disj]
  | radius c j side=>simp [primaryRow,disj]
  | cross c axes b d=>simp [primaryRow,disj]
  | horizontal f l=>simp [primaryRow,disj]
  | extra x=>cases x with
    | inl a=>simp [primaryRow,inject.eq_iff]
    | inr c=>simp [primaryRow,disj]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
