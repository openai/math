import OAI.Hierarchy.TaggedWireInstallShape
import OAI.Hierarchy.ProbeNativeRoleAddress

namespace OAI
/-! # Every consumed physical port belongs to stock or to the original catalyst reserve -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets
open LinearAlgebra.SpectralBooks ChordGraph
open AdaptiveProbe ProtocolRAM RepairHistogram
open Computability.VPVNP.BurstRAM
open scoped Classical BigOperators
variable {S n g w rows : ℕ} {A : Type} [Fintype A]

/-- A port can repeat an address. Only the positive taps need have an owner;
zero padding and omitted positive-demand entries contribute identically zero. -/
theorem charge_partition {I J T : Type} [Fintype I] [Fintype J] [Fintype T]
    (G : PortGraph (Fin S) I) (K : PortGraph (Fin S) J)
    (stock : T→Option I) (cat : T→Option J) (b : T→ℕ) (one : T→Widths S)
    (receipt : ∀r,0<b r→
      (∃i,stock r=some i ∧ cat r=none ∧ one r=pairWidth (G.tail i) (G.head i)) ∨
      (∃a,cat r=some a ∧ stock r=none ∧ one r=pairWidth (K.tail a) (K.head a))) :
    (∑r,b r • one r)=G.chordWidths (OuterBank.resourceBits stock b)+K.chordWidths (OuterBank.resourceBits cat b) := by
  simp only [PortGraph.chordWidths,chordWidth_scaled,OuterBank.resourceBits,Finset.sum_smul]
  conv_rhs =>
    lhs
    rw [Finset.sum_comm]
  conv_rhs =>
    rhs
    rw [Finset.sum_comm]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases pos : 0<b r
  · rcases receipt r pos with ⟨i,hs,hc,hw⟩|⟨j,hc,hs,hw⟩
    · simp [hs,hc,hw,ite_smul]
    · simp [hs,hc,hw,ite_smul]
  · simp [Nat.eq_zero_of_not_pos pos]

/-- A fixed rectangular physical source bank reindexed by candidate and field.
The left side is the signed matrix's input; the right side reads the actual
commodity scatter and the native catalyst-owner tags on those same fields. -/
theorem source_shape (G : PortGraph (Fin S) (Fin g)) (K : PortGraph (Fin S) A)
    (bank : Bank) (p : Columns) (m : Memory w) (ports : Fin rows→ℕ)
    (loc : (Σj,Fin (ports j))≃Fin n) (cat : Fin n→Option A)
    (demand : Fin rows→Widths S) (one : Fin n→Widths S)
    (row : ∀j,demand j=∑v,consumedBits p m (loc ⟨j,v⟩) • one (loc ⟨j,v⟩))
    (typed : ∀i,0<consumedBits p m i→
      (∃u,kind bank p m i=some u ∧ cat i=none ∧ one i=pairWidth (G.tail u) (G.head u)) ∨
      (∃a,cat i=some a ∧ kind (goods:=g) bank p m i=none ∧ one i=pairWidth (K.tail a) (K.head a))) :
    (∑j,demand j)=G.chordWidths (OuterBank.resourceBits (kind bank p m) (consumedBits (n:=n) p m))+
      K.chordWidths (OuterBank.resourceBits cat (consumedBits p m)) := by
  calc
    _ = ∑ i : (Σj,Fin (ports j)),consumedBits p m (loc i) • one (loc i) := by simp only [row,Fintype.sum_sigma]
    _ = ∑ i : Fin n,consumedBits p m i • one i :=
      loc.sum_comp (fun i : Fin n => consumedBits p m i • one i)
    _ = _ := charge_partition G K _ cat (consumedBits p m) one typed

theorem stock_read {ports : Fin rows→ℕ} (loc : (Σj,Fin (ports j))≃Fin n) (amount : Fin rows→Fin g→ℕ)
    (bank : Bank) (p : Columns) (m : Memory w)
    (row : ∀j i,amount j i=∑v,if kind bank p m (loc ⟨j,v⟩)=some i then installedBits p m (loc ⟨j,v⟩) else 0)
    (i : Fin g) : (∑j,amount j i)=OuterBank.resourceBits (kind bank p m) (installedBits (n:=n) p m) i := by
  rw [←resourceBits_reindex loc]
  unfold OuterBank.resourceBits
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  refine (row j i).trans (Finset.sum_congr rfl ?_)
  intro v _
  by_cases selected : kind bank p m (loc ⟨j,v⟩) = some i <;> simp [selected]

end Hierarchy.WireTelescope.ChosenPackets

end
end OAI
