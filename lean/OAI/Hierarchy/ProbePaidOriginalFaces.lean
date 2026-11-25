import OAI.Hierarchy.ProbePaidNativeRows
import OAI.Hierarchy.ProtocolRAMCatalogueActiveBill

namespace OAI
/-! # Original row endpoints and the simultaneous placement of all live balls -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.CoreBoard ProbeStage.ReportSockets
open BoughtSockets
open scoped Classical

variable {z W k depth jobs : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^z))}
    {marks : Marks z W k jobs}

abbrev Board.originalOrdinal (b : Board) (dirs : Directory jobs) (order : Fin b.coreRows ≃ Edges S z (2^W) k)
    (size : (dirs.header z (2^W) k S.degree depth).count=b.boughtRows) :
    Catalogue S π depth marks ↪ Fin b.rows := b.ordinal S π depth marks order size

/-- Define an endpoint even at a dormant original row to allow the scatter
bound to range over every allocated reporter address. -/
def Board.physicalEnds (b : Board) (dirs : Directory jobs) (order : Fin b.coreRows ≃ Edges S z (2^W) k)
    (size : (dirs.header z (2^W) k S.degree depth).count=b.boughtRows)
    (e : Fin b.rows) : Site z (2^W) k×Site z (2^W) k :=
  let ord:=b.originalOrdinal (π:=π) (marks:=marks) dirs order size
  let vacant : Site z (2^W) k := (.inl ⟨0,by positivity⟩,none)
  if present : ∃v,ord v=e then actualEnds S π depth marks present.choose else (vacant,vacant)

theorem Board.physicalEnds_at (b : Board) (dirs : Directory jobs) (order : Fin b.coreRows ≃ Edges S z (2^W) k)
    (size : (dirs.header z (2^W) k S.degree depth).count=b.boughtRows) (a : Catalogue S π depth marks) :
    b.physicalEnds (π:=π) (marks:=marks) dirs order size (b.originalOrdinal dirs order size a)=
      actualEnds S π depth marks a := by
  let ord:=b.originalOrdinal (π:=π) (marks:=marks) dirs order size
  have yes : ∃v,ord v=ord a:=⟨a,rfl⟩
  change (if h : ∃v,ord v=ord a then actualEnds S π depth marks h.choose else _)=_
  rw [dite_eq_left yes,ord.injective yes.choose_spec]

/-- A positively debited native face has an original catalogue preimage.
A dormant bought address carries identical dummy end sites, whereas the
two named sockets of this live debit occupy distinct physical sites. -/
theorem Board.original_of_faces {X : Type*} (b : Board) (dirs : Directory jobs)
    (order : Fin b.coreRows ≃ Edges S z (2^W) k)
    (size : (dirs.header z (2^W) k S.degree depth).count=b.boughtRows) (e : Fin b.rows)
    (site : X↪Site z (2^W) k) (p : DistinctPair X)
    (face : Faces site p (b.physicalEnds (π:=π) (marks:=marks) dirs order size e)) :
    ∃ original, b.ordinal S π depth marks order size original=e := by
  by_contra dead
  have diagonal : (b.physicalEnds (π:=π) (marks:=marks) dirs order size e).1=
      (b.physicalEnds (π:=π) (marks:=marks) dirs order size e).2 := by
    simp [Board.physicalEnds,Board.originalOrdinal,dead]
  rcases face with face|face <;> rw [face] at diagonal
  · exact p.apart (site.injective diagonal)
  · exact p.apart (site.injective diagonal.symm)

theorem Board.physicalEnds_core (b : Board) (dirs : Directory jobs) (order : Fin b.coreRows ≃ Edges S z (2^W) k)
    (size : (dirs.header z (2^W) k S.degree depth).count=b.boughtRows) (a : Edges S z (2^W) k) :
    b.physicalEnds (π:=π) (marks:=marks) dirs order size (b.coreIndex (order.symm a))=CoreBoard.ends π a :=
  b.physicalEnds_at dirs order size (.inl a)

theorem Board.physicalEnds_bought (b : Board) (dirs : Directory jobs) (order : Fin b.coreRows ≃ Edges S z (2^W) k)
    (size : (dirs.header z (2^W) k S.degree depth).count=b.boughtRows) (a : Bought S π depth marks) :
    b.physicalEnds (π:=π) (marks:=marks) dirs order size
      (b.boughtIndex (Fin.cast size ((dirs.header z (2^W) k S.degree depth).enum ⟨a.1,BoughtLocation.relative a.2⟩)))=
      actualEnds S π depth marks (.inr a) :=
  b.physicalEnds_at dirs order size (.inr a)

theorem payload_placement (port : Fin (2^z)) (x : ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k) :
    (payloadSitesAll (d:=2^W) π k) (port,x)=Prod.map (payloadPlace π port) id x := rfl

def boughtPlacement (t : Fin jobs) (unique : Exclusive marks) :
    LiveChains S π depth (marks t) × ColumnSite (ChainStrip.Columns depth) k ↪ Site z (2^W) k :=
  (allTreeSites S π depth (marks t) (unique t)).trans (stageSitesIntoPayload k)

theorem bought_placement (t : Fin jobs) (unique : Exclusive marks) (a : LiveChains S π depth (marks t))
    (x : ColumnSite (ChainStrip.Columns depth) k) :
    boughtPlacement t unique (a,x)=Prod.map (retainedCol π (marks t) a) id x := by
  change stageSitesIntoPayload k (allTreeSites S π depth (marks t) (unique t) (a,x))=_
  rw [allTreeSites_single]
  rfl

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
