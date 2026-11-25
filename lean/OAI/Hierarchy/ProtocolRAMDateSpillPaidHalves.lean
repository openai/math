import OAI.Hierarchy.ProtocolRAMDateSpillKeyRead
import OAI.Hierarchy.ProtocolRAMPaidOriginalEndpoints
import OAI.Hierarchy.ProtocolRAMTurnAuthenticatedChart
import OAI.Hierarchy.ProbeFinalRoutes

namespace OAI
/-! # Earlier spill visits are positive rows of the authenticated final paid port table -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.DateSpill
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard HistoryRoles RoleProgram WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAMTurnChart ProtocolRAM.Calendar ReportSockets
open scoped Classical BigOperators Fin.CommRing
variable {h W k n attempts w : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (b : Board) (B : Mount (S:=S) π (name (h:=h) (W:=W) (k:=k)) b.edges)
    (pad : Chord (siteLast h (2^W) k+1)) (o : CoreRoute.Orders h (2^W) k)
local notation "Src" => ProtocolRAMTurnGeometry.Source b.edges h (2^W) k
local notation "inj" => (siteNumber h (2^W) k).injective
local notation "wire" => ProtocolRAMTurnOccurrence.edgeAt B inj pad o
local notation "ends" => ProtocolRAMTurnOccurrence.endsAt B inj pad
local notation "Goods" => Commodity (Fin (2^h)) (Stages h (2^W)) k
local notation "Port" => Public S h W k attempts

/-- Both signed role words fit the same charged local-code aperture. -/
theorem printed_fit (kind : Bool) (ports : Bool→Port) (side : Bool)
    (room : 2*WordSeats.fixedRoom (k:=k) (attempts:=attempts) S≤2^w) :
    ProtocolRAMTurnOperands.printed S kind ports side false<2^w := by
  let z:=ports (if name (HistoryRoles.site S (ports false))<name (HistoryRoles.site S (ports true)) then side else !side)
  have bound : HistoryRoles.code S z<WordSeats.fixedRoom (k:=k) (attempts:=attempts) S:=HistoryRoles.code_bound S z
  change 2*HistoryRoles.code S z+kind.toNat<2^w
  cases kind <;> simp <;> omega

/-- A positive earlier commodity purchase funds every actual occurrence in its
walk, including multiple occurrences of one physical paid edge. -/
theorem good_paid (spill : Goods→ℕ) (total : Fin b.edges→ℕ) (charged : ∀e,routeLoad B.ordinary spill e≤total e)
    (g : Goods) (on : 0< spill g) (ix : Fin (B.ordinary g).length) : 0<total ((B.ordinary g).get ix) := by
  let e:=(B.ordinary g).get ix
  have member : e∈B.ordinary g:=List.get_mem ..
  have positive : 0<(B.ordinary g).count e*spill g:=Nat.mul_pos (List.count_pos_iff.mpr member) on
  have counted : (B.ordinary g).count e*spill g≤routeLoad B.ordinary spill e :=
    Finset.single_le_sum (s:=Finset.univ) (f:=fun c=>(B.ordinary c).count e*spill c)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ g)
  exact positive.trans_le (counted.trans (charged e))

/-- The physical timestamp and hop ordinal decode to a live paid row. -/
theorem visited_paid (names : Fin n≃Src) (dated : Fin n→ℕ) (spill : Goods→ℕ) (total : Fin b.edges→ℕ)
    (active : ∀a,0<dated a→∃g,names a=.inr (.inl g) ∧ 0< spill g)
    (charged : ∀e,routeLoad B.ordinary spill e≤total e) (a : Fin n) (on : 0<dated a)
    (j : ℕ) (hj : j<ProtocolRAMTurnGeometry.length (names a)) :
    ∃e : Fin b.edges,wire (ProtocolRAMTurnGeometry.origin o (names a)+j)=e.val ∧ 0<total e := by
  obtain ⟨g,row,positive⟩:=active a on
  rw [row] at hj ⊢
  let ix : Fin (B.ordinary g).length:=⟨j,by rw [ProtocolRAMTurnGeometry.length_ordinary B g];exact hj⟩
  exact ⟨(B.ordinary g).get ix,ProtocolRAMTurnOccurrence.read B inj pad o (.inr (.inl g)) j ix.isLt,
    good_paid S π b B spill total charged g positive ix⟩

theorem paid_halves (depth : ℕ) (mark : Marks h W k attempts) (unique : Exclusive mark)
    (names : Fin n≃Src) (dated : Fin n→ℕ) (spill : Goods→ℕ)
    (old : Fin b.old→ℕ) (total : Fin b.edges→ℕ)
    (before : ∀i,0<old i→Bool→Port) (after : ∀i,0<total i→Bool→Port)
    (id : {e:Fin b.edges // 0<total e}→Catalogue S π depth mark)
    (aligned : ∀e,filledChord B.actual pad e.val=sorted S π depth mark (.inl (id e)))
    (ports : ∀e on side,after e on side=.inl (HistoryRoles.paid S π depth mark unique (id ⟨e,on⟩,side)))
    (m : Memory w) (read : b.LiveReads S old total before after m)
    (active : ∀a,0<dated a→∃g,names a=.inr (.inl g) ∧ 0< spill g)
    (charged : ∀e,routeLoad B.ordinary spill e≤total e) (a : Fin n) (pos : 0<dated a)
    (j : ℕ) (hj : j<ProtocolRAMTurnGeometry.length (names a)) :
    let e:=wire (ProtocolRAMTurnGeometry.origin o (names a)+j)
    (b.newSite false).read m (e:Word w)=((ends e).1:Word w) ∧
      (b.newSite true).read m (e:Word w)=((ends e).2:Word w) := by
  obtain ⟨e,address,paid⟩:=visited_paid S π b B pad o names dated spill total active charged a pos j hj
  have code:=ProtocolRAMPaidTurnPlacement.paid_printed_ends S π depth mark unique B pad e (id ⟨e,paid⟩)
    (after e paid) (aligned ⟨e,paid⟩) (ports e paid)
  have observations:=ProtocolRAMTurnSnapshot.reported_ends S b read e paid _ _ code.1 code.2
  simpa only [address,ProtocolRAMTurnOccurrence.endsAt,dite_eq_left e.isLt] using observations

end Hierarchy.ProtocolRAM.DateSpill

end
end OAI
