import OAI.Hierarchy.ProtocolRAMTurnWindowFits
import OAI.Hierarchy.ProtocolRAMChronologicalLive

namespace OAI
/-! # Execution of the physically allocated terminal turn program -/
namespace Hierarchy.ProtocolRAMTurnWindow.Layout
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMTurnChart ProtocolRAMTurnItinerary ProtocolRAMPackedRanked
open scoped Fin.CommRing
variable (L : ProtocolRAMTurnWindow.Layout) {W : ℕ}

def program (W header rom : ℕ) (d : Data) (heads : Bank) (b : Banks) :=
  ProtocolRAMChronologicalShelf.program W L.rows L.sites L.seats header (groupBits L.rows) L.zero
    L.src L.srcBits rom L.romBits L.base L.scratch L.sink d heads b

theorem run (header rom : ℕ) (d : Data) (heads : Bank) (b : Banks)
    (u : Fin L.rows → Geometry) (w : Words) (sitesAt : Fin L.rows→ℕ) (m : Memory W)
    («public» : Loaded header (groupBits L.rows) u m)
    (old : ∀ i,0<w.width (u i).item → d.At w m (u i))
    (weights : ∀i,d.oldWidth.read m ((u i).item:Word W)=(w.width (u i).item:Word W))
    (safe : ProtocolRAMTurnCursor.Safe d W L.zero) (site : d.site=L.site)
    (headerBefore : header+6*2^groupBits L.rows≤L.floor)
    (romBefore : rom+4*2^L.romBits≤L.floor)
    (within : ∀i,(u i).raw≤(u i).length) (lenFit : ∀i,(u i).length<2^W)
    (posPrev : ∀i:Fin L.rows,0<(u i).raw→0 < i.val)
    (closed : ∀i:Fin L.rows,0<(u i).raw→0<w.width (u i).item→
      0<w.width (u ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩).item)
    (endpoint : ∀i,0<w.width (u i).item →
      (ProtocolRAMVisitColumns.total (walk header (groupBits L.rows) d b.edge b.tailSite heads)).eval m (i.val:Word W)=
        (sitesAt i:Word W)+ProtocolRAMTurnWalk.carried (fun j=>(sitesAt j:Word W)) i
          (ProtocolRAMVisitColumns.previous? (fun j=>(u j).raw) posPrev i))
    (banksLow : ∀a∈[b.oldSource,b.oldTarget,b.edge,b.tailSite,b.tailRole,b.headRole,b.starts,heads],a.Fits W L.zero)
    (siteFits : ∀i,0<w.width (u i).item → sitesAt i<2^W)
    (put : ProtocolRAMTurnShelf.Live (ProtocolRAMTurnInstalled.columns (record u w sitesAt) (ProtocolRAMTurnSnapshot.values b m)) ↪ ProtocolRAMTurnShelf.Seats L.sites L.seats)
    (loc : ∀z,(put z).1.val=(record u w sitesAt z.val).site ∧ (put z).2.val=(record u w sitesAt z.val).seat)
    (directory : ∀ (j : Fin 4) (t : ℕ),t<2^L.romBits →
      (ProtocolRAMTurnDirectory.bank rom L.romBits j).read m (t:Word W)=
        ProtocolRAMTurnDirectory.words L.rows L.sites L.seats L.base j t)
    (widthFit : ∀i,(record u w sitesAt i).width<2^W) (room : L.stop≤2^W) :
    ∃ out,(L.program W header rom d heads b).Exec m out (72+6096*L.rows+30*(L.sites*L.seats)) ∧
      (∀f:Fin 5,∀s:ProtocolRAMTurnShelf.Seats L.sites L.seats,
        out (L.base+f.val*(L.sites*L.seats)+s.1.val*L.seats+s.2.val)=ProtocolRAMTurnShelf.entry
          (ProtocolRAMTurnInstalled.columns (record u w sitesAt) (ProtocolRAMTurnSnapshot.values b m)) put f s) ∧
      ∀a,a<L.floor ∨ L.stop≤a → out a=m a := by
  have bounds := L.bounds
  have zi : L.zero=L.floor+1 := rfl
  have sb : L.base=L.src+6*L.rows+2^L.srcBits := rfl
  have bank : ∀a∈[b.oldSource,b.oldTarget,b.edge,b.tailSite,b.tailRole,b.headRole,b.starts],a.Fits W L.zero := by
    intro a ha
    apply banksLow
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
    tauto
  have inputs := L.walk_fits header (groupBits L.rows) d b.edge b.tailSite heads
    (L.header_fits header _ room headerBefore) safe (banksLow _ (by simp)) (banksLow _ (by simp)) (banksLow _ (by simp))
  have fits := L.scatter_fits rom L.romBits romBefore room
  obtain ⟨out,exec,stored,frame⟩ := ProtocolRAMChronologicalShelf.run_live header (groupBits L.rows) L.zero
    L.src L.srcBits rom L.romBits L.base L.scratch L.sink d heads b _ u w sitesAt m «public» old weights safe
    (L.header_fits header _ room headerBefore) (congrArg Bank.base site) (by simpa only [site] using L.site_room)
    within lenFit (by omega) posPrev closed endpoint inputs (by omega) rfl bank siteFits
    (L.field_fits header _ d b room (L.header_fits header _ room headerBefore) safe site bank)
    (by omega) put loc (by omega) (by omega) directory L.rom_capacity.1 L.rom_capacity.2
    L.src_room (by omega) widthFit bounds.2.2.2.1 (by omega) (show L.floor<L.base by omega) fits.1 fits.2
  refine ⟨out,exec,stored,?_⟩
  intro a ha
  rcases ha with low | high
  · obtain ⟨z,s,b,t,e⟩ := L.below low
    exact frame a (.inl z) (.inl s) (.inl b) (.inl t) e
  · have eq : L.sink=L.floor := rfl
    exact frame a (.inr (by omega)) (.inr (by omega)) (.inr (by omega)) (.inr (by omega)) (by omega)

end Hierarchy.ProtocolRAMTurnWindow.Layout

end OAI
