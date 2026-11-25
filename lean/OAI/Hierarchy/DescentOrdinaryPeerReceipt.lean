import OAI.Hierarchy.DescentOrdinaryPeerCount
import OAI.Hierarchy.DescentOrdinaryPeerCoordinates
import OAI.Hierarchy.DescentTenHopNamed

namespace OAI
/-! Every output slot of the ordinary native neighbor publisher, including
empty and padded slots, in the successor's original vertex numbering. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDyadicSpan DescentCompiler DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentOrdinaryPeerRows DescentOrdinaryPeerSlots DescentOrdinaryPeerLifts DescentTenHopRoster
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε u : ℝ} {S : AtomSchedule}
  {W : MarkedWorld F d P bits} {i z D wire hist z' D' : ℕ}
  {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε}
  {T : StageInput W G u ε} {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
  {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
  (ticket : OrdinaryLink source he T p n target)
local notation "slots" => 2^packExponent 20 source.placement.degree+2
local notation "width" => (2^(k+1)-1)*slots
local notation "window" => gap source.placement.degree+gainExponent 20 source.placement.degree
local notation "shapes" => shapeSet window k slots
local notation "E" => target.placement.degree
local notation "N" => Fintype.card source.V
local notation "N₁" => Fintype.card target.V

def ordinalPeer (pool : Finset ℕ) (sentinel j : ℕ) : ℕ :=
  if h:j<pool.card then pool.orderEmbOfFin rfl ⟨j,h⟩ else sentinel

include ticket
private theorem product_value {H R D₀ : ℕ} (old : Fin H→Fin D₀→Option (Fin H)) (oldRoom : N≤H) (_room : N₁≤R)
    (rows : ∀v y,(∃j,old ((source.vertex v).castLE oldRoom) j=some y) ↔ ∃u∈source.placement.near v,(source.vertex u).castLE oldRoom=y)
    (h : Fin R) (j : Fin E) :
    result N R width (oldWithin old) (atRow (P:=DescentTenHopRAM.paths D₀) shapes h j)=
      if yes : ∃v,(target.vertex v).val=h.val then ordinalPeer
        ((target.placement.mutual yes.choose).map (target.vertex.trans Fin.valEmbedding)) R j.val else R := by
  classical
  let oldName:=source.vertex.trans (Fin.castLEEmb oldRoom)
  obtain ⟨e,numbers,adj,card,_,_⟩:=ticket.peer_card
  have cardinal : N₁=N*width := by simpa using Fintype.card_congr e
  by_cases live : ∃v,(target.vertex v).val=h.val
  · rw [dite_eq_left live]
    let v:=live.choose
    let from_:=oldName (e v).1
    let labels:=shapes (e v).2
    let hosts:=oldSet old from_
    let pool:=(target.placement.mutual v).map (target.vertex.trans Fin.valEmbedding)
    have oldId : from_.val=(source.vertex (e v).1).val:=rfl
    have haddr : h.val=(code from_ (e v).2).val:=
      live.choose_spec.symm.trans ((numbers v).trans (code_val from_ (e v).2).symm)
    have genuine : ∀s : Fin (DescentTenHopRAM.paths D₀),oldWithin old from_ s=
        if h:s.val<hosts.card then some (hosts.orderEmbOfFin rfl ⟨s.val,h⟩) else none :=
      oldWithin_eq_get old from_
    have ys : hosts=(around source.placement.near 10 (e v).1).map oldName :=
      oldSet_named old oldName source.placement.near rows (e v).1
    have c : pool.card=hosts.card*labels.card := by
      dsimp only [pool,labels]
      rw [ys,Finset.card_map,Finset.card_map,card]
    have issu : atRow (P:=DescentTenHopRAM.paths D₀) shapes h j=requestAt shapes from_ (e v).2 j.val := by
      simpa only [request,Equiv.symm_apply_apply] using named (P:=DescentTenHopRAM.paths D₀) shapes h j from_ (e v).2 haddr
    rw [issu]
    refine (computes (P:=DescentTenHopRAM.paths D₀) N R (oldWithin old) shapes from_
      (e v).2 j.val (show from_.val<N from (source.vertex _).isLt) hosts (card_bound old from_) genuine).trans ?_
    change (entry hosts labels j.val).elim R (fun h=>h.1.val*width+h.2.val)=ordinalPeer pool R j.val
    by_cases use : j.val<hosts.card*labels.card
    · let idx : Fin (hosts.card*labels.card):=⟨j.val,use⟩
      have packed : (fun ix=>(code (selected hosts labels ix).1 (selected hosts labels ix).2).val)=pool.orderEmbOfFin c := by
        apply Finset.orderEmbOfFin_unique c _ (selected_strict hosts labels)
        intro ix
        have chosen:=selected_mem hosts labels ix
        have inMap (x : Fin H) (hx : x ∈ hosts) : x ∈ (around source.placement.near 10 (e v).1).map oldName := by
          rw [← ys]
          exact hx
        obtain ⟨raw,around_,where_⟩ := Finset.mem_map.mp (inMap _ chosen.1)
        let a:=e.symm (raw,(selected hosts labels ix).2)
        have ea : e a=(raw,(selected hosts labels ix).2):=e.apply_symm_apply _
        apply Finset.mem_map.mpr
        refine ⟨a,(adj v a).2 (by simpa only [ea] using And.intro around_ chosen.2),?_⟩
        change (target.vertex a).val=_
        rw [numbers,ea,code_val]
        exact congrArg (fun x : Fin H => x.val * width + (selected hosts labels ix).2.val) where_
      rw [entry_selected hosts labels idx]
      have good : j.val<pool.card:=by rw [c]; exact use
      rw [ordinalPeer,dite_eq_left good]
      change (selected hosts labels idx).1.val*width+(selected hosts labels idx).2.val=_
      rw [←code_val]
      exact congrFun packed idx
    · simp [entry,use,ordinalPeer,c]
  · rw [dite_eq_right live]
    unfold atRow
    split
    next isIn =>
      let xy:=finProdFinEquiv.symm (⟨h.val,isIn⟩:Fin (H*width))
      have same : (code xy.1 xy.2).val=h.val:=congrArg Fin.val (finProdFinEquiv.apply_symm_apply _)
      have padded : N≤xy.1.val:=by
        by_contra! isReal
        have vroom : h.val<N₁:=by
          rw [←same,code_val,cardinal]
          have next:=Nat.mul_le_mul_right width isReal
          rw [Nat.succ_mul] at next
          have local_:=xy.2.isLt
          omega
        let index : Fin N₁:=⟨h.val,vroom⟩
        have surj : Function.Surjective target.vertex:=((Fintype.bijective_iff_injective_and_card _).2 ⟨target.vertex.injective,by simp⟩).2
        obtain ⟨v,hv⟩:=surj index
        exact live ⟨v,congrArg Fin.val hv⟩
      exact ghost N R _ shapes xy.1 xy.2 j.val padded
    next => rfl

theorem OrdinaryLink.issued_peers {w H D₀ R : ℕ} (base : ℕ) (count sourceBank : Bank) (old : Fin H→Fin D₀→Option (Fin H))
    (m : Memory w) (oldRoom : N≤H) (newRoom : N₁≤R)
    (cf : count.Fits w base) (sf : sourceBank.Fits w base) (cap : H*D₀≤ sourceBank.size)
    (safe : DescentOrdinaryPeerCount.roof base H D₀ R E<2^w)
    (size : m count.base=(N:Word w))
    (stored : ∀a j,m (sourceBank.base+a.val*D₀+j.val)=(DescentHaloWalkRAM.number (old a j):Word w))
    (rows : ∀v y,(∃j,old ((source.vertex v).castLE oldRoom) j=some y) ↔
      ∃u∈source.placement.near v,(source.vertex u).castLE oldRoom=y) :
    let a:=DescentOrdinaryPeerCount.program w base H D₀ R E count sourceBank shapes
    a.Runs m ∧ (∀x,x<base ∨ DescentOrdinaryPeerCount.roof base H D₀ R E≤x→a.image m x=m x) ∧
      a.image m (DescentOrdinaryPeerCount.newCount base H D₀ R E).base=(N₁:Word w) ∧
      ∀h : Fin R,∀j : Fin E,a.image m ((peers base H D₀ R E).base+h.val*E+j.val)=
        ((if yes : ∃v,(target.vertex v).val=h.val then ordinalPeer
          ((target.placement.mutual yes.choose).map (target.vertex.trans Fin.valEmbedding)) R j.val else R):Word w) := by
  intro a
  have capWidth : H*DescentTenHopRAM.paths D₀≤DescentOrdinaryPeerCount.roof base H D₀ R E :=
    (span_ge _).trans ((Nat.le_add_left _ base).trans ((Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))))
  have height : H<2^w:=(Nat.le_mul_of_pos_right _ (DescentTenHopRAM.paths_pos D₀)).trans_lt (capWidth.trans_lt safe)
  have core:=DescentOrdinaryPeerCount.any base H D₀ R E count sourceBank shapes m cf sf height safe
  obtain ⟨e,_⟩:=ticket.peer_card
  have cardinal : N₁=N*width:=by simpa using Fintype.card_congr e
  refine ⟨core.1,core.2,?_,?_⟩
  · rw [cardinal]
    exact DescentOrdinaryPeerCount.count_read base N H D₀ R E count sourceBank shapes m cf sf height safe oldRoom size
  · intro h j
    have fit : h.val*E+j.val<R*E:=by
      have next:=Nat.mul_le_mul_right E h.isLt
      rw [Nat.succ_mul] at next
      have lo:=j.isLt
      omega
    have below : (peers base H D₀ R E).base+h.val*E+j.val<endAddress base H D₀ R E:=by
      change DescentOrdinaryPeerChart.out _ _ _+h.val*E+j.val<DescentOrdinaryPeerChart.out _ _ _+span (R*E)
      have upto:=fit.trans_le (span_ge (R*E))
      omega
    rw [DescentOrdinaryPeerCount.keeps _ _ _ _ _ _ _ _ _ _ below]
    have inRange : endAddress base H D₀ R E<2^w:=(Nat.le_add_right ..).trans_lt safe
    rw [DescentOrdinaryPeerRows.read base N count sourceBank shapes old m oldRoom cf sf cap height inRange size stored]
    have value := congrArg (fun x : ℕ => (x : Word w)) (product_value ticket old oldRoom newRoom (rows:=rows) h j)
    by_cases live : ∃v,(target.vertex v).val=h.val
    · simpa only [dite_eq_left live] using value
    · simpa only [dite_eq_right live] using value

end
end Hierarchy.DescentSixParty.Chronology

end OAI
