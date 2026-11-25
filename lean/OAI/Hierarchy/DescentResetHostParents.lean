import OAI.Hierarchy.DescentDenseParentColumn
import OAI.Hierarchy.DescentResetHubBits
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # The dense post-reset host's original parent from the surviving raw bitmap -/
namespace Hierarchy.DescentSixParty.ResetInput
open DescentDenseHostOrder DescentCommonHost DescentHubBits DescentCensusRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "pool" => roster Z.graph (Z.k-T.commonDepth) Ht
set_option quotPrecheck false in
local notation "Vnew" => ↥(Z.commonNames T)
variable {H pad : ℕ} (vertex : Z.V↪Fin H) (room : Fintype.card ↥(Z.commonNames T) ≤ pad)
local notation "key" => rawHostRank Z T vertex
local notation "rank" => Function.Embedding.trans (denseHostRank Z T vertex) (Fin.castLEEmb room)
local notation "slots" => H*(Finset.card pool)

def parentROM (j : Fin slots) : Fin H := (finProdFinEquiv.symm j).1

theorem parentROM_val (j : Fin slots) : (parentROM Z T j).val=j.val/(Finset.card pool) := rfl

theorem parentROM_at (v : Vnew) :
    parentROM Z T (key v)=vertex (DescentDenseHostOrder.position Z.graph v.val) := by
  change (finProdFinEquiv.symm (finProdFinEquiv (hostFields Z T vertex v))).1=_
  rw [Equiv.symm_apply_apply]
  rfl

theorem true_parent_column {w : ℕ} (banks : Banks w slots (pad+1)) (flags ids codes : Bank)
    (mem : Memory w) (ff : flags.Fits w banks.first) (idd : ids.Fits w banks.first)
    (codeRoom : codes.Fits w banks.first) (roomF : slots ≤ flags.size) (roomI : slots ≤ ids.size)
    (roomC : slots ≤ codes.size)
    (bitsRead : ∀i : Fin slots,mem (flags.base+i.val)=
      (DescentEdgeTapePrefix.row (fun _ : Vnew=>1) (fun v=>(key v).val) i.val:Word w))
    (prefixRead : ∀v : Vnew,mem (ids.base+(key v).val)=((denseHostRank Z T vertex v).val:Word w))
    (static : ∀j : Fin slots,mem (codes.base+j.val)=((parentROM Z T j).val:Word w)) :
    let target:=DescentHubBits.destination banks.bins pad flags ids
    ∃out : Memory w,(tally banks target (.lookup codes .row)).Exec mem out
        (tallyCost banks target (.lookup codes .row)) ∧
      (∀v : Vnew,out (banks.bins+(denseHostRank Z T vertex v).val)=((vertex (DescentDenseHostOrder.position Z.graph v.val)).val:Word w)) ∧
      (∀v : Fin pad,(¬∃a : Vnew,(denseHostRank Z T vertex a).castLE room=v)→ out (banks.bins+v.val)=0) ∧
      ∀a < banks.first,out a=mem a := by
  classical
  have present (i : Fin slots) : mem (flags.base+i.val)=(if active key i then 1 else 0) := by
    rw [bitsRead]
    by_cases e : active key i
    · obtain ⟨v,rfl⟩:=e
      rw [DescentEdgeTapePrefix.row_present (fun _ : Vnew => 1) (fun u : Vnew => (key u).val)
        (fun _ _ eqn => (key).injective (Fin.ext eqn)) v,
        ite_eq_left (show active key (key v) from ⟨v,rfl⟩)]
      rfl
    · rw [DescentEdgeTapePrefix.row_absent _ _ i.val (fun v h=>e ⟨v,Fin.ext h⟩)]
      simp [e]
  obtain ⟨out,run,l,a,f⟩:=DescentHubBits.emit_values key (rank) banks flags ids codes (fun j=>(parentROM Z T j).val)
    mem ff idd codeRoom roomF roomI roomC present prefixRead static
  refine ⟨out,run,?_,a,f⟩
  intro v
  change out (banks.bins + ((rank) v).val) = _
  simpa only [parentROM_at Z T vertex] using l v

/-- The rank used to write each tag is produced by this same execution's prefix
of the true occupied-host bitmap. The shape ROM is fixed over the sparse rectangle. -/
theorem prefix_parents {w : ℕ} (banks : Banks w slots (pad+1)) (flags ids codes : Bank)
    (m : Memory w) (ff : flags.Fits w banks.first) (idd : ids.Fits w banks.first)
    (cf : codes.Fits w banks.first) (roomF : slots ≤ flags.size) (roomI : slots ≤ ids.size)
    (roomC : slots ≤ codes.size) (fl : flags.base+slots ≤ ids.base)
    (cd : codes.base+slots ≤ ids.base) (headRoom : ids.base+slots+1<2^w)
    (bitsRead : ∀i : Fin slots,m (flags.base+i.val)=
      (DescentEdgeTapePrefix.row (fun _ : Vnew=>1) (fun v=>(key v).val) i.val:Word w))
    (static : ∀j : Fin slots,m (codes.base+j.val)=((parentROM Z T j).val:Word w)) :
    let expr:=DescentHubBits.destination banks.bins pad flags ids
    let first:=ProtocolRAMEndpointPrefix.exclusive w flags.base ids.base slots
    ∃out : Memory w,(first.seq (tally banks expr (.lookup codes .row))).Exec m out
        ((10+(3+12*slots))+tallyCost banks expr (.lookup codes .row)) ∧
      (∀v : Vnew,out (banks.bins+(denseHostRank Z T vertex v).val)=((vertex (DescentDenseHostOrder.position Z.graph v.val)).val:Word w)) ∧
      (∀v : Fin pad,(¬∃a : Vnew,(denseHostRank Z T vertex a).castLE room=v)→ out (banks.bins+v.val)=0) ∧
      ∀a < min ids.base banks.first,out a=m a := by
  let tape:=Z.hostTape T vertex
  let after:=ProtocolRAMEndpointPrefix.image ids.base
    (DescentEdgeTapePrefix.before tape.span tape.rank) m tape.slots
  obtain ⟨first,ranks⟩:=Z.hostTape_native T vertex m fl headRoom (fun j hj=>bitsRead ⟨j,hj⟩)
  have kept (x : ℕ) (hx : x < ids.base) : after x=m x:=
    ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inl hx)
  obtain ⟨out,run,actual,ghost,low⟩:=Z.true_parent_column T vertex room banks flags ids codes after
    ff idd cf roomF roomI roomC
    (fun j=>(kept _ (by have:=j.isLt;omega)).trans (bitsRead j)) ranks
    (fun j=>(kept _ (by have:=j.isLt;omega)).trans (static j))
  exact ⟨out,(by intro P R K machine;exact Procedure.Exec.then first run machine),actual,ghost,fun a h=>(low a (lt_min_iff.mp h).2).trans
    (kept _ (lt_min_iff.mp h).1)⟩


/-- The quotient table uses only the public rectangle width.  Its entire installation and the
survivor prefix are charged before the measured scalar parent directory is read. -/
theorem publish_parents {w : ℕ} (banks : Banks w slots (pad+1)) (flags ids codes : Bank)
    (m : Memory w) (ff : flags.Fits w banks.first) (idd : ids.Fits w banks.first)
    (cf : codes.Fits w banks.first) (roomF : slots ≤ flags.size) (roomI : slots ≤ ids.size)
    (roomC : slots ≤ codes.size) (before : flags.base+slots ≤ codes.base)
    (cd : codes.base+slots ≤ ids.base) (headRoom : ids.base+slots+1<2^w)
    (bitsRead : ∀j : Fin slots,m (flags.base+j.val)=
      (DescentEdgeTapePrefix.row (fun _ : Vnew=>1) (fun v=>(key v).val) j.val:Word w)) :
    let table := fun j : ℕ=>j/(Finset.card pool)
    let head := DescentStaticWordColumn.program w codes.base table slots
    let keyExpr := DescentHubBits.destination banks.bins pad flags ids
    let pre := ProtocolRAMEndpointPrefix.exclusive w flags.base ids.base slots
    let data := tally banks keyExpr (.lookup codes .row)
    let steps := (4+10*slots)+((10+(3+12*slots))+tallyCost banks keyExpr (.lookup codes .row))
    ∃out : Memory w,(head.seq (pre.seq data)).Exec m out steps ∧
      CheapCode (head.seq (pre.seq data)) ∧ steps≤220*(1+slots+pad) ∧
      (∀v : Vnew,out (banks.bins+(denseHostRank Z T vertex v).val)=((vertex (DescentDenseHostOrder.position Z.graph v.val)).val:Word w)) ∧
      (∀j : Fin pad,(¬∃v : Vnew,(denseHostRank Z T vertex v).castLE room=j)→ out (banks.bins+j.val)=0) ∧
      ∀a < min codes.base (min ids.base banks.first),out a=m a := by
  let table := fun j : ℕ=>j/(Finset.card pool)
  let mid := DescentStaticWordColumn.image codes.base table m slots
  have init : (DescentStaticWordColumn.program w codes.base table slots).Exec m mid (4+10*slots) :=
    DescentStaticWordColumn.mount codes.base slots table m (by omega)
  have flagsAt (j : Fin slots) : mid (flags.base+j.val)=m (flags.base+j.val) :=
    DescentStaticWordColumn.frame _ _ _ _ _ (.inl (by have:=j.isLt;omega))
  obtain ⟨out,issued,data,ghost,low⟩:=Z.prefix_parents T vertex room banks flags ids codes mid ff idd cf
    roomF roomI roomC (by omega) cd headRoom (fun j=>(flagsAt j).trans (bitsRead j))
    (fun j=>DescentStaticWordColumn.read _ _ table m j.isLt)
  refine ⟨out,?_,cheap_seq (DescentStaticWordColumn.cheap w codes.base table slots) (prefix_tally_cheap banks flags ids codes),?_,data,ghost,?_⟩
  · intro P R K mach
    exact Procedure.Exec.then init issued mach
  · have bill:=prefix_tally_cost banks flags ids codes
    omega
  · intro a ha
    exact (low a (lt_min_iff.mp ha).2).trans
      (DescentStaticWordColumn.frame _ _ _ _ _ (.inl (lt_min_iff.mp ha).1))

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
