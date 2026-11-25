import OAI.Hierarchy.DescentPhysicalRootBook
import OAI.Hierarchy.DescentPreparedWindowRead
import OAI.Hierarchy.DescentRotorReservationSources

namespace OAI
/-! # Padded donor board read from the same prior signed, geometry and reservation banks -/
namespace Hierarchy.DescentFallbackPeriod.Projected.RootSources
open DescentRotorWindowArchive DescentSharedCableNames.Stage DescentSharedLeafLookup DescentSharedBookScan
open DescentPackedZip DescentPackedColony DescentSIMDLookup DescentFallbackRankRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M field w D L cap n r : ℕ} (src : RootSources D L cap)
variable (own : Fin H→Fin G→Fin L→ℕ) (next : Fin H→Fin D→Option (Fin H))
    (marks : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap))
    (rank : Fin H→Fin (width r (2^n) D)→ℕ)
    (ord : Fin H→Fin G→Fin L→Fin L→Bool)
    (quota : Fin H→Fin D→Fin D→Fin 6→Cell field)

/-- This is the true signed predecessor window, read at both ends of an old cable. The
last part of the rotor board carries the directed reserved columns in their original port order. -/
def paddedRow (h : Fin H) (g : Fin G) : Fin (DescentRotorWindowArchive.count D L cap)→Cell field :=
  fun j=>observed (inputs (field:=field) own next marks rank h g) (ord h g) (quota h) (ix.symm j)

theorem matrix_sources {exponent : ℕ} (src : RootSources D (2^exponent) cap)
    (own : Fin H→Fin G→Fin (2^exponent)→ℕ) (next : Fin H→Fin D→Option (Fin H))
    (marks : Fin H→Fin G→Fin (2^exponent)→Fin (2*cap)→Option (Live D cap))
    (rank : Fin H→Fin (width r (2^n) D)→ℕ)
    (ord : Fin H→Fin G→Fin (2^exponent)→Fin (2^exponent)→Bool)
    (quota : Fin H→Fin D→Fin D→Fin 6→Cell field) (ceiling : ℕ) (m : Memory w)
    (addressable : ∀i,Accessible src.peers (src.tagged i) H G M w ceiling)
    (mounted : Mounted src.peers next m G M)
    (localFit : ∀i,(src.here i).Fits w ceiling ∧ H*chunks G M≤(src.here i).size)
    (signFit : ∀i j,(src.signed i j).Fits w ceiling ∧ H*chunks G M≤(src.signed i j).size)
    (current : ∀i,Reads (src.here i) (fun h g=>(own h g i:Cell field)) M m)
    (tagged : ∀i,Reads (src.tagged i) (fun h g=>((own h g i+1:ℕ):Cell field)) M m)
    (signed : ∀i j,Reads (src.signed i j) (fun h g=>((DescentSignedCableCodec.encode (marks h g i j)).val:Cell field)) M m)
    (measuredOrder : ∀i j,Source (src.oldOrder i j) (fun h g=>((ord h g i j).toNat:Cell field)) M m)
    (reservation : ∀p j f,Source (src.reservation p j f) (fun h (_:Fin G)=>quota h p j f) M m) :
    ∀j,Source (src.matrixRow H j) (fun h g=>paddedRow own next marks rank ord quota h g j) M m := by
  intro j
  obtain ⟨j,rfl⟩:=ix.surjective j
  simp only [matrixRow,paddedRow,Equiv.symm_apply_apply]
  rcases j with ((i|⟨p,i⟩)|⟨i,q⟩)|(⟨i,k⟩|⟨p,k,f⟩)
  · exact source_column _ ceiling (localFit i).1 m _ (localFit i).2 (current i)
  · have eqn (h : Fin H) (g : Fin G) :
        (next h p).elim (0:Cell field) (fun u=>((own u g i+1:ℕ):Cell field)) =
        inputs (field:=field) own next marks rank h g (.inl (.inr (p,i))) := by
      cases q:next h p <;> simp [inputs,q]
    simpa only [matrixFields,observed,eqn] using
      peerSource src.peers (src.tagged i) ceiling (addressable i) next m mounted
        (fun h g=>((own h g i+1:ℕ):Cell field)) (tagged i) p
  · exact source_column _ ceiling (signFit i q).1 m _ (signFit i q).2 (signed i q)
  · exact measuredOrder i k
  · exact reservation p k f

/-- A real host may occupy a row of any padded upstream arena. The board row at that
physical name then agrees at every cell with the directly observed router window. -/
theorem paddedRow_at {board : Type*} (name : board→Fin H)
    (win : board→Fin G→Packet D L cap n r field) (before : board→Fin G→Fin L→Fin L→Bool)
    (pair : board→Fin D→Fin D→Fin 6→Cell field)
    (packetAt : ∀v g,inputs (field:=field) own next marks rank (name v) g=win v g)
    (orderAt : ∀v g,ord (name v) g=before v g) (quotaAt : ∀v,quota (name v)=pair v)
    (v : board) (g : Fin G) (j : DescentRotorWindowArchive.Input D L cap) :
    paddedRow own next marks rank ord quota (name v) g (ix j)=observed (win v g) (before v g) (pair v) j := by
  simp only [paddedRow,Equiv.symm_apply_apply,packetAt,orderAt,quotaAt]

end
end Hierarchy.DescentFallbackPeriod.Projected.RootSources

namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.SignedFields DescentGL
open DescentPackedColony DescentPackedZip DescentSIMDLookup DescentSixParty DescentGroupPeerOrder DescentStageEdgeReceipt
open DescentSharedCableNames.Stage DescentIssuedFallbackPanel DescentColonies DescentPacking.PackedMatch.Local
open DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentPackedColony
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i w n h l c H G K R M Ht t field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {gate : PoweredGadget F} {q ε : ℝ} (A : GroupStage W gate q ε J V k)
    (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J≃Fin G) (host : V↪Fin H)
local notation "L" => 2^(h+l-c)
local notation "D" => 2*A.cap
local notation "degree" => A.degree
local notation "b" => DescentSignedCableCodec.width A.degree A.cap
local notation "N" => 2^k
variable (a : Receiver A.degree A.cap (2^k) n (h+l-c) c H G K R M h l t field Ht w)
local notation "outputs" => bankAt a.stencil a.tapped t degree a.signedEnd H (2^c) M

variable (peers : Ports A.degree) (order : Fin (2^(h+l-c))→Fin (2^(h+l-c))→Expr) (pair : Fin A.degree→Fin A.degree→Fin 6→Expr)
    (oldCap selectedDepth : Expr)
local notation "src" => a.rootSources peers order pair oldCap selectedDepth

theorem Receiver.projected_bank_access (ceiling : ℕ) (word : ceiling<2^w)
    (space : a.projectionEnd+2^(Nat.clog 2 (H*chunks (2^c) M))≤ceiling) (q : Column L A.cap) :
    (outputs q).Fits w ceiling ∧ H*chunks (2^c) M≤(outputs q).size := by
  let idx:=(column L A.cap) q
  have room:=extent (H:=H) (G:=2^c) (M:=M) (spec a.stencil a.tapped t degree q) a.signedEnd (maxBits t degree A.cap L) idx
    (word_bound a.stencil a.tapped q)
  have stops : (spec a.stencil a.tapped t degree q).stop (a.atQuery idx) H (2^c) M≤a.projectionEnd:=by
    exact room.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ idx.isLt) _)
  have start : (outputs q).base≤a.projectionEnd:=(Nat.le_add_right _ _).trans stops
  have bounds : (outputs q).base+(outputs q).size≤ceiling:=(Nat.add_le_add_right start _).trans space
  exact ⟨⟨Nat.two_pow_pos _,((Nat.le_add_left _ _).trans bounds).trans_lt word,bounds⟩,Nat.le_pow_clog (by decide) _⟩

/-- The middle state starts every real root job. The final state preserves the same
projected predecessor values after all root rows have been written. -/
def Receiver.boardMemory {D₀ cap₀ N₀ n₀ r₀ c₀ H₀ G₀ K₀ R₀ M₀ h₀ l₀ t₀ field₀ Ht₀ w₀ : ℕ}
    (cpu : Receiver D₀ cap₀ N₀ n₀ r₀ c₀ H₀ G₀ K₀ R₀ M₀ h₀ l₀ t₀ field₀ Ht₀ w₀)
    (book : RootBook n₀ r₀ D₀ (2^r₀) cap₀ field₀) (space : cpu.PreparedFits book)
    (mid : Bool) (mem : Memory w₀) : Memory w₀ :=
  if mid then cpu.preparedMid book space mem else cpu.preparedImage book space mem

theorem prepared_board (mid : Bool) (book : RootBook n (h+l-c) degree L A.cap field) (space : a.PreparedFits book)
    (μ : DescentGL.Layout (h+l)) (size : 2^(h+l)=G*N) (width : 2^l=M*N)
    (small : c≤h+l) (repack : M*L=2^l) (mem : Memory w)
    (sources : ∀j x,Reads (a.old j x) (fun v g=>DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) (R*M) mem)
    (saved : mem a.saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (beforeKey : a.saved.Fits w a.origin) (shape : a.stencil.Fits w a.origin)
    (sizeOfShape : H*chunks (2^c) M≤a.stencil.size)
    (code : V→Block c→Fin L→Cell t)
    (stencil : PackedFlow.Padded.Published (h:=h) (l:=l) M t a.stencil.base host code mem)
    (ceiling : ℕ) (next : Fin H→Fin degree→Option (Fin H))
    (priorOrder : Fin H→Block c→Fin L→Fin L→Bool)
    (capacity : Fin H→Fin degree→Fin degree→Fin 6→Cell field)
    (rank : Fin H→Fin (DescentSharedBookScan.width (h+l-c) (2^n) degree)→ℕ)
    (addr : ∀x,Accessible peers ((src).tagged x) H (2^c) M w ceiling)
    (neighbor : Mounted peers next (a.boardMemory book space mid mem) (2^c) M)
    (currentFit : ∀i,((src).here i).Fits w ceiling ∧ H*chunks (2^c) M≤((src).here i).size)
    (markedFit : ∀i j,((src).signed i j).Fits w ceiling ∧ H*chunks (2^c) M≤((src).signed i j).size)
    (earlier : ∀x y,Source (order x y) (fun v hi=>((priorOrder v hi x y).toNat:Cell field)) M (a.boardMemory book space mid mem))
    (reservation : ∀p j z,Source (pair p j z) (fun v (_:Block c)=>capacity v p j z) M (a.boardMemory book space mid mem)) :
    ∃(values : Fin H→Block c→Fin L→Cell t) (ports : Fin H→Block c→Fin L→Fin D→Option (Live degree A.cap)),
      (∀j,Source ((src).matrixRow H j)
        (fun v hi=>RootSources.paddedRow (fun v hi x=>(values v hi x).val) next ports rank priorOrder capacity v hi j)
        M (a.boardMemory book space mid mem)) ∧
      (∀v hi x,values (host v) hi x=code v hi x) ∧
      ∀v hi x j,ports (host v) hi x j=signedPanel A native S ready
        (DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (host.trans Fin.valEmbedding)))
        (donor (PackedFlow.digits groups size) μ small v hi x) j := by
  obtain ⟨values,ports,curr,tag,sign,ownAt,portAt⟩:=window_frame A native S ready groups host a space.toPrefixFits μ size
    width small repack mem (a.boardMemory book space mid mem) (by
      cases mid
      · exact a.prepared_window book space mem
      · exact a.prepared_mid_window book space mem)
    sources saved beforeKey shape sizeOfShape code stencil
  exact ⟨values,ports,(src).matrix_sources (fun v hi x=>(values v hi x).val) next ports rank priorOrder
    capacity ceiling _ addr neighbor currentFit markedFit curr (fun x=>by simpa only [Receiver.rootSources, Nat.cast_add, Nat.cast_one] using tag x) (fun x j=>sign j x) earlier reservation,ownAt,portAt⟩

end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
