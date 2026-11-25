import OAI.Hierarchy.DescentPreparedRootInputs
import OAI.Hierarchy.DescentPhysicalRootBook

namespace OAI
/-! # The actual per-host fallback rank bank inside a completed private-root program -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSharedLeafLookup DescentSharedBookScan
open DescentSixParty.Chronology DescentSixParty DescentResetHostSize
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (b : RootBook n r D (2^r) cap field)
variable (space : a.PreparedFits b) (m : Memory w) (s : Bool) (root : Code r×Option (Fin (2^n)))
local notation "groups" => 2^c
local notation "ar" => RootTemplates.arena (a.headerEnd b) H groups M r n D
local notation "pg" => ((s,.inr root):RootPage r (2^n))
local notation "ix" => (rootIndex r (2^n) pg).val
local notation "cnt" => DescentSharedBookScan.width r (2^n) D
local notation "hdr" => b.rankHeader a.projectionEnd H groups M pg
local notation "shared" => b.common a.projectionEnd H
local notation "src" => a.preparedMid b space m
local notation "dst" => a.rootInputState b space m pg

theorem fallback_low (z : ℕ) (before : z<(ar).first ix) : dst z=src z :=
  ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl before)

theorem fallback_rank_words (low : Ht+2< w) (wide : Ht+2≤ field) :
    ∀(v : Fin H) (j : Fin cnt),dst ((hdr).ranks.base+(v.val*cnt+j.val))=
      ((((ranks (a:=r) (Y:=2^n) (D:=D) shared (2^Ht) (Ht+2) src v j).val:Cell field).val):Word w) := by
  have pf:=space.rows pg
  have len:(ar).first ix+(ar).counters≤(ar).middle ix:=Nat.add_le_add_left (RootArena.le_span _) _
  have ends:(ar).middle ix≤(ar).output ix:=Nat.le_add_right ..
  exact (scalar_prefix shared hdr Ht H D r n ((ar).first ix) src low wide pf.1.1
    ((len.trans (ends.trans (Nat.le_add_right ..))).trans_lt pf.2) rfl).2.1

/-- Bounds of the predecessor counters and broadcast ROM are available even before
the corresponding scalar program is run. -/
theorem rank_readable_of_top («until» : (ar).middle ix<2^w) :
    Readable hdr cnt H groups M field w ((ar).middle ix) := by
  let base:=b.scalarEnd a.projectionEnd H
  let pitch:=DescentSharedLeafLookup.Public.stride H groups M
  let len:=DescentSharedLeafLookup.Public.words field M
  have limit:base+2*pitch+2^Nat.clog 2 len≤ a.headerEnd b:=(b.limits a.projectionEnd H groups M).2.2
  have early:a.headerEnd b≤(ar).first ix:=Nat.le_add_right ..
  have short:H*chunks groups M≤ pitch:=Nat.le_pow_clog (by decide) _
  have enough:len≤2^Nat.clog 2 len:=Nat.le_pow_clog (by decide) _
  have window:a.headerEnd b≤(ar).middle ix:=early.trans (Nat.le_add_right ..)
  have old (v:Bank) (bound:v.base+v.size≤(ar).middle ix) : v.Fits w ((ar).middle ix):=
    ⟨Nat.two_pow_pos _,by omega,bound⟩
  constructor
  · intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl
    · exact old _ le_rfl
    · exact old _ (by change base+pitch≤ _;omega)
    · exact old _ (by change base+pitch+pitch≤ _;omega)
    · exact old _ (by change base+2*pitch+2^Nat.clog 2 len≤ _;omega)
  · exact RootArena.le_span _
  · exact short
  · exact short
  · exact enough

theorem fallback_rank_fixed :
    Fixed hdr cnt H groups M field dst ∧ Readable hdr cnt H groups M field w ((ar).middle ix) := by
  let base:=b.scalarEnd a.projectionEnd H
  let pitch:=DescentSharedLeafLookup.Public.stride H groups M
  let len:=DescentSharedLeafLookup.Public.words field M
  have safe:=space.literals
  have limit:base+2*pitch+2^Nat.clog 2 len≤ a.headerEnd b:=(b.limits a.projectionEnd H groups M).2.2
  have early:a.headerEnd b≤(ar).first ix:=Nat.le_add_right ..
  have room:=space.rows pg
  have start:(ar).middle ix≤(ar).output ix:=Nat.le_add_right ..
  have «until»:(ar).middle ix<2^w:=(start.trans (Nat.le_add_right ..)).trans_lt room.2
  have short:H*chunks groups M≤ pitch:=Nat.le_pow_clog (by decide) _
  have enough:len≤2^Nat.clog 2 len:=Nat.le_pow_clog (by decide) _
  have prev:=(a.prepared_shared b space m pg).2.2
  have printed {z:ℕ} (upper:z< a.headerEnd b) : dst z=src z:=a.fallback_low b space m s root _ (upper.trans_le early)
  have addr (q:Row H groups M) : (row H groups M q).val< pitch := (row H groups M q).isLt.trans_le short
  have pos:0< pitch:=Nat.two_pow_pos _
  have hp (q:Row H groups M) : dst ((hdr).start.base+(row H groups M q).val)=src ((hdr).start.base+(row H groups M q).val) :=
    printed (by change base+_< _;have:=addr q;omega)
  have cp (q:Row H groups M) : dst ((hdr).cut.base+(row H groups M q).val)=src ((hdr).cut.base+(row H groups M q).val) :=
    printed (by change base+pitch+_< _;have:=addr q;omega)
  refine ⟨⟨fun q=>(hp q).trans (prev.start q),fun q=>(cp q).trans (prev.cut q),?_⟩,?_⟩
  · intro j x
    have index:repeatAddr j x< len:=by
      dsimp [repeatAddr,len,DescentSharedLeafLookup.Public.words]
      calc j.val*2^field+x.val< j.val*2^field+2^field:=Nat.add_lt_add_left x.isLt _
           _≤(M+1)*2^field:=by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ j.isLt
    exact (printed (z:=(hdr).broadcast.base+repeatAddr j x) (by change base+2*pitch+_< _;omega)).trans (prev.broadcast j x)
  · exact a.rank_readable_of_top b s root «until»

/-- Old physical signed and stencil rows are all below the rank writer. The separate
terminal rank columns are produced by that writer itself, including the score on empty racks. -/
theorem fallback_operands (original : RootSources D (2^r) cap)
    (value : Fin H→Fin groups→Fin (2^r)→ℕ)
    (peer : Fin H→Fin D→Option (Fin H))
    (mark : Fin H→Fin groups→Fin (2^r)→Fin (2*cap)→Option (DescentSharedCableNames.Stage.Live D cap))
    (low : Ht+2< w) (wide : Ht+2≤ field)
    (available : ∀i,Accessible original.peers (original.tagged i) H groups M w (a.headerEnd b))
    (ns : Mounted original.peers peer src groups M)
    (ownFit : ∀i,(original.here i).Fits w (a.headerEnd b) ∧ H*chunks groups M≤(original.here i).size)
    (oldFit : ∀i j,(original.signed i j).Fits w (a.headerEnd b) ∧ H*chunks groups M≤(original.signed i j).size)
    (own : ∀i,Reads (original.here i) (fun v g=>(value v g i:Cell field)) M src)
    (tagged : ∀i,Reads (original.tagged i) (fun v g=>((value v g i+1:ℕ):Cell field)) M src)
    (old : ∀i j,Reads (original.signed i j) (fun v g=>((DescentSignedCableCodec.encode (mark v g i j)).val:Cell field)) M src) :
    let score:=fun v j=>(ranks (a:=r) (Y:=2^n) (D:=D) shared (2^Ht) (Ht+2) src v j).val
    ∀j,Source (operand (H:=H) original.peers hdr original.self original.tagged original.sign j)
      (fun h g=> inputs (field:=field) value peer mark score h g j) M dst := by
  let before:=a.headerEnd b
  have after:before≤(ar).first ix:=Nat.le_add_right ..
  have lift (bank : Bank) (fit : bank.Fits w before) (i : ℕ) (inside : i< bank.size) :
      dst (bank.base+i)=src (bank.base+i):=
    a.fallback_low b space m s root _ (((Nat.add_lt_add_left inside _).trans_le fit.2.2).trans_le after)
  have keep (q : Row H groups M) : (row H groups M q).val< H*chunks groups M:=(row H groups M q).isLt
  have recordFit:=a.fallback_rank_fixed b space m s root
  have pass : Mounted original.peers peer dst groups M := by
    let ok:=available (0 : Fin (2^r))
    constructor
    · intro q j;exact (lift _ (ok.ids j) _ ((keep q).trans_le (ok.idsRoom j))).trans (ns.ids q j)
    · intro v j
      have z:v.val*D+j.val< H*D:=(Nat.add_lt_add_left j.isLt _).trans_le (by
        rw [←Nat.succ_mul];exact Nat.mul_le_mul_right D v.isLt)
      exact (lift _ ok.roster _ (z.trans_le ok.rosterRoom)).trans (ns.roster v j)
    · intro v;exact (lift _ ok.offsets _ (v.isLt.trans_le ok.offRoom)).trans (ns.offsets v)
    · intro q;exact (lift _ ok.chunks _ ((keep q).trans_le ok.chunkRoom)).trans (ns.chunks q)
  have later:before≤(ar).middle ix:=after.trans (Nat.le_add_right ..)
  have rise {x : Bank} (f : x.Fits w before) : x.Fits w ((ar).middle ix):=
    ⟨f.1,f.2.1,f.2.2.trans later⟩
  apply operands original.peers hdr original.self original.tagged original.sign value peer mark _ ((ar).middle ix) dst
  · intro i
    let ok:=available i
    exact ⟨fun j=> rise (ok.ids j),ok.idsRoom,rise ok.roster,ok.rosterRoom,rise ok.offsets,ok.offRoom,
      rise ok.chunks,ok.chunkRoom,rise ok.source,ok.srcRoom⟩
  · exact pass
  · intro i
    exact source_column _ before (ownFit i).1 dst _ (ownFit i).2
      (fun q=>(lift _ (ownFit i).1 _ ((keep q).trans_le (ownFit i).2)).trans (own i q))
  · intro i q
    exact (lift _ (available i).source _ ((keep q).trans_le (available i).srcRoom)).trans (tagged i q)
  · intro i j
    exact source_column _ before (oldFit i j).1 dst _ (oldFit i j).2
      (fun q=>(lift _ (oldFit i j).1 _ ((keep q).trans_le (oldFit i j).2)).trans (old i j q))
  · exact recordFit.2
  · exact recordFit.1
  · exact a.fallback_rank_words b space m s root low wide

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
