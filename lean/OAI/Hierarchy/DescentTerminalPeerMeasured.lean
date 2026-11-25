import OAI.Hierarchy.DescentTerminalPeerDirectory

namespace OAI
/-! # A count read from the previous physical signed ports and a sorted target socket -/
namespace Hierarchy.DescentTerminalGrainProfiles.Counter
open DescentSixParty DescentSharedCableNames DescentCompiler DescentColonies DescentTerminalCableOrder DescentSortedRoster
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentPackedColony DescentTerminalPointerDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {deg k i H groups M d w p : ℕ} {bits:P→ℕ} {W:MarkedWorld F deg P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:AtomSchedule) (ready:A.StateBounds S i)
    (groupsAt:J↪Fin groups) (hosts:V↪Fin H) (raw:Fin H→Fin A.degree→Option (Fin H))
    (presentAt:∀v,present raw (hosts v)=(A.near v).map hosts)
    (C:Sockets) (m:Memory w) (cable:Block k→Fin (2*A.cap)→Bank) (positive:0<M)
local notation "R" => indexed raw
local notation "sz" => chunks groups M
local notation "boot" => C.ready H A.degree sz m
local notation "board" => Prepare.signed A native S ready groupsAt hosts
local notation "atH" => fun v:W.graph.Site=>hosts (Prod.snd (A.pos v))
local notation "source_" => source (groups:=groups) (M:=M) (C.first H A.degree) (C.ticket H A.degree) cable
local notation "col" => columns (2^k) A.cap groups M
local notation "a₀" => DescentSignedCableCodec.width A.degree A.cap
include presentAt in
theorem measured (limit:C.stop H A.degree<2^w) (graph:H<2^w) (Dfit:A.degree<2^d) (width:a₀*M≤d) (dw:d≤w)
    (rosterFit:C.roster.Fits w C.origin) (rosterSize:H*A.degree≤C.roster.size)
    (roster:∀h j,m (C.roster.base+(h.val*A.degree+j.val))=(target (R h j):Word w))
    (cableFit:∀x j,(cable x j).Fits w C.origin)
    (cableSize:∀x j,H*sz≤(cable x j).size)
    (old:∀x t,Reads (cable x t) (fun h g=>DescentSignedCableCodec.encode (board x t h g)) M m)
    (heap:H*sz≤2^w) (hp:0<p) (scale:ℕ) (grain:A.z*G.b=scale*p)
    (ix:Fin (H*A.degree)) :
    (aggregate A.degree scale positive (Gather.values (d:=d) source_ boot ix)).val=
      slotCount (p:=p) R W.graph atH ix := by
  obtain ⟨⟨h,j⟩,rfl⟩:=finProdFinEquiv.surjective ix
  let row_:=finProdFinEquiv (h,j)
  let z:Fin col→Cell d:=Gather.values source_ boot row_
  have inputs:=C.measured H A.degree R m sz limit graph rosterFit rosterSize roster h j
  have keep:= (C.mount H A.degree sz m limit).2.2
  have old' (x t) : Reads (cable x t) (fun h g=>DescentSignedCableCodec.encode (board x t h g)) M boot := by
    intro r
    rw [keep _ (by have:=cableSize x t;have:= (cableFit x t).2.2;have:= (DescentSIMDLookup.row H groups M r).isLt;omega)]
    exact old x t r
  have good (x t) (u:Fin sz) :
      ((cable x t).read boot (((h.val*sz+u.val:ℕ):Word w))).val<2^d := by
    have coord:h.val*sz+u.val=(DescentSIMDLookup.row H groups M (h,u)).val:=by simp [DescentSIMDLookup.row,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    have bound:=(DescentSIMDLookup.row H groups M (h,u)).isLt
    rw [coord,Bank.read,Fin.val_cast_of_lt (bound.trans_le heap),Nat.mod_eq_of_lt (bound.trans_le (cableSize x t)),old' x t]
    have lt:= (data (fun h g=>DescentSignedCableCodec.encode (board x t h g)) (h,u)).isLt
    exact (Nat.mod_le _ _).trans_lt (lt.trans_le (Nat.pow_le_pow_right (by decide) width))
  have sampled (x t g) : sample A.degree positive z x t g=board x t h g :=
    (reads_sample A.degree positive boot (C.first H A.degree) (C.ticket H A.degree) cable row_ h inputs.1 good cableSize heap x t g).trans
      (DescentTerminalSignedGrainWord.wing_read (cable x t) boot _ (old' x t) h g positive (width.trans dw))
  have target_ : (z (number (2^k) A.cap groups M (.inl 0))).val=Sockets.gate R h j := by
    have gateBound : Sockets.gate R h j<2^d := by
      cases dig:R h j with
      | none=>simp [Sockets.gate,dig]
      | some x=>by_cases hl:h≤x <;> simp [Sockets.gate,dig,hl]; omega
    have gateWord := gateBound.trans_le (Nat.pow_le_pow_right (by decide) dw)
    simp only [z,row_,Gather.values,source,Equiv.symm_apply_apply,Sum.elim_inl,inputs.2,
      Fin.val_cast_of_lt gateWord,Fin.val_cast_of_lt gateBound]
  change (aggregate A.degree scale positive z).val=_
  cases off:R h j with
  | none=>
    have zero:=inactive positive z (by simpa [Sockets.gate,off] using target_) A.degree scale
    simpa [slotCount,slotKey,picked,off] using zero
  | some u=>
    by_cases forward:h≤u
    · by_cases actual:∃v,hosts v=h
      · obtain ⟨v,rfl⟩:=actual
        obtain ⟨neighbor,address,ticket⟩:=reached_socket A hosts raw presentAt v j off
        have owner : (z (number (2^k) A.cap groups M (.inl 0))).val=(PackedFlow.socket A (hosts.trans Fin.valEmbedding) v neighbor).val+1 := by
          rw [ticket];simpa [Sockets.gate,off,forward] using target_
        have read:=reached A native S ready groupsAt hosts positive z v neighbor hp grain owner sampled
        simpa [slotCount,slotKey,picked,off,forward,address] using read
      · have blank (x t g) : board x t h g=none := by
          have missing:¬∃z:J×V,groupsAt z.1=g ∧ hosts z.2=h:=by rintro ⟨z,_,seen⟩;exact actual ⟨z.2,seen⟩
          simp [Prepare.signed,Prepare.spreadField,missing]
        have score:(aggregate A.degree scale positive z).val=0 := by
          change tally A.degree scale positive z=0
          simp [tally, target_, Sockets.gate, off, forward, candidate_read, sampled, blank, peerWires]
        simpa [slotCount,slotKey,picked,off,forward,absent_mass A hosts h u (not_exists.mp actual)] using score
    · have zero:=inactive positive z (by simpa [Sockets.gate,off,forward] using target_) A.degree scale
      simpa [slotCount,slotKey,picked,off,forward] using zero

end
end Hierarchy.DescentTerminalGrainProfiles.Counter

end OAI
