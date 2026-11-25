import OAI.Hierarchy.DescentResetStemClosedWindow
import OAI.Hierarchy.DescentResetStemStencilWord

namespace OAI
/-! # Actual stencil execution at both ends of every cable in a closed reset -/

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentSharedCableNames DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments DescentRelativeContacts DescentRosterOrder DescentTreePrefixIntervals
open DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPacking.PackedMatch.Local ThreeFlat.RAM PhysicalProcedure
open DescentPlainTerminal DescentPlainTerminal.Suffix
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "A" => input.placement
local notation "c" => B.terminals.commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i
local notation "E" => Grain A
local notation "degreeAt" => fun u=>B.reset.placement.b (B.frame.host u)
variable {wordBits slots precision t Δ threshold K wire M cap : ℕ}
variable (rank : input.V↪Fin slots) (vertex : input.V↪ℕ) (near : input.V→Finset input.V)
    (wt : input.V→Block (S.groupWidth k tail i+k)→ℕ)
    (traffic : input.V→input.V→Block (S.groupWidth k tail i+k)→ℕ) (inc : input.V→List input.V)
    (port : input.V→Fin Δ→Option input.V) (listed : ∀v u,u∈near v ↔ ∃j,port v j=some u)
    (recip : ∀v u,u∈near v→v∈near u)
local notation "q₀" => (Δ+Δ)
local notation "vec" => ContactRoster.ports near port listed recip
local notation "pnl" => Stencil.measured (n:=precision) fits near degreeAt B.frame.basis wt traffic (A).hub Δ f threshold K g cap vec inc

/-- The actual numerical stencil word and its presence tag fit the wider
signed operand column at every old host, including unoccupied rows. -/
theorem stem_stencil_word_room {field : ℕ} (wider : t<field) (out : ℕ) (mem : Memory wordBits)
    (positive : 0<M) (u : Stage.Host (Fin (S.groupCount i)) input.V k) :
    GroupStage.stencilWordAt (nBits:=t) sourceDigits B.frame.basis fits rank out mem positive u+1<2^field := by
  have bound (index raw : ℕ) : digit t index raw<2^t := by
    simp only [digit,Nat.mul_add,Nat.mul_one,pow_add,Nat.mod_mul_right_div_self]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  apply lt_of_le_of_lt _ (Nat.pow_lt_pow_right (by decide : 1<2) wider)
  exact Nat.succ_le_of_lt (bound _ _)

theorem stem_stencil_on_wire (roster : ResetInput.SourceFrame.Roster B.reset B.terminals (fun u=>(input.placement.pos u).2)
    (StarKeys.filled W.graph input.placement.pos input.placement.block sourceDigits) input.placement.hub g
    B.frame vertex near B.reset.n f threshold wire K (fun v u j=>(traffic v u j:ℝ)) Δ wt)
    (incoming : ∀u z,u∈inc z ↔ z∈near u) (smallWeight : ∀v x,wt v x<2^precision) (smallTraffic : ∀v z x,traffic v z x≤cap)
    (floorBits : m-c<2^precision) (positiveBits : 1<2^precision) (stackBits : 2^(m-c)*cap<2^precision)
    (codeBits : 2*DescentFallbackShapeTable.rows (m-c) (2^B.reset.n)≤2^t)
    (hB : 0<threshold) (hK : 0<K) (hD : 0<32*Nat.clog 2 (2*Δ))
    (tabs : Fin (Stencil.count (m-c) q₀)→Tables) (field : Stencil.Slot (m-c) q₀→Expr)
    (banks : Banks) (out : ℕ) (mem : Memory wordBits) (positive : 0<M)
    (fit : DescentSIMDLookup.Fits banks (precision*Stencil.count (m-c) q₀) (t*2^(m-c)) M slots (2^c) wordBits out)
    (bounds : Gather.Bounds (w:=wordBits) (d:=precision) (M:=M) tabs (fun j=>field (Stencil.slotName (m-c) q₀ j)) banks.source.base)
    (space : banks.source.base+slots*chunks (2^c) M<2^wordBits)
    (dictionaries : ∀j,Static (tabs j) (Gather.setField (d:=precision) j) M mem)
    (physical : Fin slots→Block c→Stencil.panel (m-c) q₀ precision)
    (actor : ∀v hi,physical (rank v) hi=pnl v hi)
    (source : ∀s,Source (field s) (fun v hi=>physical v hi s) M mem)
    (table : resident (Stencil.lookup (m-c) q₀ precision t f threshold (2^B.reset.n)) banks slots (2^c) M mem)
    (beforeTable : banks.dictionary.base+banks.dictionary.size≤banks.source.base)
    (beforeMask : banks.mask.base+banks.mask.size≤banks.source.base) :
    ∃dst,(Stencil.execute tabs field banks out slots (2^c) M wordBits).Exec mem dst (Stencil.cost tabs field slots (2^c) M) ∧
      (∀s (e : E),GroupStage.stencilWordAt (nBits:=t) sourceDigits B.frame.basis fits rank out dst positive (home A (endSite A s e))=
        signedStemWord B s (home A (endSite A s e))) ∧
      (∀z<banks.source.base,dst z=mem z) ∧ ∀z,out+slots*chunks (2^c) M≤z→dst z=mem z := by
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,order,actors,edgeName,siteName⟩
  rcases B with ⟨count,rfl,grainFit,oldOrder,orderEq,Z,T,age,depth,keyWidth,tickets,unit,dimension,
    tapeWidth,graph,frame,rosterAt,raw,rawGeometry,rawHub,rawValid,grain,wireEq,atoms,branch,capacity⟩
  obtain ⟨dst,run,atEnds,below,above⟩ := GroupStage.stem_stencil_word (w:=wordBits) (slots:=slots) (n:=precision) (t:=t)
    (Δ:=Δ) (B:=threshold) (K:=K) (wire:=wire) (f:=f) (M:=M) (cap:=cap) phase S ready
    (S.resetInputDigits ctl.base ctl.radix i) Z T frame rank vertex near wt traffic inc port listed recip roster
    incoming smallWeight smallTraffic floorBits positiveBits stackBits codeBits hB hK hD tabs field banks out
    mem positive fit bounds space dictionaries physical actor source table beforeTable beforeMask
  exact ⟨dst,run,atEnds,below,above⟩

/-- Execute the signed stencil and read its compact ticket at each actual
new receiver, retaining both memory frames from the same execution. -/
theorem stem_stencil_key_run (roster : ResetInput.SourceFrame.Roster B.reset B.terminals (fun u=>(input.placement.pos u).2)
    (StarKeys.filled W.graph input.placement.pos input.placement.block sourceDigits) input.placement.hub g
    B.frame vertex near B.reset.n f threshold wire K (fun v u j=>(traffic v u j:ℝ)) Δ wt)
    (incoming : ∀u z,u∈inc z ↔ z∈near u) (smallWeight : ∀v x,wt v x<2^precision) (smallTraffic : ∀v z x,traffic v z x≤cap)
    (floorBits : m-c<2^precision) (positiveBits : 1<2^precision) (stackBits : 2^(m-c)*cap<2^precision)
    (codeBits : 2*DescentFallbackShapeTable.rows (m-c) (2^B.reset.n)≤2^t)
    (hB : 0<threshold) (hK : 0<K) (hD : 0<32*Nat.clog 2 (2*Δ))
    (tabs : Fin (Stencil.count (m-c) q₀)→Tables) (field : Stencil.Slot (m-c) q₀→Expr)
    (banks : Banks) (out : ℕ) (mem : Memory wordBits) (positive : 0<M)
    (fit : DescentSIMDLookup.Fits banks (precision*Stencil.count (m-c) q₀) (t*2^(m-c)) M slots (2^c) wordBits out)
    (bounds : Gather.Bounds (w:=wordBits) (d:=precision) (M:=M) tabs (fun j=>field (Stencil.slotName (m-c) q₀ j)) banks.source.base)
    (space : banks.source.base+slots*chunks (2^c) M<2^wordBits)
    (dictionaries : ∀j,Static (tabs j) (Gather.setField (d:=precision) j) M mem)
    (physical : Fin slots→Block c→Stencil.panel (m-c) q₀ precision)
    (actor : ∀v hi,physical (rank v) hi=pnl v hi)
    (source : ∀s,Source (field s) (fun v hi=>physical v hi s) M mem)
    (table : resident (Stencil.lookup (m-c) q₀ precision t f threshold (2^B.reset.n)) banks slots (2^c) M mem)
    (beforeTable : banks.dictionary.base+banks.dictionary.size≤banks.source.base)
    (beforeMask : banks.mask.base+banks.mask.size≤banks.source.base)
    {keyBits : ℕ} (wider : t<keyBits)
    (signBits : DescentSignedCableCodec.width (A).degree (A).cap≤keyBits)
    (ranks : Fin (Fintype.card input.V)→Fin (DescentSharedBookScan.width (B.reset.k-c)
      (2^B.reset.n) (A).degree)→Cell (GroupStage.depthBound D n f g+2)) :
    ∃dst,(Stencil.execute tabs field banks out slots (2^c) M wordBits).Exec mem dst (Stencil.cost tabs field slots (2^c) M) ∧
      (∀u : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k,∀s (slot : Fin (2^(m-c))×Fin (2*(A).cap)),
        let root:=receiverRoot B u
        let value:=GroupStage.stencilWordAt (nBits:=t) sourceDigits B.frame.basis fits rank out dst positive
        let packet:=stemNativePane (field:=keyBits) B value ranks (B.frame.host.symm root.1) root.2
        (DescentResetStemKey.word (DescentResetStemKey.parse (A).degree (A).cap keyBits) s
          (DescentResetStemKey.panel packet slot.1 slot.2)).val=
          DescentResetStemKey.code ((oldStemAt B u s slot).map (stemTicket B s))) ∧
      (∀z<banks.source.base,dst z=mem z) ∧ ∀z,out+slots*chunks (2^c) M≤z→dst z=mem z := by
  obtain ⟨dst,run,onWire,below,above⟩ := stem_stencil_on_wire B rank vertex near wt traffic inc port listed recip roster
    incoming smallWeight smallTraffic floorBits positiveBits stackBits codeBits hB hK hD tabs field banks out
    mem positive fit bounds space dictionaries physical actor source table beforeTable beforeMask
  refine ⟨dst,run,?_,below,above⟩
  intro u s slot root value packet
  exact stem_key_read B value ranks (stem_stencil_word_room B rank wider out dst positive) signBits onWire u s slot

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
