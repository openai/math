import OAI.Hierarchy.DescentResetIssuedFallback
import OAI.Hierarchy.DescentResetMeasuredFields
import OAI.Hierarchy.DescentResetStencilGather

namespace OAI
/-! # Native short terminal codes at genuine earlier signed endpoints -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments DescentRelativeContacts DescentRosterOrder DescentTreePrefixIntervals
open DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPacking.PackedMatch.Local ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "fits" => frame.enough.trans (Nat.sub_le m g)
local notation "R" => Z.placement
local notation "E" => Grain A
local notation "H" => Host J V k
local notation "src" => DescentIssuedFallbackPanel.endSite (W:=W) A
local notation "shortT" => fun t=>shortName c (T.code t)

open DescentPlainTerminal DescentPlainTerminal.Suffix
local notation "degreeAt" => fun u=>Z.placement.b (frame.host u)
local notation "limit" => fun u=>Nat.le_trans (Z.placement.depth (frame.host u)) (Nat.le_of_eq frame.extent)
local notation "sourceIx" => StarKeys.filled W.graph A.pos A.block digits
local notation "physicalSite" => home A
local notation "yAt" => fun u=>rearrange frame.basis (sourceIx u)
local notation "upperAt" => fun u=>high fits (yAt u)
local notation "lowerAt" => fun u=>@DescentPlainTerminal.low m T.commonDepth (yAt u)

variable {w slots n t Δ B K wire f M cap : ℕ}
variable (rank : V↪Fin slots) (vertex : V↪ℕ) (near : V→Finset V)
    (wt : V→Block m→ℕ) (traffic : V→V→Block m→ℕ) (inc : V→List V)
    (port : V→Fin Δ→Option V) (listed : ∀v u,u∈near v ↔ ∃j,port v j=some u)
    (recip : ∀v u,u∈near v→v∈near u)
local notation "q₀" => (Δ+Δ)
local notation "vec" => ContactRoster.ports near port listed recip
local notation "pnl" => Stencil.measured (n:=n) fits near degreeAt frame.basis wt traffic A.hub Δ f B K g cap vec inc

theorem signed_stencil_run (roster : ResetInput.SourceFrame.Roster Z T (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g frame vertex near Z.n f B wire K (fun v u j=>(traffic v u j:ℝ)) Δ wt)
    (incoming : ∀u z,u∈inc z ↔ z∈near u) (smallWeight : ∀v x,wt v x<2^n) (smallTraffic : ∀v z x,traffic v z x≤cap)
    (floorBits : m-c<2^n) (positiveBits : 1<2^n) (stackBits : 2^(m-c)*cap<2^n)
    (codeBits : 2*DescentFallbackShapeTable.rows (m-c) (2^Z.n)≤2^t)
    (hB : 0<B) (hK : 0<K) (hD : 0<32*Nat.clog 2 (2*Δ))
    (tabs : Fin (Stencil.count (m-c) q₀)→Tables) (field : Stencil.Slot (m-c) q₀→Expr)
    (banks : Banks) (out : ℕ) (mem : Memory w) (positive : 0<M)
    (fit : DescentSIMDLookup.Fits banks (n*Stencil.count (m-c) q₀) (t*2^(m-c)) M slots (2^c) w out)
    (bounds : Gather.Bounds (w:=w) (d:=n) (M:=M) tabs (fun j=>field (Stencil.slotName (m-c) q₀ j)) banks.source.base)
    (space : banks.source.base+slots*chunks (2^c) M<2^w)
    (dictionaries : ∀j,Static (tabs j) (Gather.setField (d:=n) j) M mem)
    (physical : Fin slots→Block c→Stencil.panel (m-c) q₀ n)
    (actor : ∀v hi,physical (rank v) hi=pnl v hi)
    (source : ∀s,Source (field s) (fun v hi=>physical v hi s) M mem)
    (table : resident (Stencil.lookup (m-c) q₀ n t f B (2^Z.n)) banks slots (2^c) M mem)
    (beforeTable : banks.dictionary.base+banks.dictionary.size≤banks.source.base)
    (beforeMask : banks.mask.base+banks.mask.size≤banks.source.base) :
    ∃dst,(Stencil.execute tabs field banks out slots (2^c) M w).Exec mem dst (Stencil.cost tabs field slots (2^c) M) ∧
      (∀s (e : E),let u:=src s e; let hi:=upperAt u;let low:=lowerAt u;let cell:=physicalSite u
        digit t low.val (digit (t*2^(m-c)) (lane hi positive).val (dst (out+(DescentSIMDLookup.row slots (2^c) M
          (position (rank (A.pos u).2) hi positive)).val)).val)=2*DescentFallbackShapeTable.cell (m-c)
            (shortName c (T.code (fallbackCell A S ready digits Z T frame s cell))).2+(exceptionalCell A S ready digits Z T frame cell).toNat) ∧
      (∀z<banks.source.base,dst z=mem z) ∧ ∀z,out+slots*chunks (2^c) M≤z→dst z=mem z := by
  obtain ⟨dst,exe,read,below,above⟩:=Stencil.returned (m-c) q₀ n t f B (2^Z.n) tabs field banks out mem
    physical positive fit bounds space dictionaries source table beforeTable beforeMask
  refine ⟨dst,exe,?_,below,above⟩
  intro s e
  let u:=src s e
  let hi:=upperAt u
  let x:=lowerAt u
  let cell:=physicalSite u
  let z:=(shortName c (T.code (fallbackCell A S ready digits Z T frame s cell))).2
  have legit (v : V) (hi : Block c):=Stencil.measured_input (n:=n) fits near degreeAt frame.basis wt traffic A.hub
    Δ f B K g cap vec inc limit floorBits positiveBits smallWeight smallTraffic stackBits v hi
  have native:=A.issued_fallback_word S ready digits Z T frame vertex near Z.n f B wire K Δ cap wt traffic
    roster inc incoming vec (ContactRoster.covers near port listed recip) smallTraffic hB hK hD pnl legit s e
  have word:=read (rank (A.pos u).2) hi x
  rw [actor] at word
  have legal:=T.codeLegal (fallbackCell A S ready digits Z T frame s cell)
  have level : z.1.1≤ m-c:=(Nat.sub_le_sub_right (legal.2.1.trans_eq frame.extent) c)
  have bound:=DescentFallbackShapeTable.cell_fit (m-c) z level (Nat.mod_lt _ (Nat.two_pow_pos _))
  let flag:=exceptionalCell A S ready digits Z T frame cell
  have short : 2*DescentFallbackShapeTable.cell (m-c) z+flag.toNat<2^t:=by cases flag <;> simp <;> omega
  change Stencil.word (pnl (A.pos u).2 hi) f B (2^Z.n) x=2*DescentFallbackShapeTable.cell (m-c) z+flag.toNat at native
  rw [native,Fin.val_cast_of_lt short] at word
  exact word

theorem all_stencil_values (roster : ResetInput.SourceFrame.Roster Z T (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g frame vertex near Z.n f B wire K (fun v u j=>(traffic v u j:ℝ)) Δ wt)
    (incoming : ∀u z,u∈inc z ↔ z∈near u) (smallWeight : ∀v x,wt v x<2^n) (smallTraffic : ∀v z x,traffic v z x≤cap)
    (floorBits : m-c<2^n) (positiveBits : 1<2^n) (stackBits : 2^(m-c)*cap<2^n)
    (codeBits : 2*DescentFallbackShapeTable.rows (m-c) (2^Z.n)≤2^t)
    (hB : 0<B) (hK : 0<K) (hD : 0<32*Nat.clog 2 (2*Δ)) :
    let safe:=roster.2.2.2.2.2.choose
    let row:=DescentPlainTerminal.endpoint near degreeAt frame.basis wt f (32*Nat.clog 2 (2*Δ)) B g (2^Z.n) safe
      (fun v j=>(frame.host v,j)∈Z.placement.keys) A.hub
    ∀v (hi : Block c) (x : Block (m-c)),((Stencil.word (pnl v hi) f B (2^Z.n) x:ℕ):Cell t).val=
      2*Stencil.shapeCode (m-c) (2^Z.n) (fieldsRelative c (row v ((rearrange frame.basis).symm (join fits hi x))))+
        ((A.hub v) || decide ((frame.host v,group (degreeAt v) (join fits hi x))∈Z.placement.keys)).toNat := by
  intro safe row v hi x
  let original:=(rearrange frame.basis).symm (join fits hi x)
  let keys:=resetKeys near Δ f B K wt (fun u z i=>(traffic u z i:ℝ)) degreeAt limit frame.basis
  have same : (fun u j=>(u,j)∈keys)=(fun u j=>(frame.host u,j)∈Z.placement.keys) :=
    funext fun u=>funext fun j=>propext (roster.2.2.2.1 u j).symm
  have legit:=Stencil.measured_input (n:=n) fits near degreeAt frame.basis wt traffic A.hub Δ f B K g cap vec inc
    limit floorBits positiveBits smallWeight smallTraffic stackBits v hi
  have native:=Stencil.issued_word fits near degreeAt frame.basis wt traffic A.hub Δ f B K g (2^Z.n) cap
    hi v (vec v) inc (pnl v hi) (fun v=>T.commonLow _) frame.enough limit safe smallTraffic hK hB hD
    incoming (ContactRoster.covers near port listed recip v) legit x
  dsimp only at native
  have mark : ((v,group (degreeAt v) (join fits hi x))∈keys) ↔
      ((frame.host v,group (degreeAt v) (join fits hi x))∈Z.placement.keys):=(roster.2.2.2.1 _ _).symm
  change Stencil.word (pnl v hi) f B (2^Z.n) x=2*Stencil.shapeCode (m-c) (2^Z.n) (fieldsRelative c
    (DescentPlainTerminal.endpoint near degreeAt frame.basis wt f (32*Nat.clog 2 (2*Δ)) B g (2^Z.n) safe
      (fun u j=>(u,j)∈keys) A.hub v original))+((A.hub v) || decide ((v,group (degreeAt v) (join fits hi x))∈keys)).toNat at native
  have markBit : decide ((v,group (degreeAt v) (join fits hi x))∈keys) =
      decide ((frame.host v,group (degreeAt v) (join fits hi x))∈Z.placement.keys) := Bool.decide_congr mark
  rw [same,markBit] at native
  obtain ⟨term,ht,eqn⟩:=(roster.2.2.2.2.2.choose_spec.2 v (row v original)).mpr ⟨original,rfl⟩
  let z:=(shortName c (T.code term)).2
  have level : z.1.1≤ m-c:=Nat.sub_le_sub_right ((T.codeLegal term).2.1.trans_eq frame.extent) c
  have cell:=DescentFallbackShapeTable.cell_fit (m-c) z level (Nat.mod_lt _ (Nat.two_pow_pos _))
  have identity : Stencil.shapeCode (m-c) (2^Z.n) (fieldsRelative c (row v original))=DescentFallbackShapeTable.cell (m-c) z:=by
    rw [←eqn,←fields_relative]
    exact Stencil.shapeCode_fields _ _
  have short : Stencil.word (pnl v hi) f B (2^Z.n) x<2^t:=by
    rw [native]
    change 2*Stencil.shapeCode (m-c) (2^Z.n) (fieldsRelative c (row v original))+_ < _
    rw [identity]
    cases (A.hub v || decide ((frame.host v,group (degreeAt v) (join fits hi x))∈Z.placement.keys)) <;> simp <;> omega
  rw [Fin.val_cast_of_lt short]
  exact native

theorem all_stencil_words (roster : ResetInput.SourceFrame.Roster Z T (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g frame vertex near Z.n f B wire K (fun v u j=>(traffic v u j:ℝ)) Δ wt)
    (incoming : ∀u z,u∈inc z ↔ z∈near u) (smallWeight : ∀v x,wt v x<2^n) (smallTraffic : ∀v z x,traffic v z x≤cap)
    (floorBits : m-c<2^n) (positiveBits : 1<2^n) (stackBits : 2^(m-c)*cap<2^n)
    (codeBits : 2*DescentFallbackShapeTable.rows (m-c) (2^Z.n)≤2^t)
    (hB : 0<B) (hK : 0<K) (hD : 0<32*Nat.clog 2 (2*Δ))
    (tabs : Fin (Stencil.count (m-c) q₀)→Tables) (field : Stencil.Slot (m-c) q₀→Expr)
    (banks : Banks) (out : ℕ) (mem : Memory w) (positive : 0<M)
    (fit : DescentSIMDLookup.Fits banks (n*Stencil.count (m-c) q₀) (t*2^(m-c)) M slots (2^c) w out)
    (bounds : Gather.Bounds (w:=w) (d:=n) (M:=M) tabs (fun j=>field (Stencil.slotName (m-c) q₀ j)) banks.source.base)
    (space : banks.source.base+slots*chunks (2^c) M<2^w)
    (dictionaries : ∀j,Static (tabs j) (Gather.setField (d:=n) j) M mem)
    (physical : Fin slots→Block c→Stencil.panel (m-c) q₀ n)
    (actor : ∀v hi,physical (rank v) hi=pnl v hi)
    (source : ∀s,Source (field s) (fun v hi=>physical v hi s) M mem)
    (table : resident (Stencil.lookup (m-c) q₀ n t f B (2^Z.n)) banks slots (2^c) M mem)
    (beforeTable : banks.dictionary.base+banks.dictionary.size≤banks.source.base)
    (beforeMask : banks.mask.base+banks.mask.size≤banks.source.base) :
    let safe:=roster.2.2.2.2.2.choose
    let row:=DescentPlainTerminal.endpoint near degreeAt frame.basis wt f (32*Nat.clog 2 (2*Δ)) B g (2^Z.n) safe
      (fun v j=>(frame.host v,j)∈Z.placement.keys) A.hub
    ∃dst,(Stencil.execute tabs field banks out slots (2^c) M w).Exec mem dst (Stencil.cost tabs field slots (2^c) M) ∧
      (∀v (hi : Block c) (x : Block (m-c)),digit t x.val (digit (t*2^(m-c)) (lane hi positive).val
        (dst (out+(DescentSIMDLookup.row slots (2^c) M (position (rank v) hi positive)).val)).val)=
        2*Stencil.shapeCode (m-c) (2^Z.n) (fieldsRelative c (row v ((rearrange frame.basis).symm (join fits hi x))))+
          ((A.hub v) || decide ((frame.host v,group (degreeAt v) (join fits hi x))∈Z.placement.keys)).toNat) ∧
      (∀z<banks.source.base,dst z=mem z) ∧ ∀z,out+slots*chunks (2^c) M≤z→dst z=mem z := by
  intro safe row
  obtain ⟨dst,exe,read,below,above⟩:=Stencil.returned (m-c) q₀ n t f B (2^Z.n) tabs field banks out mem
    physical positive fit bounds space dictionaries source table beforeTable beforeMask
  refine ⟨dst,exe,?_,below,above⟩
  intro v hi x
  have native:=A.all_stencil_values S ready digits Z T frame vertex near wt traffic inc port listed recip roster
    incoming smallWeight smallTraffic floorBits positiveBits stackBits codeBits hB hK hD v hi x
  have atRow:=read (rank v) hi x
  rw [actor] at atRow
  exact atRow.trans native

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
