import OAI.Hierarchy.DescentResetSignedStencilRun
import OAI.Hierarchy.DescentResetMeasuredReturn
import OAI.Hierarchy.DescentRecordedReservationRead

namespace OAI
/-! # The attained reset stencil cell is exactly its original terminal code and exceptional flag -/
set_option quotPrecheck false
namespace Hierarchy.DescentSixParty.ResetInput
open DescentGL DescentColonies DescentPlainTerminal DescentPlainTerminal.Suffix DescentSIMDLookup
open DescentChosenRouter DescentResetAttachments DescentRelativeContacts DescentRosterOrder
open DescentTreePrefixIntervals DescentIssuedFallbackPanel DescentPacking.PackedMatch.Local
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V]
  {d m g h C Ht n f B wire K Δ cap t : ℕ} {bits : P→ℕ} {N : MarkedWorld F d P bits}
  {price ε : ℝ} {Z : ResetInput N price ε h C Ht} {T : Z.Terminals}
  {pos : N.graph.Site→V} {ix : N.graph.Site→Block m} {hub : V→Bool} (frame : Z.SourceFrame T pos ix hub g)
  (vertex : V↪ℕ) (near : V→Finset V) (wt : V→Block m→ℕ) (traffic : V→V→Block m→ℕ)
  (inc : V→List V) (port : V→Fin Δ→Option V) (listed : ∀v u,u∈near v ↔ ∃j,port v j=some u)
  (recip : ∀v u,u∈near v→v∈near u)
local notation "c" => T.commonDepth
local notation "fits" => frame.enough.trans (Nat.sub_le ..)
local notation "degreeAt" => fun u=>Z.placement.b (frame.host u)
local notation "limit" => fun u=>(Z.placement.depth (frame.host u)).trans_eq frame.extent
local notation "vec" => ContactRoster.ports near port listed recip
local notation "pnl" => Stencil.measured (n:=n) fits near degreeAt frame.basis wt traffic hub Δ f B K g cap vec inc

theorem SourceFrame.stencil_values (roster : frame.Roster (Z:=Z) (T:=T) (pos:=pos) (ix:=ix) (hub:=hub) (g:=g) vertex near Z.n f B wire K (fun v u j=>(traffic v u j:ℝ)) Δ wt)
    (incoming : ∀u z,u∈inc z ↔ z∈near u) (smallWeight : ∀v x,wt v x<2^n) (smallTraffic : ∀v z x,traffic v z x≤cap)
    (floorBits : m-c<2^n) (positiveBits : 1<2^n) (stackBits : 2^(m-c)*cap<2^n)
    (codeBits : 2*DescentFallbackShapeTable.rows (m-c) (2^Z.n)≤2^t)
    (hB : 0<B) (hK : 0<K) (hD : 0<32*Nat.clog 2 (2*Δ)) :
    let safe:=roster.2.2.2.2.2.choose
    let row:=DescentPlainTerminal.endpoint near degreeAt frame.basis wt f (32*Nat.clog 2 (2*Δ)) B g (2^Z.n) safe
      (fun v j=>(frame.host v,j)∈Z.placement.keys) hub
    ∀v (hi : Block c) (x : Block (m-c)),((Stencil.word (pnl v hi) f B (2^Z.n) x:ℕ):Cell t).val=
      2*Stencil.shapeCode (m-c) (2^Z.n) (fieldsRelative c (row v ((rearrange frame.basis).symm (join fits hi x))))+
        ((hub v) || decide ((frame.host v,group (degreeAt v) (join fits hi x))∈Z.placement.keys)).toNat := by
  intro safe row v hi x
  let original:=(rearrange frame.basis).symm (join fits hi x)
  let keys:=resetKeys near Δ f B K wt (fun u z i=>(traffic u z i:ℝ)) degreeAt limit frame.basis
  have same : (fun u j=>(u,j)∈keys)=(fun u j=>(frame.host u,j)∈Z.placement.keys) :=
    funext fun u=>funext fun j=>propext (roster.2.2.2.1 u j).symm
  have legit:=Stencil.measured_input (n:=n) fits near degreeAt frame.basis wt traffic hub Δ f B K g cap vec inc
    limit floorBits positiveBits smallWeight smallTraffic stackBits v hi
  have native:=Stencil.issued_word fits near degreeAt frame.basis wt traffic hub Δ f B K g (2^Z.n) cap
    hi v (vec v) inc (pnl v hi) (fun v=>T.commonLow _) frame.enough limit safe smallTraffic hK hB hD
    incoming (ContactRoster.covers near port listed recip v) legit x
  dsimp only at native
  have mark : ((v,group (degreeAt v) (join fits hi x))∈keys) ↔
      ((frame.host v,group (degreeAt v) (join fits hi x))∈Z.placement.keys):=(roster.2.2.2.1 _ _).symm
  change Stencil.word (pnl v hi) f B (2^Z.n) x=2*Stencil.shapeCode (m-c) (2^Z.n) (fieldsRelative c
    (DescentPlainTerminal.endpoint near degreeAt frame.basis wt f (32*Nat.clog 2 (2*Δ)) B g (2^Z.n) safe
      (fun u j=>(u,j)∈keys) hub v original))+((hub v) || decide ((v,group (degreeAt v) (join fits hi x))∈keys)).toNat at native
  have flag : decide ((v,group (degreeAt v) (join fits hi x))∈keys) =
      decide ((frame.host v,group (degreeAt v) (join fits hi x))∈Z.placement.keys) := decide_eq_decide.mpr mark
  rw [same,flag] at native
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
    cases (hub v || decide ((frame.host v,group (degreeAt v) (join fits hi x))∈Z.placement.keys)) <;> simp <;> omega
  rw [Fin.val_cast_of_lt short]
  exact native


end
end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentCompiler DescentGL DescentColonies DescentPlainTerminal DescentPlainTerminal.Suffix DescentSIMDLookup
open DescentChosenRouter DescentResetAttachments DescentRelativeContacts DescentRosterOrder DescentTreePrefixIntervals
open DescentPacking.PackedMatch.Local DescentIssuedFallbackPanel
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p)
local notation "A" => input.placement
local notation "K" => quota S.rounds
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i
local notation "full" => (A).wire*((A).z*G.b)*(A).cap
local notation "width" => S.groupWidth k tail i+k
local notation "cc" => reset.terminals.commonDepth
local notation "oldDepth" => fun v=>reset.reset.placement.b (reset.frame.host v)
local notation "oldBad" => fun v j=>(reset.frame.host v,j)∈reset.reset.placement.keys
local notation "symNear" => fun v u (hit:u∈(A).near v)=>((A).symmetric v u).mp hit
local notation "rcp" => fun v u (hit:u∈(A).mutual v)=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hit).2,(Finset.mem_filter.mp hit).1⟩

theorem old_roster : reset.frame.Roster (Z:=reset.reset) (T:=reset.terminals) (pos:=_) (ix:=_) (hub:=_) (g:=g) (input.vertex.trans Fin.valEmbedding) (A).mutual reset.reset.n f full (A).wire K
    (fun v u j=>((A).resetFlow sourceDigits v u j:ℝ)) (A).degree ((A).resetLoad sourceDigits) := by
  simp only [reset.dimension,input.edges,input.grain]
  convert reset.roster using 1
  funext v u j
  simp only [GroupStage.resetFlow,input.edges,input.grain]
  exact congrArg (fun cnt => (pairLoad (W.countWorld cnt) (fun v => ((A).pos v).2)
    (StarKeys.filled W.graph (A).pos (A).block sourceDigits) (wire*(z*G.b)) v u j : ℝ)) reset.count_eq.symm

def originalCell (v : input.V) (x : Block width) :=
  let rows:=old_roster (reset:=reset)
  endpoint (A).mutual oldDepth reset.frame.basis ((A).resetLoad sourceDigits) f (32*Nat.clog 2 (2*(A).degree)) full g
    (2^reset.reset.n) rows.2.2.2.2.2.choose oldBad (A).hub v x

def realPanel {m : ℕ} (dim : m=width) (basis : Layout m) (nbits t : ℕ) (v : input.V) (hi : Block cc)
    (x : Block (m-cc)) : Cell t :=
  let xy:=(Equiv.cast (congrArg Block dim)).trans sourceDigits
  let name:=((A).numberedHeader xy input.vertex).site
  let dep:=((A).mixerHeader xy name).depth A f
  let ports:=ContactRoster.ports (A).mutual (PackedFlow.portAt A name) (PackedFlow.actual_ports A name symNear) rcp
  let incoming:=fun v:input.V=>(DescentPackedColony.slots (A).degree).filterMap (PackedFlow.portAt A name v)
  let low:cc≤ m:=by rw [dim];exact reset.frame.enough.trans (Nat.sub_le ..)
  let data:=Stencil.measured (n:=nbits) low (A).mutual dep basis ((A).resetLoad xy) ((A).resetFlow xy)
    (A).hub (A).degree f full K g full ports incoming v hi
  (Stencil.word data f full (2^reset.reset.n) x:ℕ)

include accepted in
/-- The source cell named by one physical high group and one lower index is a true
old endpoint, including when there is no old actor in that source cell. -/
theorem stencil_cell {m nbits t : ℕ} (dim : m=width) (μ : Layout m) (won : HEq μ reset.frame.basis)
    (level : m-cc<2^nbits) (one : 1<2^nbits) (capacity : 2^(m-cc)*full<2^nbits)
    (shape : 2*DescentFallbackShapeTable.rows (m-cc) (2^reset.reset.n)≤2^t)
    (active : 0<full) (quotaPos : 0<K) (degreePos : 0<32*Nat.clog 2 (2*(A).degree))
    (v : input.V) (hi : Block cc) (x : Block (m-cc)) :
    let atOld:=(rearrange reset.frame.basis).symm
      (join (reset.frame.enough.trans (Nat.sub_le ..)) hi (Fin.cast (congrArg (fun z=>2^(z-cc)) dim) x))
    (realPanel (reset:=reset) dim μ nbits t v hi x).val=
      2*Stencil.shapeCode (m-cc) (2^reset.reset.n) (fieldsRelative cc (originalCell (reset:=reset) v atOld))+
      (((A).hub v) || decide (oldBad v (group (oldDepth v) (rearrange reset.frame.basis atOld)))).toNat := by
  subst m
  have eq:=eq_of_heq won
  subst μ
  let name:=((A).numberedHeader sourceDigits input.vertex).site
  let dep:=((A).mixerHeader sourceDigits name).depth A f
  have levels:dep=oldDepth:=funext fun v=>(accepted.measured.depth v).symm
  have rows:=old_roster (reset:=reset)
  have weights (v:input.V) (x:Block width) : (A).resetLoad sourceDigits v x<2^nbits:=by
    have fullBound:full≤2^(width-cc)*full:=Nat.le_mul_of_pos_left full (Nat.two_pow_pos _)
    exact ((A).reset_words_at S input.valid sourceDigits v v x).2.trans_lt (fullBound.trans_lt capacity)
  have paid (v u:input.V) (x:Block width) : (A).resetFlow sourceDigits v u x≤full:=
    ((A).reset_words_at S input.valid sourceDigits v u x).1.trans ((A).reset_words_at S input.valid sourceDigits v u x).2
  have scalar:=reset.frame.stencil_values (input.vertex.trans Fin.valEmbedding) (A).mutual ((A).resetLoad sourceDigits)
    ((A).resetFlow sourceDigits) (fun v=>(DescentPackedColony.slots (A).degree).filterMap (PackedFlow.portAt A name v))
    (PackedFlow.portAt A name) (PackedFlow.actual_ports A name symNear) rcp rows (PackedFlow.Padded.listed_at A name)
    weights paid level one capacity shape active quotaPos degreePos v hi x
  simp only [realPanel,Equiv.cast_refl,Equiv.refl_trans,originalCell,Fin.cast_refl,id_eq,
    Equiv.apply_symm_apply]
  erw [show ((A).mixerHeader sourceDigits name).depth A f = oldDepth from levels]
  exact scalar

end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
