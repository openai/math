import OAI.Hierarchy.DescentRecordedStencilCell
import OAI.Hierarchy.DescentResetActorIssued

namespace OAI
/-! # Reset actors from the actual recorded estimator and its published stencil word -/
namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentCompiler DescentGL DescentColonies DescentPlainTerminal DescentPlainTerminal.Suffix DescentSIMDLookup
open DescentChosenRouter DescentResetAttachments DescentRelativeContacts DescentRosterOrder DescentTreePrefixIntervals
open DescentPacking.PackedMatch.Local DescentIssuedFallbackPanel
open ResetInput.SourceFrame DescentDenseHostOrder DescentCommonHost DescentPackedZip
open DescentActorRaster.CPU Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
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

local notation "peer" => PackedFlow.portAt A ((A).numberedHeader sourceDigits input.vertex).site
local notation "hw" => DescentCommonPalette.rotor reset.reset.graph
local notation "Y" => 2^reset.reset.n
local notation "Shape" => Node Unit (Unit×DescentContacts.Endpoint Y) (hw).Site
local notation "lev" => levelAt reset.frame f peer
local notation "op" => opcode (width-cc)
variable {nbits t a : ℕ}
local notation "stencil" => realPanel (reset:=reset) rfl reset.frame.basis nbits t

include accepted in
theorem actor_cell (level : width-cc<2^nbits) (one : 1<2^nbits)
    (capacity : 2^(width-cc)*full<2^nbits) (shapeRoom : 2*DescentFallbackShapeTable.rows (width-cc) Y≤2^t)
    (positive : 0<full) (quota : 0<K) (degPos : 0<32*Nat.clog 2 (2*(A).degree))
    (v : input.V) (hi : Block cc) (q : Shape) (fit : lev v q+1<2^a) :
    gate (width-cc) t a (op q) (encode t (2^(width-cc)) (stencil v hi)) (lev v q+1:ℕ)=
    if reset.reset.emits reset.terminals (recover reset.reset.graph (reset.frame.host v) q) hi then 1 else 0 := by
  have read:=accepted.stencil_cell rfl reset.frame.basis HEq.rfl level one capacity shapeRoom positive quota degPos v hi
  exact issued_bit reset.frame (input.vertex.trans Fin.valEmbedding) (A).mutual reset.reset.n f full (A).wire K
    (A).degree ((A).resetLoad sourceDigits) (fun u z j=>((A).resetFlow sourceDigits u z j:ℝ)) (old_roster (reset:=reset))
    peer (PackedFlow.actual_ports A _ symNear) v hi q (stencil v hi) (by simpa [originalCell] using read) fit

variable {Q H M w : ℕ} (qs : Fin Q → Node Unit (Unit×DescentContacts.Endpoint (2^reset.reset.n)) (DescentCommonPalette.rotor reset.reset.graph).Site) (rack : Fin H→Option input.V)
local notation "zeroes" => fun _ : Fin (2^(width-cc))=>(0:Cell t)
def realWords (h : Fin H) (hi : Block cc) :=
  encode t (2^(width-cc)) ((rack h).elim zeroes (fun v=>stencil v hi))

def realHeader (j : Fin Q) (h : Fin H) (_ : Block cc) : Cell a :=
  ((rack h).elim 0 (fun v=>lev v (qs j)+1):ℕ)

def realActor (j : Fin Q) (h : Fin H) (hi : Block cc) : Cell 1 :=
  (rack h).elim 0 fun v=>if reset.reset.emits reset.terminals (recover reset.reset.graph (reset.frame.host v) (qs j)) hi then 1 else 0

include accepted in
/-- Inputs are the previous header field and original low-window stencil words.
The first input may contain arbitrary data at a padded previous rack. -/
theorem issue_actors (level : width-cc<2^nbits) (one : 1<2^nbits)
    (capacity : 2^(width-cc)*full<2^nbits) (shapeRoom : 2*DescentFallbackShapeTable.rows (width-cc) Y≤2^t)
    (positive : 0<full) (quota : 0<K) (degPos : 0<32*Nat.clog 2 (2*(A).degree))
    (qs : Fin Q → Shape) (rack : Fin H → Option input.V)
    (tabs : Fin Q→Tables) (st : Expr) (heads : Fin Q→Expr) (base : ℕ) (m : Memory w)
    (words : Fin H→Block cc→Cell (t*2^(width-cc)))
    (live : ∀h v,rack h=some v→∀hi,words h hi=encode t (2^(width-cc)) (stencil v hi))
    (limit : ∀j v,lev v (qs j)+1<2^a)
    (fit : ∀j,Fits (tabs j) st (heads j) (t*2^(width-cc)) a M base w)
    (room : base+Q*(H*chunks (2^cc) M)<2^w)
    (fixed : ∀j,Static (tabs j) (gate (width-cc) t a (op (qs j))) M m)
    (input : Source st words M m) (header : ∀j,Source (heads j) (realHeader (reset:=reset) (a:=a) qs rack j) M m) :
    let p:=passes tabs st heads base H (2^cc) M
    let out:=ProtocolRAM.result p m
    (ProtocolRAM.program w p).Exec m out (clock p) ∧
      (∀j(pos : Row H (2^cc) M),out (base+j.val*(H*chunks (2^cc) M)+(row H (2^cc) M pos).val)=
        ((data (realActor (reset:=reset) qs rack j) pos).val:Word w)) ∧
      (∀z,z<base ∨ base+Q*(H*chunks (2^cc) M)≤z → out z=m z) ∧ CheapCode (ProtocolRAM.program w p) := by
  have calcBits (j : Fin Q) (h : Fin H) (hi : Block cc) :
      gate (width-cc) t a (op (qs j)) (words h hi) (realHeader qs rack j h hi)=realActor qs rack j h hi:=by
    cases known : rack h with
    | none=>simp [realHeader,realActor,known,absent]
    | some v=>
      rw [live h v known]
      simp only [realHeader,realActor,known,Option.elim_some]
      exact actor_cell accepted level one capacity shapeRoom positive quota degPos v hi (qs j) (limit j v)
  obtain ⟨ran,read,frame,cheap⟩:=DescentActorRaster.CPU.run tabs st heads base m (fun s=>op (qs s)) words
    (realHeader (reset:=reset) (a:=a) qs rack) fit room fixed input header
  exact ⟨ran,fun j y=>by simpa only [calcBits] using read j y,frame,cheap⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
