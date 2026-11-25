import OAI.Hierarchy.DescentRecordedCanvas
import OAI.Hierarchy.DescentReservationMount

namespace OAI
/-! # Column reservations read from the two attained depths and the first Walsh contact word -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentBaseVariance DescentWalshPrecision DescentPackedWalsh
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

open ProtocolRAM DescentReservationHeader DescentPlainTerminal.Suffix.Cutoff

namespace ClosedReset.Recorded
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p) (E : EstimatorArena)
local notation "A" => input.placement
local notation "K" => quota S.rounds
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i
local notation "owners" => Fintype.card input.V
local notation "full" => (A).wire*((A).z*G.b)*(A).cap


theorem cast_inputs {F₁ P₁ J V : Type} [Field F₁] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d₁ k₁ a b : ℕ} {bw : P₁→ℕ} {W₁ : MarkedWorld F₁ d₁ P₁ bw} {G₁ : PoweredGadget F₁} {q₁ ε₁ : ℝ}
    (A₁ : GroupStage W₁ G₁ q₁ ε₁ J V k₁) (same : a=b) (digits : Block b≃J×Block k₁)
    (vertex : V↪Fin (Fintype.card V)) (f₁ : ℕ) (v u : V) :
    let new:=(Equiv.cast (congrArg Block same)).trans digits
    let name:=(A₁.numberedHeader new vertex).site
    (A₁.mixerHeader new name).depth A₁ f₁ v=(A₁.numberedHeader digits vertex).depth A₁ f₁ v ∧
      (∑x,A₁.resetFlow new v u x)=∑x,A₁.resetFlow digits v u x := by
  subst a
  exact ⟨rfl,rfl⟩

def firstContactBank (E : EstimatorArena) : Bank :=
  ⟨location E.start E.hosts E.high E.dim,Nat.clog 2 (E.hosts*2^E.high)⟩

def attainedDepth (E : EstimatorArena) (j : ℕ) : Expr := .lookup E.depthRows (.lit (j*(E.dim+1)))

include accepted in
theorem attainedDepth_read {w ceiling : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w)
    (depths :
      let digits:=(Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name:=((A).numberedHeader digits input.vertex).site
      ∀v,mem (E.depthRows.base+(name v).val*(E.dim+1))=(((A).mixerHeader digits name).depth A f v:Word w))
    (legal : E.depthRows.Fits w ceiling) (room : ∀v,(input.vertex v).val*(E.dim+1)<E.depthRows.size)
    (v : input.V) (tick : Word w) :
    (attainedDepth E (input.vertex v).val).eval mem tick=(reset.reset.placement.b (reset.frame.host v):Word w) := by
  let moved:=cast_inputs A (dim.trans reset.keyWidth) sourceDigits input.vertex f v v
  change E.depthRows.read mem (((input.vertex v).val*(E.dim+1):ℕ):Word w)=_
  rw [DescentPackedZip.bank_read E.depthRows mem (room v) legal]
  exact (depths v).trans (congrArg (fun z : ℕ=>(z:Word w)) (moved.1.trans (accepted.measured.depth v).symm))

include accepted in
theorem reservation_word {w ceiling : ℕ} (dim : E.dim=reset.reset.k) (maxPorts : ℕ) (ports : D≤ maxPorts)
    (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts)) (mem : Memory w)
    (first : E.FirstTotals (publicLoad E dim maxPorts ports hostCount) mem) (e : Contacts (A).mutual)
    (depths :
      let digits:=(Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name:=((A).numberedHeader digits input.vertex).site
      ∀v,mem (E.depthRows.base+(name v).val*(E.dim+1))=(((A).mixerHeader digits name).depth A f v:Word w))
    (depthLegal : E.depthRows.Fits w ceiling) (depthRoom : ∀v,(input.vertex v).val*(E.dim+1)<E.depthRows.size)
    (bankLegal : (firstContactBank E).Fits w ceiling) (wordBits : E.precision≤w)
    (base levels total : ℕ) (maxDepth : max (reset.reset.placement.b (reset.frame.host e.1))
      (reset.reset.placement.b (reset.frame.host e.2.val))<2^levels)
    (sumFits : (∑x,(A).resetFlow sourceDigits e.1 e.2.val x)<2^total)
    (widthBits : levels+total≤w) (output : n<w) (hw : 0<wire) (hK : 0<K) (positive : 0<wire*(z*G.b)*(A).cap)
    (static : DescentReservationHeader.Resident base levels total K (2^f*(wire*(z*G.b)*(A).cap)) (2^n) mem) (tick : Word w) :
    let c:=contactRow E dim maxPorts ports hostCount e
    let idx:=Expr.lit (DescentPackedWalsh.row c (fun _ : Fin E.high=>false)).val
    let lhs:=attainedDepth E (input.vertex e.1).val
    let rhs:=attainedDepth E (input.vertex e.2.val).val
    ((term base levels total lhs rhs (firstTotal (firstContactBank E) idx E.precision)).eval mem tick).val=
      min (2^n) (reset.terminals.columns.size (reset.frame.host e.1) (reset.frame.host e.2.val)) := by
  let digits:=(Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
  let name:=((A).numberedHeader digits input.vertex).site
  let c:=contactRow E dim maxPorts ports hostCount e
  let atRow:=Expr.lit (DescentPackedWalsh.row c (fun _ : Fin E.high=>false)).val
  let depth:=fun v=>reset.reset.placement.b (reset.frame.host v)
  have moved (v u : input.V):=
    cast_inputs A (dim.trans reset.keyWidth) sourceDigits input.vertex f v u
  have actualDepth (v : input.V) : (attainedDepth E (input.vertex v).val).eval mem tick=(depth v:Word w) := by
    change E.depthRows.read mem (((input.vertex v).val*(E.dim+1):ℕ):Word w)=_
    rw [DescentPackedZip.bank_read E.depthRows mem (depthRoom v) depthLegal]
    change mem (E.depthRows.base+(name v).val*(E.dim+1))=_
    rw [depths v,(moved v v).1,←accepted.measured.depth v]
  have measured:=contact_total E dim maxPorts ports hostCount mem first e
  have fitSum : (∑x,(A).resetFlow digits e.1 e.2.val x)<2^total:=(moved e.1 e.2.val).2.symm ▸ sumFits
  have native:=from_first (u:=E.high) (l:=E.low) (firstContactBank E) atRow (attainedDepth E (input.vertex e.1).val)
    (attainedDepth E (input.vertex e.2.val).val) mem tick c bankLegal (Nat.le_pow_clog (by decide : 1<2) _)
    wordBits rfl ((A).resetFlow digits e.1 e.2.val) measured base levels total K (2^f*(wire*(z*G.b)*(A).cap))
    n (depth e.1) (depth e.2.val) (actualDepth e.1) (actualDepth e.2.val) maxDepth fitSum widthBits output static
  have sum_eq : (∑x,(A).resetFlow digits e.1 e.2.val x) = ∑x,(A).resetFlow sourceDigits e.1 e.2.val x := (moved e.1 e.2.val).2
  apply native.trans
  apply (congrArg (fun mass => DescentReservationHeader.width K (2^f*(wire*(z*G.b)*(A).cap)) (max (depth e.1) (depth e.2.val)) mass (2^n)) sum_eq).trans
  apply physical_width (u:=S.groupWidth k tail i) (l:=k) (Δ:=(A).degree) reset.frame (input.vertex.trans Fin.valEmbedding)
    (A).mutual n f (wire*(z*G.b)*(A).cap) wire K ((A).resetFlow sourceDigits) ((A).resetLoad sourceDigits) _ hw hK positive
  convert reset.roster using 1
  funext v u j
  simp only [GroupStage.resetFlow,input.edges,input.grain]
  exact congrArg (fun cnt => (pairLoad (W.countWorld cnt) (fun v => ((A).pos v).2)
    (StarKeys.filled W.graph (A).pos (A).block sourceDigits) (wire*(z*G.b)) v u j : ℝ)) reset.count_eq.symm

/-- Installing the common reservation table above the two reached input banks preserves
    all physical first contact totals and the attained depths in the same execution. -/
theorem prepare_reservations {w : ℕ} (dim : E.dim=reset.reset.k) (maxPorts : ℕ) (ports : D≤ maxPorts)
    (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts)) (mem : Memory w)
    (first : E.FirstTotals (publicLoad E dim maxPorts ports hostCount) mem)
    (depths :
      let digits:=(Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name:=((A).numberedHeader digits input.vertex).site
      ∀v,mem (E.depthRows.base+(name v).val*(E.dim+1))=(((A).mixerHeader digits name).depth A f v:Word w))
    (base levels total : ℕ) (legal : finish base levels total<2^w)
    (firstEnd : location E.start E.hosts E.high E.dim+E.hosts*2^E.high≤base)
    (depthEnd : E.depthRows.base+E.depthRows.size≤base)
    (depthRoom : ∀v,(input.vertex v).val*(E.dim+1)<E.depthRows.size) :
    let scale:=2^f*(wire*(z*G.b)*(A).cap)
    let table:=DescentReservationHeader.literal (w:=w) base levels total K scale (2^n)
    let dst:=DescentReservationHeader.header base levels total K scale (2^n) mem
    table.program.Exec mem dst (4+10*(2^levels+2^(levels+total))) ∧
      DescentReservationHeader.Resident base levels total K scale (2^n) dst ∧
      E.FirstTotals (publicLoad E dim maxPorts ports hostCount) dst ∧
      (let digits:=(Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
       let name:=((A).numberedHeader digits input.vertex).site
       ∀v,dst (E.depthRows.base+(name v).val*(E.dim+1))=(((A).mixerHeader digits name).depth A f v:Word w)) ∧
      (∀a<base,dst a=mem a) := by
  obtain ⟨execute,res,saved,_,_⟩:=DescentReservationHeader.installed base levels total K
    (2^f*(wire*(z*G.b)*(A).cap)) (2^n) mem legal
  refine ⟨execute,res,?_,?_,fun a ha=>saved a (.inl ha)⟩
  · intro v
    have room:=(DescentPackedWalsh.row v (fun _ : Fin E.high=>false)).isLt
    rw [saved _ (.inl (by omega))]
    exact first v
  · intro digits name v
    have room:=depthRoom v
    rw [saved _ (.inl (by exact (Nat.add_lt_add_left room _).trans_le depthEnd))]
    exact depths v

end ClosedReset.Recorded
end
end Hierarchy.DescentSixParty

end OAI
