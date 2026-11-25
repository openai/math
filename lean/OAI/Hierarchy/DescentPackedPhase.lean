import OAI.Hierarchy.DescentColonyDynamicSplit
import OAI.Hierarchy.DescentCensusLaneNumbers
import OAI.Hierarchy.DescentPackedAllSeeds
import OAI.Hierarchy.DescentPackedColonyWinner
import OAI.Hierarchy.DescentPackedWinnerRAM
import OAI.Hierarchy.DescentPackedStageChoices

namespace OAI
/-! # One finite native ordinary-stage chooser, including both first minima -/

namespace Hierarchy.DescentPackedColony.Phase
open DescentColonies DescentGL DescentSIMDLookup DescentAffineColors DescentBinaryField
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {ℓ Δ G k b M w : ℕ}
local notation "q" => (2^k-1)
local notation "s" => (1+k*2^k)
local notation "r" => (2^(k+1))

/-- Every word and every instruction is fixed before the source instance is evaluated. -/
structure Shelves (k Δ : ℕ) where
  layers : Fin (2^k-1)→Layout Δ
  split : DescentPackedMinimum.Layout (2^k-1)
  color : DescentPackedMinimum.Layout (2^(k+1))
  amount : Bank
  zip : Fin (2^k-1)→DescentPackedZip.Tables
  selected : ℕ
  paintTable : ℕ
  output : ℕ
  first : ℕ

def Shelves.mu (L : Shelves k Δ) := L.split.result+(q-1)
def Shelves.paint (L : Shelves k Δ) := L.color.result+(r-1)
def Shelves.panels (L : Shelves k Δ) (i : Fin q) := (L.layers i).source k
def Shelves.field (L : Shelves k Δ) := chosen L.mu L.panels L.amount L.zip

/-- One common short field accommodates every two-input ROM as well as the
output digits. Its denominator is shared across all five scheduled phases. -/

def program (L : Shelves k Δ) (w H G M : ℕ) : Procedure w :=
  let a:=AllSeeds.search w H G M k L.layers
  let z:=scan w L.selected (H*chunks G M) L.field
  let d:=PackedWinnerRAM.program k w L.paintTable L.output H G M L.mu L.paint L.panels
  ((((a.text.seq (DescentPackedMinimum.search L.split w H G M)).seq z).seq
    (DescentPackedMinimum.search L.color w H G M)).seq d.text)

def cost (L : Shelves k Δ) (w H G M : ℕ) :=
  let a:=AllSeeds.search w H G M k L.layers
  let z:=4+H*chunks G M*(2*(1+33*q)+4)
  let d:=PackedWinnerRAM.program k w L.paintTable L.output H G M L.mu L.paint L.panels
  (((a.ticks+PackedChoices.ticks L.split H G M)+z)+PackedChoices.ticks L.color H G M)+d.ticks

structure Space (L : Shelves k Δ) (w H G b M : ℕ) : Prop where
  trials : AllSeeds.ArrayRoom L.layers L.first H G k b M w
  split : DescentPackedMinimum.Fits L.split w s M H G
  splitPanel : ∀i,L.split.source i=L.panels i
  trialsStop : ∀i (d : ℕ),d<k→((L.layers i).source (d+1)).base+H*chunks G M≤L.split.work
  previous : L.first≤L.split.work
  splitRom : ∀i,(L.split.dictionary i).base+(L.split.dictionary i).size≤L.first
  countLow : L.amount.base+H*chunks G M≤L.first
  countRoom : H*chunks G M≤L.amount.size
  countFit : L.amount.Fits w L.selected
  zipLow : ∀i,(L.zip i).shift.base+2^(s*M)≤L.first ∧ (L.zip i).apply.base+2^((s+b*2^k)*M)≤L.first
  zipRoom : ∀i,WordRoom (L.zip i) s (b*2^k) M w L.selected
  zipKey : (⟨L.mu,0⟩:Bank).Fits w L.selected
  zipAbove : L.split.work≤L.selected
  zipEnd : L.selected+H*chunks G M<2^w
  color : DescentPackedMinimum.Fits L.color w (PackedContribution.width k b) M H G
  colorPanel : ∀j,(L.color.source j).base=L.selected
  colorRom : ∀j,(L.color.dictionary j).base+(L.color.dictionary j).size≤L.first
  afterZip : L.selected+H*chunks G M≤L.color.work
  final : PackedWinnerRAM.Fits k w L.paintTable L.output H G M L.mu L.paint L.panels
  paintRom : L.paintTable+PackedWinnerRAM.tableWords k M≤L.first

local notation "hostCount" => (2^ℓ)

/-- Each premise names an original low packed source word or fixed ROM word. -/
structure Initial (L : Shelves k Δ) (hk : 0<k) (rs : DynamicSplit.Roster ℓ Δ)
    (W amt : Fin G→Fin hostCount→Block k→ℕ) (D cap b M : ℕ) (m : Memory w) : Prop where
  graph : ∀i,Input (L.layers i) rs W D cap b M (modulus hk) (seedAt k i).val m
  amounts : Reads L.amount (fun v g=>counts b (amt g v)) M m
  zip : ∀i,DescentPackedZip.Static (L.zip i) (affine (b:=b) (modulus hk) (seedAt k i).val) M m
  split : ∀i (key : Cell (s*M)),m ((L.split.dictionary i).base+key.val)=(DescentPackedScore.chunkScore (@PackedSplit.value k) key:Word w)
  color : ∀j (key : Cell (PackedContribution.width k b*M)),m ((L.color.dictionary j).base+key.val)=
    (DescentPackedScore.chunkScore (@PackedContribution.value k b j) key:Word w)
  names : ∀(x : Block k) (i : Fin q) (j : Candidate k) (key : Cell (s*M)),
    m ((PackedWinnerRAM.bank L.paintTable M x i j).base+key.val)=
      ((table (M:=M) (PackedWinnerKey.value hk i j x) key).val:Word w)

private theorem incoming_eq (rs : DynamicSplit.Roster ℓ Δ) :
    incoming (peers rs)=DynamicSplit.incoming rs := by
  funext v
  simp [incoming,peers,slots,DynamicSplit.incoming,List.map_ofFn]

private theorem dict_low {X : Bank} {width z : ℕ} (bits : X.bits=width)
    (below : X.base+X.size≤z) (i : Cell width) : X.base+i.val<z := by
  have small : i.val<X.size := by simpa only [Bank.size,bits] using i.isLt
  omega

/-- The final memory retains both exact first-minimum words and the physical
per-block matching data computed using those two particular winners. -/
theorem execute (L : Shelves k Δ) (space : Space L w hostCount G b M) (hk : 0<k) (hm : 0<M)
    (rs : DynamicSplit.Roster ℓ Δ) (W amt : Fin G→Fin hostCount→Block k→ℕ) (D cap : ℕ)
    (small : ∀g v x,W g v x<2^b) (outgoing : ∀g v x,amt g v x<2^b)
    (scoreRoom : G*hostCount*2^k<2^w) (massRoom : (∑g,∑v,∑x,amt g v x)<2^w)
    (m : Memory w) (init : Initial L hk rs W amt D cap b M m) :
    let inc:=DynamicSplit.incoming rs
    let Q:=uniformColonyScore inc W D cap (modulus hk)
    ∃out : Memory w,∃i : Fin q,∃j : Candidate k,
      (program L w hostCount G M).Exec m out (cost L w hostCount G M) ∧
      (scanMinimum Q (nonzeroWords k)).1=some (seedAt k i,Q (seedAt k i)) ∧
      (scanMinimum (scoreAt (GroupedScan.groupedSlabs inc W amt D cap (modulus hk) (seedAt k i))) (List.range r)).1=
        some (j.val,score (GroupedScan.groupedSlabs inc W amt D cap (modulus hk) (seedAt k i)) j) ∧
      out L.mu=(i.val:Word w) ∧ out L.paint=(j.val:Word w) ∧ (∀u<L.first,out u=m u) ∧
      (∀u,L.output+2^k*(hostCount*chunks G M)≤u→ out u=m u) ∧
      ∀(x : Block k) (p : Row hostCount G M),out (PackedWinnerRAM.slot L.output (hostCount*chunks G M) x+(row hostCount G M p).val)=
        ((data (fun v g=>PackedWinnerKey.value hk i j x (PackedSplit.state inc W D cap (modulus hk) (seedAt k i) v g)) p).val:Word w) := by
  let inc:=DynamicSplit.incoming rs
  let panel:=fun i=>PackedSplit.state inc W D cap (modulus hk) (seedAt k i)
  let src:= (AllSeeds.search w hostCount G M k L.layers).after m
  obtain ⟨all,initial,results⟩:=AllSeeds.published L.layers space.trials rs W D cap (modulus hk) (seedAt k) small m init.graph
  rw [incoming_eq rs] at results
  have si (i) : DescentPackedScore.Input (M:=M) (L.split.source i) (L.split.dictionary i) PackedSplit.value (panel i) src :=
    ⟨by rw [space.splitPanel];exact results i,fun t=>(initial _ (dict_low (space.split.fields i) (space.splitRom i) t)).trans (init.split i t)⟩
  obtain ⟨m1,i,run1,read1,mu,_,frame1,high1⟩:=PackedChoices.seed inc W D cap hk L.split space.split hm scoreRoom src si
  have low1 (z) (hz:z<L.first) : m1 z=m z := (frame1 z (hz.trans_le space.previous)).trans (initial z hz)
  have srcBound (i) : (L.panels i).Fits w L.split.work := (space.splitPanel i) ▸ space.split.source i
  have capRows (i) : hostCount*chunks G M≤(L.panels i).size := (space.splitPanel i) ▸ space.split.rows i
  have srcFit (i) : (L.panels i).Fits w L.selected := ⟨(srcBound i).1,(srcBound i).2.1,(srcBound i).2.2.trans space.zipAbove⟩
  have panels (i) (p : Row hostCount G M) : m1 ((L.panels i).base+(row hostCount G M p).val)=((data (panel i) p).val:Word w) :=
    (frame1 _ (by have :=(srcBound i).2.2;have :=(row hostCount G M p).isLt.trans_le (capRows i);omega)).trans (results i p)
  have keyFit : q≤2^w := (Nat.sub_le _ _).trans ((Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_succ k)).trans space.final.codes)
  let n:=hostCount*chunks G M
  let m2:=ProtocolRAM.image L.selected n L.field m1
  have zipExec : (scan w L.selected n L.field).Exec m1 m2 (4+n*(2*L.field.work+4)) :=
    @scan_exec w L.selected n L.field m1
      (chosen_fits L.mu L.selected L.panels L.amount L.zip space.zipKey srcFit space.countFit space.zipRoom) space.zipEnd
  have stored := chosen_read L.mu L.panels L.amount L.zip L.selected space.zipRoom (fun i=>⟨srcFit i,capRows i⟩)
    space.countFit space.countRoom keyFit inc W amt D cap (modulus hk) (seedAt k) outgoing m1 i read1
    (fun p=>(low1 _ (by have :=space.countLow;have :=(row hostCount G M p).isLt;omega)).trans (init.amounts p))
    panels (fun i=>static_congr _ _ m m1 L.first low1 (space.zipLow i).1 (space.zipLow i).2 (init.zip i))
  have zipLow (z) (hz:z<L.selected) : m2 z=m1 z := ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl hz)
  have first2 (z) (hz:z<L.first) : m2 z=m z := (zipLow z ((hz.trans_le space.previous).trans_le space.zipAbove)).trans (low1 z hz)
  let selected :=fun v g=>PackedContribution.actual b inc W amt D cap (modulus hk) (seedAt k i) g v
  have ci (j : Candidate k) : DescentPackedScore.Input (M:=M) (L.color.source j) (L.color.dictionary j) (PackedContribution.value j)
      selected m2 :=
    ⟨fun p=>by rw [space.colorPanel];exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row hostCount G M p)).trans (stored p),
      fun t=>(first2 _ (dict_low (space.color.fields j) (space.colorRom j) t)).trans (init.color j t)⟩
  obtain ⟨m3,j,run2,read2,paint,frame2,high2⟩:=PackedChoices.affine inc W amt D cap hk (seedAt k i) L.color space.color hm massRoom outgoing m2 ci
  have selectedLow : L.selected≤L.color.work := (Nat.le_add_right ..).trans space.afterZip
  have step3 (z) (hz:z<L.selected) : m3 z=m1 z := (frame2 z (hz.trans_le selectedLow)).trans (zipLow z hz)
  have first3 (z) (hz:z<L.first) : m3 z=m z := (step3 z ((hz.trans_le space.previous).trans_le space.zipAbove)).trans (low1 z hz)
  have k1 : L.mu<L.selected := by have bound:=space.zipKey.2.2;change L.mu+1≤L.selected at bound;omega
  have finalSeed := (step3 L.mu k1).trans read1
  have done : PackedWinnerRAM.Ready (lo:=L.paintTable) (seed:=L.mu) (paint:=L.paint) (source:=L.panels) (M:=M) hk i j (panel i) m3 :=
    ⟨finalSeed,read2,fun p=>(step3 _ (by have :=(srcFit i).2.2;have :=(row hostCount G M p).isLt.trans_le (capRows i);omega)).trans (panels i p),
      fun x ii jj t=>(first3 _ (PackedWinnerRAM.entry_low space.paintRom x ii jj t)).trans (init.names x ii jj t)⟩
  let lastStep:=PackedWinnerRAM.program k w L.paintTable L.output hostCount G M L.mu L.paint L.panels
  have named : lastStep.text.Exec m3 (lastStep.after m3) lastStep.ticks := PackedWinnerRAM.exec space.final m3
  have finish := PackedWinnerRAM.frame (lo:=L.paintTable) (out:=L.output) (seed:=L.mu) (paint:=L.paint) (source:=L.panels) (M:=M) (G:=G) (H:=hostCount) m3
  have outputLow : L.first≤L.output := by
    have e₁:=space.previous
    have e₂:=space.zipAbove
    have e₃:=space.color.workspace
    have e₄:=space.color.ledger.2.2
    have e₅:=space.final.paint
    dsimp only [Shelves.paint] at e₅
    omega
  have passed : L.split.result+q≤L.selected := by
    have key:=space.zipKey.2.2;change L.split.result+(q-1)+1≤L.selected at key;omega
  have colorEnd : L.color.result+r≤L.output := by have key:=space.final.paint;change L.color.result+(r-1)<L.output at key;omega
  have upper (z : ℕ) (hz:L.output+2^k*n≤z) : lastStep.after m3 z=m z := by
    have post:=space.color.workspace
    have ord:=space.color.ledger.2.2
    have span:=space.afterZip
    have seedWork:=space.zipAbove
    have afterZip:L.selected+n≤z := by omega
    have old:=AllSeeds.frame_above L.layers m (fun i d hd=>(space.trialsStop i d hd).trans (by omega : L.split.work≤z))
    exact (PackedWinnerRAM.frame_above (lo:=L.paintTable) (out:=L.output) (seed:=L.mu) (paint:=L.paint) (source:=L.panels)
      (M:=M) (G:=G) (H:=hostCount) m3 z hz).trans ((high2 z (by omega)).trans
        ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inr afterZip)).trans ((high1 z (by omega)).trans old)))
  refine ⟨lastStep.after m3,i,j,?_,mu,paint,(finish _ space.final.seed).trans finalSeed,(finish _ space.final.paint).trans read2,
    fun z hz=>(finish _ (hz.trans_le outputLow)).trans (first3 z hz),upper,PackedWinnerRAM.published space.final hk i j (panel i) m3 done⟩
  dsimp only [program,cost]
  rw [← chosen_work L.mu L.panels L.amount L.zip]
  exact Procedure.Exec.then
    (Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then all run1) zipExec) run2) named

end
end Hierarchy.DescentPackedColony.Phase

end OAI
