import OAI.Hierarchy.DescentResetTrunkGather
import OAI.Hierarchy.DescentResetTrunkResident
import OAI.Hierarchy.DescentResetStemIssuedWindows

namespace OAI
/-! # The trunk reads the incoming stem panel at the paired physical host -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)


open DescentPackedZip DescentSIMDLookup DescentIssuedFallbackPanel DescentResetFieldAssembler
open DescentResetTrunkIssue DescentSixParty.Chronology ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure

local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "rank_" => (Z).rawHostRank T vertexCode
local notation "radius" => (Z).k-(T).commonDepth
local notation "depth_" => GroupStage.depthBound D n f g
local notation "pitch" => Fintype.card input.V*(DescentDenseHostOrder.roster (Z).graph radius depth_).card
local notation "relay" => DescentResetTrunkPalette.pointer (H:=Fintype.card input.V) (Z).graph radius depth_ true
local notation "groups" => S.groupCount (i+1)
local notation "cap" => input.placement.cap
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "slots" => Fin L×Fin (2*cap)
local notation "Q" => DescentResetStemPackedIssue.count L cap
local notation "stemOrd" => DescentResetStemPackedIssue.ordinal L cap
variable {M b Wd : ℕ}

def incomingBank (rows out : ℕ) (x : Fin (2^k)) (j : Fin (L*(2*cap))) : Bank :=
  let addr:=finProdFinEquiv (x,stemOrd (true,finProdFinEquiv.symm j))
  ⟨out+addr.val*rows,Nat.clog 2 rows⟩

def incomingWord {Hn : ℕ} (rack : Fin Hn→Option B.next.V) (b : ℕ) (x : Fin (2^k)) (p : slots)
    (h₀ : Fin Hn) (g₀ : Fin groups) : Cell (b*7) :=
  (rack h₀).elim 0 fun v=>
    let u:=((g₀,v),x)
    DescentResetFieldAssembler.raw b («meta» B u (localOrigin B u (stemIndex B true p)))

theorem incoming_candidate_index (j : Fin (L*(2*cap))) :
    stemIndex B true (finProdFinEquiv.symm j)=incomingCandidate B j := by
  apply Fin.ext
  simp only [stemIndex,incomingCandidate,Fin.val_castLE,Equiv.apply_symm_apply]
  rfl

theorem trunk_gather_value (rack : Fin pitch→Option B.next.V)
    (present : ∀v,rack (rank_ v)=some v) (named : ∀h₀ v,rack h₀=some v → rank_ v=h₀)
    (x : Fin (2^k)) (j : Fin (L*(2*cap))) (h₀ : Fin pitch) (g₀ : Fin groups) :
    (relay h₀).elim 0 (fun d₀=>incomingWord B rack b x (finProdFinEquiv.symm j) d₀ g₀)=
      DescentResetFieldAssembler.raw b ((rack h₀).elim .blank (fun t=>hostStem B ((g₀,t),x) j)) := by
  cases here : rack h₀ with
  | some v=>
    have seen:=named h₀ v here
    subst h₀
    rw [trunk_pointer B v true]
    cases shapeAt : trunkLabels B v with
    | none=>simp [shapeAt,hostStem,zero_raw]
    | some p=>
      simp [shapeAt,hostStem,incomingWord]
      rw [present p.right]
      change DescentResetFieldAssembler.raw b («meta» B ((g₀,p.right),x)
        (localOrigin B ((g₀,p.right),x) (stemIndex B true (finProdFinEquiv.symm j)))) = _
      rw [incoming_candidate_index B j]
      rfl
  | none=>
    cases ptr : relay h₀ with
    | none=>simp [zero_raw]
    | some y=>
      cases target : rack y with
      | none=>simp [incomingWord,target,zero_raw]
      | some v=>
        have same:=named y v target
        have hit : relay h₀=some (rank_ v):=ptr.trans (congrArg some same.symm)
        obtain ⟨u,hu⟩:=trunk_alias_resident B h₀ v hit
        have yes:=present u
        rw [hu,here] at yes
        cases yes

/-- The previous native stem program emits an outer block index, a signed stem
ordinal, and the packed host/group row in that order. The public right-relay
directory preserves both the low block and its SIMD group lane. -/
theorem trunk_gathered_at (rack : Fin pitch→Option B.next.V)
    (present : ∀v,rack (rank_ v)=some v) (named : ∀h₀ v,rack h₀=some v → rank_ v=h₀)
    (base out : ℕ) (m : Memory Wd)
    (early : out+(2^k*Q)*(pitch*chunks groups M)≤base)
    (room : base+DescentDyadicSpan.span (pitch*chunks groups M)<2^Wd)
    (emitted : ∀(x : Fin (2^k)) (p : slots) (r₀ : Row pitch groups M),
      m (out+(finProdFinEquiv (x,stemOrd (true,p))).val*(pitch*chunks groups M)+(row pitch groups M r₀).val)=
        ((data (incomingWord B rack b x p) r₀).val:Word Wd)) :
    let n₀:=pitch*chunks groups M
    let phase:=DescentResetTrunkGather.phase Wd base groups M relay
    phase.Runs m ∧ (∀a,a<base ∨ base+n₀≤a→phase.image m a=m a) ∧
      ∀(x : Fin (2^k)) (j : Fin (L*(2*cap))),
        let scan:=DescentResetTrunkGather.issue n₀ base (incomingBank B n₀ out x j)
        scan.Fits Wd (base+DescentDyadicSpan.span n₀) ∧
        Source scan (fun h₀ g₀=>DescentResetFieldAssembler.raw b ((rack h₀).elim .blank (fun t=>hostStem B ((g₀,t),x) j))) M (phase.image m) := by
  intro n₀ phase
  have exe:=DescentResetTrunkGather.run_at (M:=M) (G:=groups) (b:=b*7) relay base m room
  refine ⟨exe.1,exe.2.1,?_⟩
  intro x j
  let bank:=incomingBank B n₀ out x j
  let p : slots:=finProdFinEquiv.symm j
  let idx:=finProdFinEquiv (x,stemOrd (true,p))
  have where_ : out+idx.val*n₀≤base:=(Nat.add_le_add_left (Nat.mul_le_mul_right n₀ idx.isLt.le) out).trans early
  have endRows : bank.base+n₀≤base:=by
    change out+idx.val*n₀+n₀≤base
    rw [Nat.add_assoc,←Nat.succ_mul]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right n₀ idx.isLt) out).trans early
  have low : bank.base+bank.size≤base+DescentDyadicSpan.span n₀:=Nat.add_le_add_right where_ _
  have fit : bank.Fits Wd (base+DescentDyadicSpan.span n₀):=⟨Nat.two_pow_pos _,
    (Nat.le_add_left ..).trans_lt (low.trans_lt room),low⟩
  have got:=exe.2.2 bank (incomingWord B rack b x p) fit endRows (DescentDyadicSpan.span_ge n₀) (emitted x p)
  refine ⟨got.1,?_⟩
  have result:=got.2
  rwa [show (fun h₀ g₀=>(relay h₀).elim 0 (fun v=>incomingWord B rack b x p v g₀))=
      (fun h₀ g₀=>DescentResetFieldAssembler.raw b ((rack h₀).elim .blank (fun t=>hostStem B ((g₀,t),x) j))) from
    funext (fun h₀=>funext (trunk_gather_value B rack present named x j h₀))] at result

theorem trunk_gathered (rack : Fin pitch→Option B.next.V)
    (present : ∀v,rack (rank_ v)=some v) (named : ∀h₀ v,rack h₀=some v → rank_ v=h₀)
    (base out : ℕ) (m : Memory Wd)
    (early : out+(2^k*Q)*(pitch*chunks groups M)+DescentDyadicSpan.span (pitch*chunks groups M)≤base)
    (room : base+DescentDyadicSpan.span (pitch*chunks groups M)<2^Wd)
    (emitted : ∀(x : Fin (2^k)) (p : slots) (r₀ : Row pitch groups M),
      m (out+(finProdFinEquiv (x,stemOrd (true,p))).val*(pitch*chunks groups M)+(row pitch groups M r₀).val)=
        ((data (incomingWord B rack b x p) r₀).val:Word Wd)) :
    let n₀:=pitch*chunks groups M
    let phase:=DescentResetTrunkGather.phase Wd base groups M relay
    phase.Runs m ∧ (∀a,a<base ∨ base+n₀≤a→phase.image m a=m a) ∧
      ∀(x : Fin (2^k)) (j : Fin (L*(2*cap))),
        let scan:=DescentResetTrunkGather.issue n₀ base (incomingBank B n₀ out x j)
        scan.Fits Wd (base+DescentDyadicSpan.span n₀) ∧
        Source scan (fun h₀ g₀=>DescentResetFieldAssembler.raw b ((rack h₀).elim .blank (fun t=>hostStem B ((g₀,t),x) j))) M (phase.image m) := by
  exact trunk_gathered_at B rack present named base out m ((Nat.le_add_right ..).trans early) room emitted

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
