import OAI.Hierarchy.DescentColonyWinningColumns

namespace OAI
/-! # Materialized winning outgoing and split banks for every group and site -/

noncomputable section
namespace Hierarchy.DescentColonies.Materialized
open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM NativeBatch
open ThreeFlat.RAM PhysicalProcedure
open DescentGL (Bits Nonzero)
open scoped Fin.CommRing

variable {G H k w : ℕ}

def size (G H k : ℕ) := G*H*(k+1)
abbrev Slot (G H k : ℕ) := (Fin G×Fin H)×Option (Fin k)

def index (G H k : ℕ) : Slot G H k≃Fin (size G H k) :=
  (finProdFinEquiv.prodCongr (finSuccEquiv k).symm).trans finProdFinEquiv

def first (G H k base : ℕ) := AllSeedsRAM.winningBase G H k base+2^k
def endAt (G H k base : ℕ) := first G H k base+size G H k*2^k
def dest (base : ℕ) (s : Slot G H k) := first G H k base+((index G H k) s).val*2^k

def expr (base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) (s : Slot G H k) : Expr := match s.2 with
  | none => WinningColumns.outgoing G H k base (raw s.1.1 s.1.2) a
  | some d => WinningColumns.column base s.1.1 s.1.2 (some d)

def step (w base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) (i : Fin (size G H k)) : Code w :=
  let s := (index G H k).symm i
  let e := expr base raw a s
  ⟨scan w (dest base s) (2^k) e,ProtocolRAM.image (dest base s) (2^k) e,
    4+2^k*(2*e.work+4)⟩

def program (w base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) : Code w :=
  Code.seq (step w base raw a) _ le_rfl

/-- The dyadic slots of all trial runs end before the packed score gathering pass. -/
theorem old_end (base : ℕ) (i : Fin (2^k-1)) (g : Fin G) (v : Fin H) (d : Fin k) :
    AllSeedsRAM.retainedBank base i g v (some d)+2^k≤AllSeedsRAM.gatherBase G H k base := by
  have edge := AllSeedsRAM.retained_end base i g v (some d)
  have slots := AllSeedsRAM.mono G H k base (i.isLt.trans_le (Nat.sub_le _ _))
  change AllSeedsRAM.slot G H k base (i.val+1)≤AllSeedsRAM.slot G H k base (2^k) at slots
  have power := Nat.le_pow_clog (by decide : 1<2) ((2^k)*AllSeedsRAM.stride G H k)
  have inc := (AllSeedsRAM.next G H k base i.val).le
  exact edge.trans (Nat.le_of_lt (inc.trans (slots.trans (Nat.add_le_add_left power base))))

private theorem fits (base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) (s : Slot G H k)
    (old : ∀g v,raw g v+2^k≤base) (room : endAt G H k base<2^w) :
    (expr base raw a s).Fits w (first G H k base) := by
  have out : first G H k base<2^w := (Nat.le_add_right ..).trans_lt room
  have bits : 2^k<2^w := (Nat.le_add_left ..).trans_lt out
  have before : WinningColumns.winnerPtr G H k base<first G H k base := by
    dsimp [WinningColumns.winnerPtr,first]
    have := Nat.two_pow_pos k
    omega
  rcases s with ⟨⟨g,v⟩,(_|d)⟩
  · apply WinningColumns.outgoing_fits _ _ _ _ _ _ bits before
    exact (old g v).trans ((Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))
  · apply WinningColumns.column_fits _ _ _ _ _ bits before
    exact fun i=>(old_end base i g v d).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))

theorem dest_end (base : ℕ) (s : Slot G H k) : dest base s+2^k≤endAt G H k base := by
  have h := Nat.mul_le_mul_right (2^k) ((index G H k) s).isLt
  simpa only [dest,endAt,Nat.succ_mul,Nat.add_assoc] using Nat.add_le_add_left h (first G H k base)

theorem run (base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) (m : Memory w)
    (old : ∀g v,raw g v+2^k≤base) (room : endAt G H k base<2^w) :
    (program w base raw a).text.Exec m ((program w base raw a).after m) (program w base raw a).ticks := by
  have runAll : (program w base raw a).exec := by
    unfold program
    apply Code.exec_seqAll
    intro i M labels registers slots machine
    let s := (index G H k).symm i
    exact scan_exec (dest base s) (2^k) (expr base raw a s) M
      (ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (fits base raw a s old room))
      ((dest_end base s).trans_lt room) machine
  intro labels registers slots machine
  exact runAll m machine

theorem below (base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) (m : Memory w) (z : ℕ)
    (hz : z<first G H k base) : (program w base raw a).after m z=m z :=
  Code.frame_seq _ z (fun _i _M=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _
    (Or.inl (hz.trans_le (Nat.le_add_right ..)))) m _ _

theorem published_expr (base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) (m : Memory w)
    (old : ∀g v,raw g v+2^k≤base) (room : endAt G H k base<2^w) (s : Slot G H k) (x : Block k) :
    (program w base raw a).after m (dest base s+x.val)=(expr base raw a s).eval m (x.val:Word w) := by
  let jobs := step w base raw a
  let Init := fun M : Memory w=>∀j<first G H k base,M j=m j
  let Claim := fun i : Fin (size G H k)=>fun M : Memory w=>let z := (index G H k).symm i;
    M (dest base z+x.val)=(expr base raw a z).eval m (x.val:Word w)
  have stable (i : Fin (size G H k)) (M : Memory w) (h : Init M) : Init ((jobs i).after M) :=
    fun z hz=>(ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl (hz.trans_le (Nat.le_add_right ..)))).trans (h z hz)
  have now (i : Fin (size G H k)) (M : Memory w) (h : Init M) : Claim i ((jobs i).after M) :=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ _ x).trans (eval_below _ _ m M (fits _ _ _ _ old room) h)
  have keep (i j : Fin (size G H k)) (lt : i<j) (M : Memory w) (ok : Claim i M) : Claim i ((jobs j).after M) := by
    apply (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl ?_)).trans ok
    dsimp [dest]
    simp only [Equiv.apply_symm_apply]
    have q := Nat.mul_le_mul_right (2^k) lt
    rw [Nat.succ_mul] at q
    have := x.isLt
    omega
  have get := (Code.read_seq jobs Init stable Claim now keep m (fun _ _=>rfl) _ le_rfl).2
    ((index G H k) s) ((index G H k) s).isLt
  simpa only [program,jobs,Claim,Equiv.symm_apply_apply] using get

/-- The selected cost cache, including all split rows, survives the score gather
and minimum scan. Only words at or above the gathering base are touched there. -/
theorem afterSearch_before (base D cap : ℕ) (a : Bits k) (income : Fin H→List (Fin H))
    (ptr : Fin G→Fin H→ℕ) (m : Memory w) (z : ℕ) (lo : z<AllSeedsRAM.gatherBase G H k base) :
    AllSeedsRAM.afterSearch base D cap a income ptr m z=(AllSeedsRAM.stage w base D cap a income ptr).after m z :=
  (DescentFirstMinimumRAM.frame _ _ _ _ z (lo.trans_le (Nat.le_add_right ..))).trans
    (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl lo))

def expected (income : Fin H→List (Fin H)) (weight amount : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) (s : Slot G H k) (x : Block k) := match s.2 with
  | none => multiplierLoad (amount s.1.1) a μ.val s.1.2 x
  | some d => SiteRAM.retainedValue income (multiplierLoad (weight s.1.1) a μ.val) D cap (some d) s.1.2 x

/-- Every keyed output word of the same post-memory sees the native minimum
selected by the preceding procedure. For the occupancy rows, true split flags
are read from that seed's retained historical banks. For amount rows, the old
outgoing-count directory is pulled through that multiplier independently. -/
theorem published (base D cap : ℕ) (a : Bits k) (income : Fin H→List (Fin H))
    (ptr raw : Fin G→Fin H→ℕ) (m : Memory w) (weight amount : Fin G→Fin H→Block k→ℕ)
    (old : ∀g v,ptr g v+2^k≤base) (oldRaw : ∀g v,raw g v+2^k≤base)
    (room : endAt G H k base<2^w) (cf : cap<2^w)
    (inputs : ∀g v (x : Block k),m (ptr g v+x.val)=(weight g v x:Word w))
    (amounts : ∀g v (x : Block k),m (raw g v+x.val)=(amount g v x:Word w))
    («partial» : ∀(ν : Nonzero k) g d,d<k→∀v x,(Scan.readWeights (multiplierLoad (weight g) a ν.val) d v x).sum<2^w)
    (μ : Nonzero k) (found : AllSeedsRAM.afterSearch base D cap a income ptr m (WinningColumns.winnerPtr G H k base)=
      (MultiplierMinimumRAM.key μ:Word w)) (s : Slot G H k) (x : Block k) :
    (program w base raw a).after (AllSeedsRAM.afterSearch base D cap a income ptr m) (dest base s+x.val)=
      (expected income weight amount D cap a μ s x:Word w) := by
  let sealed := AllSeedsRAM.afterSearch base D cap a income ptr m
  have firstFit : first G H k base<2^w := (Nat.le_add_right ..).trans_lt room
  have bits : 2^k<2^w := (Nat.le_add_left ..).trans_lt firstFit
  have source (z : ℕ) (lo : z<base) : sealed z=m z :=
    (afterSearch_before base D cap a income ptr m z (lo.trans_le (Nat.le_add_right ..))).trans
      (Code.frame_seq (AllSeedsRAM.steps w base D cap a income ptr) z (fun i M=>
       CandidateRAM.below _ _ _ _ _ _ _ M z (lo.trans_le (Nat.le_add_right ..))) m _ _)
  rw [published_expr base raw a sealed oldRaw room s x]
  rcases s with ⟨⟨g,v⟩,(_|d)⟩
  · apply WinningColumns.outgoing_eval G H base (raw g v) a sealed (amount g v) bits μ found
    exact fun y=>(source _ ((Nat.add_lt_add_left y.isLt _).trans_le (oldRaw _ _))).trans (amounts _ _ y)
  · apply WinningColumns.column_eval base g v (some d) sealed income (weight g) D cap a bits.le μ found
    intro i y
    have addr := (Nat.add_lt_add_left y.isLt _).trans_le (old_end base i g v d)
    apply (afterSearch_before base D cap a income ptr m _ addr).trans
    apply AllSeedsRAM.retained_read base D cap a income ptr m weight old _ cf inputs «partial»
    have count := Nat.mul_le_mul_right (AllSeedsRAM.stride G H k) (Nat.sub_le (2^k) 1)
    have pow := Nat.le_pow_clog (by decide : 1<2) ((2^k)*AllSeedsRAM.stride G H k)
    exact ((Nat.add_le_add_left (count.trans pow) base).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))).trans_lt firstFit

/-- One physical run starts with both distinct old measurement directories.
It computes a minimizing multiplier and every outgoing and split word needed
to form the affine estimator's slabs. -/
theorem from_inputs (base D cap : ℕ) (a : Bits k) (income : Fin H→List (Fin H))
    (ptr raw : Fin G→Fin H→ℕ) (m : Memory w) (weight amount : Fin G→Fin H→Block k→ℕ)
    (hk : 0<k) (old : ∀g v,ptr g v+2^k≤base) (oldRaw : ∀g v,raw g v+2^k≤base)
    (room : endAt G H k base<2^w) (cf : cap<2^w) (bill : G*(H*2^k)<2^w)
    (B : ℕ) (reserve : 2^k*B<2^w) (limit : ∀g v x,weight g v x≤B)
    (inputs : ∀g v (x : Block k),m (ptr g v+x.val)=(weight g v x:Word w))
    (amounts : ∀g v (x : Block k),m (raw g v+x.val)=(amount g v x:Word w)) :
    let Q := uniformColonyScore income weight D cap a
    let search := AllSeedsRAM.search w base D cap a income ptr
    let sealed := AllSeedsRAM.afterSearch base D cap a income ptr m
    let P := program w base raw a
    ∃ μ : Nonzero k,(search.1.seq P.text).Exec m (P.after sealed) (search.2+P.ticks) ∧
      (scanMinimum Q (nonzeroWords k)).1=some (μ,Q μ) ∧ (∀ν,Q μ≤Q ν) ∧
      (∀s (x : Block k),P.after sealed (dest base s+x.val)=(expected income weight amount D cap a μ s x:Word w)) ∧
      ∀z<base,P.after sealed z=m z := by
  have firstFit : first G H k base<2^w := (Nat.le_add_right ..).trans_lt room
  have fit : AllSeedsRAM.winningBase G H k base+(2^k-1)<2^w :=
    (Nat.add_le_add_left (Nat.sub_le _ _) _).trans_lt firstFit
  obtain ⟨μ,pick,found,best,key,keep⟩ := AllSeedsRAM.selection base D cap a income ptr m weight hk old fit cf
    bill B reserve limit inputs
  refine ⟨μ,?_,found,best,?_,?_⟩
  · intro labels registers slots machine
    exact Procedure.Exec.then pick (run base raw a _ oldRaw room) machine
  · exact published base D cap a income ptr raw m weight amount old oldRaw room cf inputs amounts
      (fun μ g d _ v x=>CandidateRAM.interval_room weight a μ B limit reserve g d v x) μ key
  · intro z hz
    apply (below _ _ _ _ _ (hz.trans_le _)).trans (keep z hz)
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))

theorem ticks_bound (base : ℕ) (raw : Fin G→Fin H→ℕ) (a : Bits k) :
    (program w base raw a).ticks≤4+size G H k*(4+2^k*(2*(1+(2^k-1)*(10*2^k+18))+4)) := by
  apply Code.clock_seq
  intro i
  let s := (index G H k).symm i
  change 4+2^k*(2*(expr base raw a s).work+4)≤_
  rcases s with ⟨⟨g,v⟩,(_|d)⟩
  · exact (congrArg (fun b=>4+2^k*(2*b+4)) (WinningColumns.outgoing_work ..)).le
  · simp only [expr,WinningColumns.column_work]
    gcongr; omega

end Hierarchy.DescentColonies.Materialized

end
end OAI
