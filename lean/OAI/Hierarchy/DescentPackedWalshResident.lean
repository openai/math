import OAI.Hierarchy.DescentPackedWalshArena

namespace OAI
/-! # All depth passes reuse a single literal image and the previously computed local transforms -/
namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open DescentPackedWalsh DescentSIMDLookup DescentPackedWalshReduction ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ} (A : EstimatorArena)

theorem areas :
    A.origin≤A.reduceAt ∧ A.reduceAt≤A.orderAt ∧ A.orderAt≤A.transformAt ∧ A.transformAt≤A.squareAt ∧
      A.squareAt≤A.start ∧ A.start≤A.numeratorAt ∧ A.numeratorAt≤A.inputEnd := by
  refine ⟨Nat.le_add_right ..,?_,Nat.le_add_right ..,Nat.le_add_right ..,(Nat.le_add_right A.squareAt _).trans (Nat.le_add_right A.staticEnd _),?_,Nat.le_add_right ..⟩
  · exact A.plan.header_mono A.reduceAt (Nat.zero_le _)
  · unfold numeratorAt location sqOffset
    omega

theorem literal_low (m : Memory w) {z : ℕ} (early : z<A.transformAt) :
    A.literal m z=A.baseMemory m z := by
  have sq:=A.areas.2.2.2.1
  simp only [literal,initial,mounted,squareROM,ite_eq_right (Nat.not_le_of_gt early),
    ite_eq_right (Nat.not_le_of_gt (early.trans_le sq))]

theorem literal_before (m : Memory w) {z : ℕ} (low : z<A.origin) : A.literal m z=m z := by
  obtain ⟨a,b,c,_,_,_,_⟩:=A.areas
  rw [A.literal_low m (low.trans_le (a.trans (b.trans c))),
    A.lower_reduce m z (low.trans_le (a.trans b)),A.plan.mount_low _ _ _ _ (low.trans_le a)]
  exact Weight.frame _ _ _ _ _ _ _ _ (Or.inl low)

theorem weight_fixed (m : Memory w) : Weight.Fixed A.weights A.high A.low A.precision A.precision
    A.gainBits A.hosts (A.literal m) := by
  let W:=Weight.install A.origin A.hosts A.high A.low A.precision A.precision A.gainBits m
  have read {z : ℕ} (hz : z<A.reduceAt) : A.literal m z=W z := by
    obtain ⟨_,a,b,_,_,_,_⟩:=A.areas
    rw [A.literal_low m (hz.trans_le (a.trans b)),A.lower_reduce m z (hz.trans_le a)]
    exact A.plan.mount_low _ _ _ _ hz
  have lit:=Weight.reads A.origin A.hosts A.high A.low A.precision A.precision A.gainBits
    A.depthRows A.gainRows (⟨A.numeratorAt,rowBits A.hosts A.high⟩:Bank) m
  have t₁:=Nat.two_pow_pos A.gainBits
  have t₂:=Nat.two_pow_pos (A.gainBits+A.precision*2^A.low)
  constructor
  · intro v p
    have hi:=(row v p).isLt.trans_le (rows_le A.hosts A.high)
    exact (read (by change A.origin+(row v p).val<A.origin+
      (page A.hosts A.high+2^A.gainBits+2^(A.gainBits+A.precision*2^A.low));omega)).trans (lit.owner v p)
  · intro a
    have hi:=a.isLt
    exact (read (by change A.origin+page A.hosts A.high+a.val<A.origin+
      (page A.hosts A.high+2^A.gainBits+2^(A.gainBits+A.precision*2^A.low));omega)).trans (lit.shift a)
  · intro a
    have hi:=a.isLt
    exact (read (by change A.origin+page A.hosts A.high+2^A.gainBits+a.val<A.origin+
      (page A.hosts A.high+2^A.gainBits+2^(A.gainBits+A.precision*2^A.low));omega)).trans (lit.result a)

theorem reduce_pins (m : Memory w) (z : ℕ) (low : A.reduceAt≤z) (high : z<A.orderAt) :
    A.literal m z=A.plan.mount A.reduceAt m A.plan.depth z := by
  rw [A.literal_low m (high.trans_le A.areas.2.2.1),A.lower_reduce m z high]
  exact A.plan.mount_inside _ _ _ _ _ low high

theorem extract_pins (m : Memory w) (i : ℕ) (hi : i<Column.size A.dim
    (A.precision+A.plan.depth) (A.plan.laneBits A.plan.depth)) :
    A.literal m (A.orderAt+i)=A.orderRow i :=
  (A.literal_low m (Nat.add_lt_add_left hi A.orderAt)).trans (A.order_read m i hi)

structure Fits (A : EstimatorArena) (w : ℕ) : Prop where
  hostRows : A.hosts≤A.depthRows.size ∧ A.hosts≤A.gainRows.size
  depth : A.depthRows.Fits w A.start
  gain : A.gainRows.Fits w A.start
  depthAway : A.depthRows.base+A.depthRows.size≤A.origin ∨ A.staticEnd≤A.depthRows.base
  gainAway : A.gainRows.base+A.gainRows.size≤A.origin ∨ A.staticEnd≤A.gainRows.base
  bounded : A.solveAt<2^w
  word : rowBits A.hosts A.high≤w
  lookup : A.gainBits+A.precision*2^A.low≤w
  layout : laneBits A.dim A.payload A.precision=A.low

/-- All old addresses and the printed numerator are inside the one retained low-memory band. -/
theorem host_words (fits : A.Fits w) : A.hosts*2^A.high≤A.dataWords :=by
    have bound:=A.plan.data_mono 0 (show 1≤A.plan.depth+1 by omega)
    change 0+A.plan.hosts 0*A.plan.chunks 0≤A.dataWords at bound
    have num : 2^A.high≤A.plan.chunks 0 := by
      apply Nat.pow_le_pow_right (by decide)
      change A.high≤A.high+A.low-A.plan.laneBits 0
      have clear : A.plan.laneBits 0=A.low := by
        simpa only [plan,reduction,Plan.laneBits,Nat.add_zero,laneBits,dim] using fits.layout
      omega
    exact (Nat.mul_le_mul A.plan.real_le num).trans (by simpa only [Nat.zero_add] using bound)

theorem shared_room (fits : A.Fits w) (j : ℕ) (live : j<A.dim+1) :
    Weight.Room A.weights (A.scratch j) A.hosts A.high A.low A.precision A.gainBits w ∧
    (∀S∈[A.weights.owner,A.weights.depth,A.weights.gain,A.weights.shift,A.weights.numer,A.weights.results],
      S.base+S.size≤A.inputEnd) := by
  obtain ⟨a,b,c,d,e,f,g⟩:=A.areas
  have all : A.reduceAt≤A.inputEnd:=by omega
  have scratch : A.inputEnd≤A.scratch j:=A.calendar.pre j
  have final := (A.includes_bank j live).trans_lt fits.bounded
  have chunkFits:=A.host_words fits
  have bound : A.scratch j+A.hosts*2^A.high<2^w:= ((Nat.add_le_add_left chunkFits _).trans
    (Nat.le_add_right (A.bank j) _)).trans_lt final
  have before : A.start≤A.scratch j:=by omega
  have weaken {S : Bank} (ok : S.Fits w A.start) : S.Fits w (A.scratch j):=
    ⟨ok.1,ok.2.1,ok.2.2.trans before⟩
  have endNum : A.numeratorAt+page A.hosts A.high≤A.scratch j:=scratch
  have realNum : (⟨A.numeratorAt,rowBits A.hosts A.high⟩:Bank).Fits w (A.scratch j) :=
    ⟨Nat.two_pow_pos _,by change page A.hosts A.high<2^w;omega,endNum⟩
  have fit:=Weight.room A.origin (A.scratch j) A.hosts A.high A.low A.precision A.gainBits _ _ _
    bound (all.trans scratch) fits.word fits.lookup (weaken fits.depth) (weaken fits.gain) realNum fits.hostRows
      (rows_le A.hosts A.high)
  have afterResults : A.origin+page A.hosts A.high+2^A.gainBits+
      2^(A.gainBits+A.precision*2^A.low)≤A.inputEnd := by
    simpa only [reduceAt, Weight.footprint, Nat.add_assoc] using all
  have afterShift := (Nat.le_add_right _ _).trans afterResults
  refine ⟨fit,?_⟩
  intro S member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl
  · change A.origin+page A.hosts A.high≤A.inputEnd
    exact (Nat.le_add_right _ _).trans afterShift
  · exact fits.depth.2.2.trans (f.trans g)
  · exact fits.gain.2.2.trans (f.trans g)
  · change A.origin+page A.hosts A.high+2^A.gainBits≤A.inputEnd
    exact afterShift
  · exact le_rfl
  · change A.origin+page A.hosts A.high+2^A.gainBits+2^(A.gainBits+A.precision*2^A.low)≤A.inputEnd
    exact afterResults

end
end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
