import OAI.Computability.BorderVNP.DiagonalTallyRAMArena
import OAI.Computability.BorderVNP.DiagonalTallyRAMBroadcast

/-! # The complete native tally evaluator on its physical allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyScatter
open DiagonalTallyMaterialize (Operand storeAll storeAll_before)
open private resident_congr from OAI.Computability.BorderVNP.DiagonalTallyRAMLayout

/-- Materialize the sparse records and initialize this team's local counter array. -/
def prepareTallies : Code := .seq DiagonalTallyMaterialize.materialize clear

/-- Compute the local increments, check the common row, aggregate and serialize every
parameter exponent and scalar multiplicity for the residue reader. -/
def evaluateTallies : Code := .seq prepareTallies complete

variable {w : ℕ}

/-- The initial data at the entry following the private cell and cube lookup calls.
Every condition concerns the input memory or natural sizes of the source records. -/
structure Arena.Source (a : Arena) (pub : Arg → Word w) (m : Memory w)
    (os : List Operand) (xs : List (List Bool)) (p : ℕ) : Prop where
  /-- Address space for this team's arena. -/
  fits : a.Fits w (pub 0).val
  /-- Scalar directory at entry. -/
  directory : a.frame.resident pub m
  /-- Output encoder directory at entry. -/
  bitsDirectory : serializeFrame pub m (a.bitFrame w) a.dim
  /-- First physical input descriptor, passed from cell and packet evaluation. -/
  inputPtr : (m ((pub 0).val+44)).val=p
  /-- Native inputs, including the actual returned values reached by the five-word descriptors. -/
  operands : DiagonalTallyMaterialize.supplied m a.fresh p os
  /-- Number of source operands. -/
  count : os.length=a.count
  /-- Every parameter and gadget ID belongs to this common coordinate bank. -/
  coords : ∀ o∈os,o.pair.1<a.dim
  /-- The sums of nonnegative local increments fit into a word. -/
  sums : ∀ j<a.dim,incrementAt a.frame.localBase (a.frame.localBase+j) (os.map Operand.pair)<2^w
  /-- The common prefix provides the actual raw bit words in memory. -/
  raw : DiagonalTallyBits.WordsAt m a.raw xs
  /-- Rectangular field count. -/
  number : xs.length=a.teams*a.dim
  /-- Fixed field width. -/
  lengths : ∀ x∈xs,x.length=a.width

/-- The natural increment at one true coordinate before the common claim is read. -/
def Arena.localRow (a : Arena) (os : List Operand) (c : ℕ) : ℕ :=
  incrementAt a.frame.localBase (a.frame.localBase+c) (os.map Operand.pair)

/-- Complete step bound with sparse input work and the explicit rectangular decode,
aggregation and serialization work. -/
def Arena.work (a : Arena) (w : ℕ) (os : List Operand) : ℕ :=
  DiagonalTallyMaterialize.setup.slots+21*os.length+8*(os.map fun o => o.digits.length).sum+1+
    (clearSetup.slots+4*a.dim+1)+costBound a.frame+serializeSetup.slots+10*(a.dim*w)+1

private theorem supplied_ptr_bound (m : Memory w) (limit p : ℕ) (os : List Operand)
    (h : DiagonalTallyMaterialize.supplied m limit p os) (pfit : p<2^w) (room : limit<2^w) :
    p+5*os.length < 2^w := by
  induction os generalizing p with
  | nil => simpa using pfit
  | cons o os ih =>
    obtain ⟨hp,_,_,_,tail⟩ := h
    have h := ih (p+5) tail (by omega)
    simp only [List.length_cons,Nat.mul_succ]; omega

private theorem Arena.prepare_runs (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (h : a.Source pub m os xs p) :
    ∃ es t, Runs pub mac prepareTallies s m es t (a.initialized m os) ∧
      traceCost es ≤ DiagonalTallyMaterialize.setup.slots+21*os.length+
        8*(os.map fun o => o.digits.length).sum+1+(clearSetup.slots+4*a.dim+1) := by
  have hf := h.fits.frameFit
  have hroom : a.fresh+2*a.count<2^w := hf.2.2.1
  have dir := h.fits.dir
  have hdir : (pub 0).val+44<2^w := by omega
  have hptr : p<2^w := h.inputPtr ▸ (m ((pub 0).val+44)).isLt
  have frame : DiagonalTallyMaterialize.frameAt pub m p a.fresh os.length :=
    ⟨h.inputPtr,h.directory.2.2.1,h.directory.2.2.2.1.trans h.count.symm⟩
  obtain ⟨x,t,rx,hx,_,_⟩ := DiagonalTallyMaterialize.materialize_runs pub mac s m os p a.fresh a.fresh
    frame h.operands le_rfl hdir (supplied_ptr_bound m _ _ os h.operands hptr (by omega)) (h.count ▸ hroom)
  have resident := resident_congr a.frame pub m (storeAll m a.fresh os) h.directory
    (fun j _ hj => storeAll_before m a.fresh j os (by omega))
  obtain ⟨y,u,ry,hy⟩ := clear_runs pub mac t (storeAll m a.fresh os) a.frame resident hf
  refine ⟨_,_,rx.seq ry,?_⟩
  rw [show traceCost (x++y) = traceCost x+traceCost y from VPVNP.RAMBuckets.cost_append ..]
  exact Nat.add_le_add hx hy

private theorem Arena.initialized_count (a : Arena) (m : Memory w) (os : List Operand) (c : ℕ) (hc : c<a.dim) :
    DiagonalTallyScatter.after a.frame.localBase (os.map Operand.pair) (a.initialized m os) (a.frame.localBase+c) =
      word w (a.localRow os c) := by
  simp [DiagonalTallyScatter.after,Arena.initialized,cleared,Arena.localRow,hc]

/-- Genuine execution from the source memory for every matching local row. Every output
bit is the corresponding low-to-high bit of the global sum read from the common prefix. -/
theorem evaluateTallies_runs (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (h : a.Source pub m os xs p)
    (matchRow : ∀ c<a.dim,word w (a.localRow os c)=claimWord a.frame xs a.team c) :
    ∃ es t m', Runs pub mac evaluateTallies s m es t m' ∧ traceCost es ≤ a.work w os ∧
      (∀ e ∈ es, e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      ∀ c<a.dim, ∀ j<w, m' ((a.bitFrame w).dst+(c*w+j)) =
        word w (((∑ i : Fin a.teams,claimWord (w := w) a.frame xs i.val c).val.testBit j).toNat) := by
  obtain ⟨x,t,rx,hx⟩ := a.prepare_runs pub mac s m os xs p h
  have hi := a.input pub m os xs p h.fits h.directory h.operands h.count h.coords h.sums h.raw h.number h.lengths
  have hdir : (pub 0).val+43<2^w := by
    have hd := h.fits.dir
    have hroom : a.fresh+2*a.count<2^w := h.fits.frameFit.2.2.1
    omega
  obtain ⟨y,u,mu,ry,hy,_,bits⟩ := complete_runs pub mac t (a.initialized m os) a.frame (a.bitFrame w)
    (os.map Operand.pair) xs hi (fun c hc => (a.initialized_count m os c hc).trans (matchRow c hc))
    h.fits.bitFit hdir rfl (a.finalFrame pub m os xs h.fits h.bitsDirectory hi)
  have run := rx.seq ry
  refine ⟨_,_,_,run,?_,ordinary_run (show ordinary evaluateTallies = true by decide) run,bits⟩
  rw [show traceCost (x++y) = traceCost x+traceCost y from VPVNP.RAMBuckets.cost_append ..]
  change traceCost y ≤ costBound a.frame+serializeSetup.slots+10*(a.dim*w)+1 at hy
  unfold Arena.work; omega

/-- Conversely, every returning execution forces the numerical claim of this team. -/
theorem evaluateTallies_sound (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (h : a.Source pub m os xs p) {es t mt} (run : Runs pub mac evaluateTallies s m es t mt) :
    ∀ c<a.dim,word w (a.localRow os c)=claimWord a.frame xs a.team c := by
  obtain ⟨_,u,rx,_⟩ := a.prepare_runs pub mac s m os xs p h
  have hi := a.input pub m os xs p h.fits h.directory h.operands h.count h.coords h.sums h.raw h.number h.lengths
  cases run with
  | atom h _ _ => cases h
  | seq prep rest =>
    obtain ⟨_,rfl,rfl⟩ := rx.unique_of_deterministic (by decide) prep
    intro c hc
    exact (a.initialized_count m os c hc).symm.trans
      (complete_sound pub mac u (a.initialized m os) a.frame (os.map Operand.pair) xs hi rest c hc)

/-- When the actual natural rows are supplied in the common prefix, the physical
output bank carries the bits of their ordinary integer sums. This includes all carries
between little-endian digits and uses one instruction history for each fixed assignment. -/
theorem evaluateTallies_natural_runs (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (p : ℕ) (rows : Fin a.teams → Fin a.dim → ℕ)
    (h : a.Source pub m os (broadcast a.width rows) p) (rowFit : ∀ i c, rows i c<2^a.width)
    (localCounts : ∀ c, a.localRow os c.val = rows ⟨a.team,h.fits.team⟩ c)
    (sumFit : ∀ c, ∑ i, rows i c < 2^w) :
    ∃ es t m', Runs pub mac evaluateTallies s m es t m' ∧ traceCost es ≤ a.work w os ∧
      (∀ e ∈ es, e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      ∀ c : Fin a.dim, ∀ j<w, m' ((a.bitFrame w).dst+(c.val*w+j)) =
        word w (((∑ i,rows i c).testBit j).toNat) := by
  have each (i : Fin a.teams) (c : Fin a.dim) :
      claimWord (w := w) a.frame (broadcast a.width rows) i.val c.val=word w (rows i c) := by
    exact (claimWord_fieldWord a.frame rfl _ i c).trans (fieldWord_broadcast rows rowFit i c)
  obtain ⟨es,t,mt,run,work,trace,bits⟩ := evaluateTallies_runs a pub mac s m os _ p h (fun c hc =>
    (congrArg (word w) (localCounts ⟨c,hc⟩)).trans (each ⟨a.team,h.fits.team⟩ ⟨c,hc⟩).symm)
  refine ⟨es,t,mt,run,work,trace,fun c j hj => ?_⟩
  exact (bits c.val c.isLt j hj).trans (congrArg (fun q : ℕ => word w (q.testBit j).toNat)
    (claimSum_val (w := w) a.frame _ c.val (fun i => rows i c) (fun i => each i c) (sumFit c)))

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
