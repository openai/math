import OAI.Hierarchy.GridCompilerAdmission
import OAI.Hierarchy.GridControllerSimGeometry
import OAI.Hierarchy.GridSimulationAssign
import OAI.Hierarchy.GridPinCanonicalSpec
import OAI.Hierarchy.GridPinResourceFiber

namespace OAI
/-! # Actual classified cost rows feed the grid tick and literal writer -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridSimulation
open ThreeFlat RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM GridPinArena GridThrough FactorPinIntervals
open scoped Fin.CommRing Classical

variable {w k n q d nparams ell text B e S N stages full span : ℕ}

/-- The known sector layout supplies all surviving sources after the
threshold and classification passes. The length in the public resource row
is the actual number of bits in the original intervals belonging to the node. -/
theorem publication_input (Q : Layout (Cell k n×Fin q) S N d) (ht : 0<(n+1)^k*q)
    (cost : Fin N→Fin (k+2)→ℕ) (dest : Fin full→Fin N) (bucket : Fin S→Fin full)
    (quotient : ∀ j,(bucket j).val=j.val/(2*span)) (own : ∀j,dest (bucket j)=Q.origin j)
    (pos : 0<w) (spanPos : 0< span) (bitRoom : S≤full*(2*span))
    (small : GridPinArena.Small w (GridPinPublisher.canonical w k n q d nparams ell text B e S N stages full (2*span))
      S full (stages*full) ((20*(w+1)+2)^(k+2)))
    (words : GridReceiverHeader.count w≤ slab w) (sFit : S≤GridDescription.sector w)
    (capFit : ell≤GridDescription.sector w)
    (capture m : Memory (64*w)) (o : Memory (64*w)) (award : Assigned ht cost m o)
    (reads : ∀ f : Fin N,m (14*GridDescription.sector w+f.val*(k+2)+1)=
      (TraceAdmission.inputCount dest f S span:Word (64*w)))
    (anc : ∀ b : Fin full,m (16*GridDescription.sector w+slab w+stages*full+b.val)=((dest b).val:Word (64*w)))
    (low : ∀ j<S,m j=capture j)
    (sel : ∀ i<ell,m (12*GridDescription.sector w+i)=capture (12*GridDescription.sector w+i)) :
    GridPinPublisher.Raw (GridPinPublisher.canonical w k n q d nparams ell text B e S N stages full (2*span))
      Q ht cost dest capture o := by
  let J := GridDescription.sector w
  let g := slab w
  let K := (20*(w+1)+2)^(k+2)
  have sep : 32*g≤J := (scales w pos).1
  have rows : N*(k+2)≤g := small.resource
  have items : N≤g := (Nat.le_mul_of_pos_right _ (by omega : 0<k+2)).trans rows
  have keys : K≤g := small.classes
  have protected_low (a : ℕ) (below : a<14*J) : protectedAddress w N (k+2) a := by
    unfold protectedAddress FactorBucketRAM.untouched FactorBucketRAM.Outside
    dsimp [assignmentBanks]; omega
  have bank (a : ℕ) (here : 14*J≤a) (before : a<14*J+g) : protectedAddress w N (k+2) a := by
    unfold protectedAddress FactorBucketRAM.untouched FactorBucketRAM.Outside
    dsimp [assignmentBanks]; omega
  have archive (a : ℕ) (beyond : 16*J≤a) : protectedAddress w N (k+2) a := by
    change FactorBucketRAM.Outside a (14*J+g) (GridReceiverHeader.count w) ∧
      FactorBucketRAM.Outside a (15*J) (N*(k+2)) ∧ FactorBucketRAM.Outside a (15*J+g) N ∧
      FactorBucketRAM.Outside a (15*J+2*g) K ∧ FactorBucketRAM.Outside a (15*J+3*g) N
    unfold FactorBucketRAM.Outside
    omega
  refine ⟨award.key,award.owner,?_,?_,?_,?_⟩
  · intro f
    have bound := Nat.mul_le_mul_right (k+2) f.isLt
    rw [Nat.succ_mul] at bound
    change o (14*J+f.val*(k+2)+1)=_
    rw [award.frame _ (bank _ (by omega) (by omega)),reads]
    rw [GridPinPublisher.inputLength_from_resource dest Q.origin bucket spanPos bitRoom quotient own]
  · intro b
    change o (16*J+g+stages*full+b.val)=_
    rw [award.frame _ (archive _ (by omega)),anc]
  · intro j hj
    change o (0+j)=capture (0+j)
    simpa using (award.frame j (protected_low _ (by omega))).trans (low j hj)
  · intro i hi
    change i < ell at hi
    change o (12*J+i)=capture (12*J+i)
    rw [award.frame _ (protected_low _ (by omega)),sel _ hi]

/-- The executable suffix following successful resource publication. -/
def publication (P : GridPinPublisher.Plan) (w src N k T e : ℕ) : Procedure (64*w) :=
  (assign w src N (k+2) T).seq (P.canonicalProgram (64*w) e)

variable {F : Type} [Field F] [Fintype F] {u tp tr tk ep er ek : ℕ}
variable (X : Catalyst.Approximation F k u) (enc : FieldCode F (64*w))
variable (params : Fin nparams→Word (64*w)) (recv : Machine (64*w) tp tr tk)
    (eval : Machine (64*w) ep er ek) (x : Fin (e*2)→Bool) (sel : Fin ell→Bool)
local notation "pp" => GridPinPublisher.canonical w k n q d nparams ell text B e S N stages full (2*span)
local notation "capture" => GridPinPublisher.capture (compact:=B) X enc params recv eval x sel

theorem published (Q : Layout (Cell k n×Fin q) S N d) (ht : 0<(n+1)^k*q)
    (cost : Fin N→Fin (k+2)→ℕ) (dest : Fin full→Fin N) (bucket : Fin S→Fin full)
    (quotient : ∀ j,(bucket j).val=j.val/(2*span)) (own : ∀j,dest (bucket j)=Q.origin j)
    (dispatch : ∀ f,GridTicks.index (Q.owner f)=FactorAllocation.owner ht w cost f)
    (order : ∀ t,Q.rows t=FactorAllocation.factors w cost (List.finRange N) (GridTicks.index t))
    (direction : Fin e→Fin k) (railRoom : e*2≤S)
    (paired : ∀ f,Q.origin (pairPorts (GridPinPublisher.exteriorRails railRoom) (f,true))=
      Q.origin (pairPorts (GridPinPublisher.exteriorRails railRoom) (f,false)))
    (textFit : text≤w^2)
    (header : ∀ t,Q.header t=GridReceiverHeader.header text textFit (GridDescription.code (q:=w^2) recv eval)
      ((GridTicks.index t).val:Word (64*w)) params sel)
    (advice : Q.advice=GridPinCapturedSources.advice (e:=e) (compact:=B) X enc params recv eval)
    (rawSize : GridSelfHeader.rawSize w e B nparams≤S)
    (pos : 0<w) (axis : k≤w) (spanPos : 0< span)
    (small : GridPinArena.Small w pp S full (stages*full) ((20*(w+1)+2)^(k+2)))
    (original : Memory (64*w))
    (resources : ∀ (i : Fin N) (j : Fin (k+2)),
      (original (14*GridDescription.sector w+(i.val*(k+2)+j.val))).val=cost i j)
    (lengths : ∀ f : Fin N,original (14*GridDescription.sector w+f.val*(k+2)+1)=
      (TraceAdmission.inputCount dest f S span:Word (64*w)))
    (anc : ∀ b : Fin full,original (16*GridDescription.sector w+slab w+stages*full+b.val)=((dest b).val:Word (64*w)))
    (low : ∀ j, j<S → original j=capture j)
    (saved : ∀ i<ell,original (12*GridDescription.sector w+i)=capture (12*GridDescription.sector w+i)) :
    let A := PinAssignment.ofFactorIntervals Q direction (pairPorts (GridPinPublisher.exteriorRails railRoom)) paired
    let src := thresholdSource w e B nparams
    (publication pp w src N k ((n+1)^k*q) e).Spec (·=original)
      (fun _ out=>GridPinPublisher.Published A pp out ∧ ∀ a,protectedAddress w N (k+2) a →
        GridPinPublisher.Outside pp e a → out a=original a)
      (assignTime w N (k+2) + (3+e*(1+GridPinNativeLoops.seedOps.length)+(pp).budget (64*w))) := by
  intro A src
  let g := slab w
  let J := GridDescription.sector w
  let T := (n+1)^k*q
  have sc : 32*g≤J ∧ 32*J<2^(64*w) := scales w pos
  have power : g*g=J := by change 2^(16*w)*2^(16*w)=2^(32*w); rw [←pow_add]; congr 1; omega
  have rows : N*(k+2)≤g := small.resource
  have upperN : N≤g := (Nat.le_mul_of_pos_right _ (by omega : 0<k+2)).trans rows
  have count : GridReceiverHeader.count w≤g := by
    have h : w+1≤2^w := Nat.lt_two_pow_self
    have bigger : 32*2^w≤g := by
      change 2^5*2^w≤2^(16*w)
      rw [←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    dsimp [GridReceiverHeader.count];omega
  have bitBound : S≤g := small.bits
  have capBound : ell≤g := small.selector
  have ticksBound : T≤g := (Nat.le_mul_of_pos_right T small.pinsPos).trans small.pinStorage
  have extent : src+(64*w)*(GridReceiverHeader.count w)=GridSelfHeader.rawSize w e B nparams := by
    dsimp [src,thresholdSource,GridSelfHeader.rawSize]; ring
  have sep : GridSelfHeader.rawSize w e B nparams≤12*J := by omega
  have inTable (i : ℕ) (hi : i<(64*w)*GridReceiverHeader.count w) :
      original (src+i)=((FactorBucketRAM.thresholdBit (64*w) i).toNat:Word (64*w)) := by
    rw [low _ (by omega)]
    exact threshold_read X enc params recv eval x sel pos sep i hi
  have run1 : (assign w src N (k+2) T).Spec (·=original)
      (fun _ out => Assigned ht cost original out) (assignTime w N (k+2)) :=
    assign_spec (src:=src) pos ht (by omega : 0<k+2) cost original
    rows count upperN small.classes (lt_of_le_of_lt ((Nat.mul_le_mul rows count).trans_eq power) (by omega))
    (lt_of_le_of_lt (show k+2≤64*w by omega) Nat.lt_two_pow_self) (by omega) (by omega)
    inTable resources
  let assigned := fun o : Memory (64*w) => Assigned ht cost original o
  have run2 : ((pp).canonicalProgram (64*w) e).Spec assigned
      (fun m out=>GridPinPublisher.Published A pp out ∧
        ∀ a,GridPinPublisher.Outside pp e a→ out a=m a) (3+e*(1+GridPinNativeLoops.seedOps.length)+(pp).budget (64*w)) := by
    intro pc regs slots M code reg pub exit install rom cfg m entry hit
    have ready := publication_input Q ht cost dest bucket quotient own pos spanPos small.capacity
      small count (by omega) (by omega) capture original m hit lengths anc low saved
    exact GridPinPublisher.canonicalSpec pp X enc params recv eval x sel Q ht cost dest bucket quotient own
      dispatch order direction railRoom paired textFit pos header advice rawSize sep rfl small m ready
      M code reg pub exit install rom cfg m entry rfl
  intro pcs regs slots machine pc reg pub exit install rom cfg m entry initial
  obtain ⟨ticks,within,final,out,advance,hpc,tmp,classified,ready⟩ :=
    Procedure.Spec.seq run1 run2 (fun _ _ hit=>hit)
      machine pc reg pub exit install rom cfg m entry initial
  exact ⟨ticks,within,final,out,advance,hpc,ready.1,
    fun a keep outside => (ready.2 a outside).trans (classified.frame a keep)⟩

/-- Below the compact X bank all five classification intervals and all six
pin publication intervals begin strictly above the byte being retained. -/
theorem low_preserved (_pos : 0<w) (z : ℕ) (lo : z<4*GridDescription.sector w) :
    protectedAddress w N (k+2) z ∧ GridPinPublisher.Outside pp e z := by
  let J := GridDescription.sector w
  have high : 0<J := Nat.two_pow_pos _
  have h : z<4*J := lo
  simp only [protectedAddress,FactorBucketRAM.untouched,FactorBucketRAM.Outside,assignmentBanks,
    GridPinPublisher.Outside,GridPinPublisher.canonical]
  omega

section Geometry
variable {m logRadix pc : ℕ}
local notation "rails" => GridControllerSimGeometry.railCount m n B
local notation "plan" => GridPinPublisher.canonical w (m+1) n q d nparams ell text B rails S N stages full (2*span)
local notation "arena" => GridCompilerAdmission.arena w
local notation "arch" => GridControllerIdle.shape m n B logRadix q d pc
local notation "bank" => (arena).data rails n
variable (X : Catalyst.Approximation F (m+1) (q*d)) (code : FieldCode F (64*w))
variable (Q : Layout (Cell (m+1) n×Fin q) S N d)
variable (room : GridControllerSimGeometry.railCount m n B*2≤S)
local notation "ports" => pairPorts (GridPinPublisher.exteriorRails room)
variable (same : ∀ f,Q.origin (pairPorts (GridPinPublisher.exteriorRails room) (f,true)) =
  Q.origin (pairPorts (GridPinPublisher.exteriorRails room) (f,false)))
local notation "setting" => PinAssignment.ofFactorIntervals Q GridIdleLayout.direction ports same

/-- The last two physical operations of the simulator return the complete
native wiring input, including every original external pin and compact row.
The assignment phase is the real threshold/digit/key and stable pin-publisher
program, with its joint post supplied by `published`. -/
theorem publication_raw (src : ℕ) (positive : 0<q*d) (large : 0<w)
    (fit : GridControllerIdle.Fits (64*w) arena arch)
    (roomG : GridControllerIdle.Room arena arch)
    (space : GridOrderedSources.Fits (r:=rails) (n:=n) (w:=64*w) X arena B)
    (count : Fin (m+1) → GridTicks.Tick (m+1) (n+1) q → ℕ)
    (conserve : ∀ j t,(GridTicks.pairFiber GridIdleLayout.direction
      (fun e=>GridTicks.index (Q.tick (ports (e,false)))) j t).card=count j t)
    (enough : ∀ c j,X.width j≤((GridTicks.pairsOn (count j) (GridTicks.lineTicks j c)) \
      (GridTicks.pairsOn (count j) (GridTicks.cellTicks c))).card)
    (original m0 : Memory (64*w)) (pin : Fin (rails*2)→Bool) (elapsed : ℕ)
    (compact : ∀ i<GridApproximationAdvice.wordCount X,m0 (2*GridDescription.sector w+i)=
      GridApproximationAdvice.paddedMemory X code B (2*GridDescription.sector w) original (2*GridDescription.sector w+i))
    (raw : ∀ i : Fin (rails*2),m0 i.val=RAM.BitLayout.bitWord (64*w) (pin i))
    (assigned : (publication plan w src N (m+1) ((n+1)^(m+1)*q) rails).Spec (·=m0)
      (fun _ out=>GridPinPublisher.Published setting plan out ∧ ∀ a,protectedAddress w N ((m+1)+2) a →
        GridPinPublisher.Outside plan rails a → out a=m0 a) elapsed) :
    let issue := publication plan w src N (m+1) ((n+1)^(m+1)*q) rails
    let hydrate := (GridControllerSimGeometry.program (64*w) arena arch).seq
      (GridOrderedDataRAM.prepare (64*w) bank (arch).data ((arch).rails*2))
    (issue.seq hydrate).Spec (·=m0) (fun _ out=>GridOrderedSources.Raw X
      (Program.ofScheduled setting X.width count conserve enough) code arena B pin out original)
      (elapsed+(GridControllerSimGeometry.cost (64*w) arena arch+(9+5*(arch).data+11*((arch).rails*2)))) := by
  intro issue hydrate
  have hydrated : Procedure.Spec hydrate _ _ _ :=
    GridControllerSimGeometry.raw_spec arena X code Q ports same plan rfl rfl
      original pin positive fit roomG space count conserve enough
  have together : Procedure.Spec _ _ _ _ := Procedure.Spec.seq assigned hydrated (by
    intro _ out h
    have frame (a : ℕ) (ha : a<4*GridDescription.sector w) : out a=m0 a := by
      have keep:=low_preserved (w:=w) (k:=m+1) (n:=n) (q:=q) (d:=d)
        (nparams:=nparams) (ell:=ell) (text:=text) (B:=B) (e:=rails) (S:=S) (N:=N)
        (stages:=stages) (full:=full) (span:=span) large a ha
      exact h.2 a keep.1 keep.2
    refine ⟨h.1,?_,?_⟩
    · intro i hi
      have cells : GridApproximationAdvice.wordCount X≤GridDescription.sector w:=space.words
      have below : 2*GridDescription.sector w+i<4*GridDescription.sector w:=by omega
      exact (frame _ below).trans (compact i hi)
    · intro i
      have few : GridControllerSimGeometry.railCount m n B≤GridDescription.sector w/8:=roomG.rails
      have inside : i.val<GridControllerSimGeometry.railCount m n B*2:=i.isLt
      exact (frame _ (by omega)).trans (raw i))
  intro pcs regs slots machine pcEntry reg pub exit install rom cfg mem entry initial
  obtain ⟨ticks,within,last,out,advance,done,middle,_,final⟩ :=
    together machine pcEntry reg pub exit install rom cfg mem entry initial
  exact ⟨ticks,within,last,out,advance,done,final⟩


end Geometry

end Hierarchy.GridSimulation
end

end OAI
