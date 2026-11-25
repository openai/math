import OAI.Hierarchy.DescentPackedWalshMount

namespace OAI
/-! # The basis of the chronological reset is read from the original two count families -/
namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open DescentPackedWalsh DescentSIMDLookup DescentPackedWalshReduction DescentGL DescentIntegerScale
open DescentMeasuredWeights DescentWeightColumnRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ} (E : EstimatorArena)
local notation "P" => E.plan
local notation "k" => E.dim

def spectrumMem (start : Memory w) :=
  numeratorMem E.transformAt E.start E.squareAt E.hosts E.high E.low E.precision start

def image (start : Memory w) :=
  PhysicalTrajectory.finalMemory k E.solveAt E.bank (E.calendar.state P E.hosts (E.spectrumMem start) (k+1))

def cpu (w : ℕ) : Procedure w :=
  ((numeratorCode E.transformAt E.start E.squareAt E.hosts E.high E.low E.precision w).seq
    (E.calendar.code P w E.hosts (k+1))).seq (PhysicalTrajectory.program w k E.solveAt E.bank)

def clock :=
  numeratorTicks E.hosts E.high E.low+E.calendar.ticks P E.hosts (k+1)+
    (PhysicalTrajectory.time k E.solveAt E.bank k+DescentGLPermutationRAM.clock k)

/-- The first forward transform's zeroth coefficient on each physical row. -/
def FirstTotals (x : Fin E.hosts→Bits k→ℕ) (out : Memory w) : Prop :=
  ∀v,digit E.precision (ordinal E.low (fun _=>false)).val
      (out (location E.start E.hosts E.high k+(row v (fun _ : Fin E.high=>false)).val)).val=∑z,x v z

theorem spectrum_zero (fits : E.Fits w) (mem prev : Memory w)
    (x : Fin E.hosts→Bits k→ℕ) (B : ℕ) (bound : ∀v a,x v a≤B) (precision : 2^(3*k)*B^2<2^E.precision)
    (resident : ∀a<E.start,mem a=E.literal prev a)
    (old : Installed E.start (fun v=>shaped (fun a=>(asCube (x v) a:Cell E.precision))) mem) :
    E.FirstTotals x (E.spectrumMem mem) := by
  obtain ⟨a,b,c,d,e,f,g⟩:=E.areas
  have last : E.inputEnd≤E.solveAt:=E.calendar.pre (k+1)
  have endWidth : E.inputEnd<2^w:=last.trans_lt fits.bounded
  have numWords : sqOffset E.start E.hosts E.high E.low+(k+1)*page E.hosts E.high=E.inputEnd := by
    unfold inputEnd numeratorAt location
    rw [Nat.add_mul,Nat.one_mul,Nat.add_assoc]
  have key : smallKey E.low E.precision≤w :=
    (Nat.le_add_left _ E.gainBits).trans fits.lookup
  obtain ⟨_,_,zero,_⟩:=issued_spectrum E.transformAt E.start E.squareAt (E.baseMemory prev) mem x B bound
    precision key le_rfl (Nat.le_add_right E.staticEnd E.dataGap) (numWords.trans_lt endWidth) resident old
  exact zero

theorem spectrum_input (fits : E.Fits w) (mem prev : Memory w)
    (lev : Fin E.hosts→ℕ) (gain : Fin E.hosts→Cell E.gainBits) (x : Fin E.hosts→Bits k→ℕ)
    (B : ℕ) (bound : ∀v a,x v a≤B) (precision : 2^(3*k)*B^2<2^E.precision)
    (resident : ∀a<E.start,mem a=E.literal prev a)
    (old : Installed E.start (fun v=>shaped (fun a=>(asCube (x v) a:Cell E.precision))) mem)
    (levels : ∀v,prev (E.depthRows.base+v.val)=(lev v:Word w))
    (gains : ∀v,prev (E.gainRows.base+v.val)=((gain v).val:Word w)) :
    let m:=E.spectrumMem mem
    (numeratorCode E.transformAt E.start E.squareAt E.hosts E.high E.low E.precision w).Exec mem m
      (numeratorTicks E.hosts E.high E.low) ∧
    (∀j<k+1,DepthInput (E.shelf j) E.inputEnd E.payload E.precision E.precision E.gainBits
      E.positive lev gain x m prev) ∧ ∀a<E.start,m a=mem a := by
  obtain ⟨a,b,c,d,e,f,g⟩:=E.areas
  have last : E.inputEnd≤E.solveAt:=E.calendar.pre (k+1)
  have endWidth : E.inputEnd<2^w:=last.trans_lt fits.bounded
  have numWords : sqOffset E.start E.hosts E.high E.low+(k+1)*page E.hosts E.high=E.inputEnd := by
    unfold inputEnd numeratorAt location
    rw [Nat.add_mul,Nat.one_mul,Nat.add_assoc]
  have key : smallKey E.low E.precision≤w :=
    (Nat.le_add_left _ E.gainBits).trans fits.lookup
  obtain ⟨exec,spectrum,_,frame⟩:=issued_spectrum E.transformAt E.start E.squareAt (E.baseMemory prev) mem x B bound
    precision key le_rfl (Nat.le_add_right E.staticEnd E.dataGap) (numWords.trans_lt endWidth) resident old
  refine ⟨exec,?_,frame⟩
  intro j live
  obtain ⟨room,ports⟩:=E.shared_room fits j live
  have fromROM {i : ℕ} (early : i<E.start) : E.spectrumMem mem i=E.literal prev i :=
    (frame i early).trans (resident i early)
  have fromOld (bank : Bank) (fits : bank.Fits w E.start)
      (away : bank.base+bank.size≤E.origin ∨ E.staticEnd≤bank.base) (i : ℕ) (hi : i<bank.size) :
      E.spectrumMem mem (bank.base+i)=prev (bank.base+i) := by
    have inBank:=Nat.add_lt_add_left hi bank.base
    rw [fromROM (inBank.trans_le fits.2.2)]
    rcases away with lo|high
    · exact E.literal_before prev (inBank.trans_le lo)
    · exact E.literal_after prev (high.trans (Nat.le_add_right ..))
  have weights:=E.weight_fixed prev
  have readWeight {i : ℕ} (hi : i<E.reduceAt) : E.spectrumMem mem i=E.literal prev i :=
    fromROM (hi.trans_le (b.trans (c.trans (d.trans e))))
  have literals : Weight.Fixed E.weights E.high E.low E.precision E.precision E.gainBits E.hosts
      (E.spectrumMem mem) := by
    have ownerEnd := (Nat.le_add_right (page E.hosts E.high) (2^E.gainBits)).trans
      (Nat.le_add_right _ (2^(E.gainBits+E.precision*2^E.low)))
    constructor
    · intro v p
      have h:=(row v p).isLt.trans_le (rows_le E.hosts E.high)
      exact (readWeight (by
        change E.origin+(row v p).val<E.origin+
        (page E.hosts E.high+2^E.gainBits+2^(E.gainBits+E.precision*2^E.low))
        exact Nat.add_lt_add_left (h.trans_le ownerEnd) _)).trans (weights.owner v p)
    · intro i
      have h:=i.isLt
      exact (readWeight (by
        have before := (Nat.add_lt_add_left h (page E.hosts E.high)).trans_le
          (Nat.le_add_right _ (2^(E.gainBits+E.precision*2^E.low)))
        change E.origin+page E.hosts E.high+i.val<E.origin+
          (page E.hosts E.high+2^E.gainBits+2^(E.gainBits+E.precision*2^E.low))
        simpa only [Nat.add_assoc] using
          Nat.add_lt_add_left before E.origin)).trans (weights.shift i)
    · intro i
      have h:=i.isLt
      exact (readWeight (by change E.origin+page E.hosts E.high+2^E.gainBits+i.val<E.origin+
        (page E.hosts E.high+2^E.gainBits+2^(E.gainBits+E.precision*2^E.low));omega)).trans (weights.result i)
  refine ⟨room,ports,literals,?_,?_,spectrum,?_,?_,(E.packed_before j).le,?_,?_,?_⟩
  · intro v
    exact (fromOld E.depthRows fits.depth fits.depthAway _ (v.isLt.trans_le fits.hostRows.1)).trans (levels v)
  · intro v
    exact (fromOld E.gainRows fits.gain fits.gainAway _ (v.isLt.trans_le fits.hostRows.2)).trans (gains v)
  · exact c.trans (d.trans (e.trans (f.trans g)))
  · exact d.trans (e.trans (f.trans g))
  · exact (E.includes_bank j live).trans_lt fits.bounded
  · dsimp only
    intro z low high
    exact (fromROM (high.trans_le (c.trans (d.trans e)))).trans (E.reduce_pins prev z low high)
  · dsimp only
    intro i hi
    have h : E.orderAt+i<E.transformAt := Nat.add_lt_add_left hi _
    exact (fromROM (h.trans_le (d.trans e))).trans (E.extract_pins prev i hi)

/-- The program and all addresses are fixed by the arena. The chosen matrix and the exact finite
permutation image come from applying that program to the two original physical count families. -/
theorem from_counts_first {A C : Type} [Fintype A] [Fintype C] (levels : A→ℕ)
    (loc : Item levels C↪Fin E.hosts) (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ)
    (x : A→Bits k→ℕ) (y : C→Bits k→ℕ) (f full K q scoreBits B : ℕ) (mem prev : Memory w)
    (fit : E.Fits w) (gainRoom : ∀v,padded loc (gain levels f full K) 0 v<2^E.gainBits)
    (bound : ∀v a,padded loc (load levels x y) (fun _=>0) v a≤B)
    (precision : 2^(3*k)*B^2<2^E.precision) (ordinals : ∀v,padded loc (level levels j cj) 0 v<2^w)
    (stages : k+1≤2^w) (payload : E.payload≤w) (integer : E.precision+Nat.clog 2 E.hosts≤w)
    (billSize : ∀s<k+1,∀v d,bill s (padded loc (level levels j cj) 0)
      (fun z=>(⟨_,gainRoom z⟩:Cell E.gainBits)) (padded loc (load levels x y) (fun _=>0)) v d<2^E.precision)
    (resident : ∀a<E.start,mem a=E.literal prev a)
    (old : Installed E.start (fun v=>shaped (fun a=>(asCube (padded loc (load levels x y) (fun _=>0) v) a:
      Cell E.precision))) mem)
    (names : ∀v,prev (E.depthRows.base+v.val)=((padded loc (level levels j cj) 0 v : ℕ):Word w))
    (gains : ∀v,prev (E.gainRows.base+v.val)=((padded loc (gain levels f full K) 0 v : ℕ):Word w))
    (centralRoom : PhysicalTrajectory.Room w k E.solveAt E.bank)
    (positive : 0<q) (scoreSize : 3*k+scoreBits+2≤w)
    (scores : ∀v d,mixingWeightNumerator levels j cj x y f full K v d≤2^scoreBits) :
    let W:=mixingWeightNumerator levels j cj x y f full K
    let μ:=PhysicalTrajectory.canonicalTrajectory W q k
    (E.cpu w).Exec mem (E.image mem) E.clock ∧
    (∀i : Fin k,E.image mem (PhysicalTrajectory.pointer k E.solveAt i.val)=
      ((rowIndex k (rowFunctional μ i)).val:Word w)) ∧
    (∀i : Fin (2^k),E.image mem (PhysicalTrajectory.outputBase k E.solveAt+i.val)=
      ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm i))).val:Word w)) ∧
    (∀z<E.start,E.image mem z=mem z) ∧
    E.FirstTotals (padded loc (load levels x y) (fun _=>0)) (E.image mem) := by
  dsimp only
  obtain ⟨spectrum,inputs,low⟩:=E.spectrum_input fit mem prev _
    (fun v => (⟨_,gainRoom v⟩ : Cell E.gainBits)) _ B bound precision resident old names gains
  have saved := E.calendar.pre (k+1)
  obtain ⟨collect,allValues,lower⟩:=measured_calendar E.calendar E.payload E.positive (E.spectrumMem mem)
    prev _ _ _ B bound precision fit.layout ordinals stages (saved.trans_lt fit.bounded) payload integer billSize inputs
  obtain ⟨solver,rows,cube,frame⟩:=issue_canonical levels loc j cj x y f full K gainRoom E.bank _ centralRoom
    positive scoreSize scores (fun v=>allValues v.val v.isLt)
  have interval : E.start≤E.inputEnd:=E.areas.2.2.2.2.2.1.trans E.areas.2.2.2.2.2.2
  have unchanged (z : ℕ) (hz : z<E.inputEnd) : E.image mem z=E.spectrumMem mem z:=
    (frame z (hz.trans_le saved)).trans (lower z hz)
  refine ⟨?_,rows,cube,fun z hz=>(unchanged z (hz.trans_le interval)).trans (low z hz),?_⟩
  · intro labels regs slots machine
    exact Procedure.Exec.then (Procedure.Exec.then spectrum collect) solver machine
  · intro v
    have rowFit:=(row v (fun _ : Fin E.high=>false)).isLt.trans_le (rows_le E.hosts E.high)
    have endFirst : location E.start E.hosts E.high k+page E.hosts E.high≤E.inputEnd:=by
      unfold inputEnd numeratorAt sqOffset location
      rw [Nat.succ_mul];omega
    rw [unchanged _ ((Nat.add_lt_add_left rowFit _).trans_le endFirst)]
    exact E.spectrum_zero fit mem prev _ B bound precision resident old v


theorem from_counts {A C : Type} [Fintype A] [Fintype C] (levels : A→ℕ)
    (loc : Item levels C↪Fin E.hosts) (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ)
    (x : A→Bits k→ℕ) (y : C→Bits k→ℕ) (f full K q scoreBits B : ℕ) (mem prev : Memory w)
    (fit : E.Fits w) (gainRoom : ∀v,padded loc (gain levels f full K) 0 v<2^E.gainBits)
    (bound : ∀v a,padded loc (load levels x y) (fun _=>0) v a≤B)
    (precision : 2^(3*k)*B^2<2^E.precision) (ordinals : ∀v,padded loc (level levels j cj) 0 v<2^w)
    (stages : k+1≤2^w) (payload : E.payload≤w) (integer : E.precision+Nat.clog 2 E.hosts≤w)
    (billSize : ∀s<k+1,∀v d,bill s (padded loc (level levels j cj) 0)
      (fun z=>(⟨_,gainRoom z⟩:Cell E.gainBits)) (padded loc (load levels x y) (fun _=>0)) v d<2^E.precision)
    (resident : ∀a<E.start,mem a=E.literal prev a)
    (old : Installed E.start (fun v=>shaped (fun a=>(asCube (padded loc (load levels x y) (fun _=>0) v) a:
      Cell E.precision))) mem)
    (names : ∀v,prev (E.depthRows.base+v.val)=((padded loc (level levels j cj) 0 v : ℕ):Word w))
    (gains : ∀v,prev (E.gainRows.base+v.val)=((padded loc (gain levels f full K) 0 v : ℕ):Word w))
    (centralRoom : PhysicalTrajectory.Room w k E.solveAt E.bank)
    (positive : 0<q) (scoreSize : 3*k+scoreBits+2≤w)
    (scores : ∀v d,mixingWeightNumerator levels j cj x y f full K v d≤2^scoreBits) :
    let W:=mixingWeightNumerator levels j cj x y f full K
    let μ:=PhysicalTrajectory.canonicalTrajectory W q k
    (E.cpu w).Exec mem (E.image mem) E.clock ∧
    (∀i : Fin k,E.image mem (PhysicalTrajectory.pointer k E.solveAt i.val)=
      ((rowIndex k (rowFunctional μ i)).val:Word w)) ∧
    (∀i : Fin (2^k),E.image mem (PhysicalTrajectory.outputBase k E.solveAt+i.val)=
      ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm i))).val:Word w)) ∧
    ∀z<E.start,E.image mem z=mem z := by
  obtain ⟨ran,rows,table,frame,_⟩:=E.from_counts_first levels loc j cj x y f full K q scoreBits B mem prev fit
    gainRoom bound precision ordinals stages payload integer billSize resident old names gains centralRoom positive scoreSize scores
  exact ⟨ran,rows,table,frame⟩

end
end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
