import OAI.Hierarchy.DescentSubwordReturn
import OAI.Hierarchy.DescentPackedColumnBatch

namespace OAI
/-! # One shared packed-word splitting dictionary for all incoming signed port columns -/
namespace Hierarchy.DescentGLPacked.BankImage.SignedFields.Retile
open DescentSIMDLookup DescentPackedZip DescentPackedColony.Phase.Arena ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {a H G K R M N w : ℕ}

def pitch (H G M : ℕ) := 2^(Nat.clog 2 (H*chunks G M))
def stop (base a H G R M N : ℕ) := Subwords.destination base a H G R M+(N+1)*pitch H G M
def output (base a H G R M : ℕ) (j : Fin N) : Bank :=
  ⟨Subwords.destination base a H G R M+j.val*pitch H G M,Nat.clog 2 (H*chunks G M)⟩
def field (base a H G R M : ℕ) (input : Fin N→Bank) (j : ℕ) : Expr :=
  if hj:j<N then Subwords.term (Subwords.chart base a H G R M) (input ⟨j,hj⟩) else .lit 0
def scans (base a H G R M : ℕ) (input : Fin N→Bank) :=
  DescentPackedFlowBatch.passes (Subwords.destination base a H G R M) (H*chunks G M) (pitch H G M)
    (field base a H G R M input) 0 N
def program (base H a : ℕ) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) (input : Fin N→Bank) (w : ℕ) :=
  (Subwords.literals (w:=w) base H a size ratio pos).program.seq (ProtocolRAM.program w (scans base a H G R M input))
def ticks (base H a : ℕ) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) (input : Fin N→Bank) :=
  4+10*(Subwords.literals (w:=0) base H a size ratio pos).length+clock (scans base a H G R M input)

theorem fits_output (base : ℕ) (j : Fin N) (room : stop base a H G R M N<2^w) :
    (output base a H G R M j).Fits w (stop base a H G R M N) ∧ H*chunks G M≤(output base a H G R M j).size := by
  let stride:=pitch H G M
  let first:=Subwords.destination base a H G R M
  have position:=Nat.mul_le_mul_right stride (Nat.succ_le_of_lt j.isLt)
  rw [Nat.succ_mul] at position
  have limit:first+(N+1)*stride<2^w:=room
  rw [Nat.succ_mul] at limit
  change (0<stride ∧ stride<2^w ∧ first+j.val*stride+stride≤first+(N+1)*stride) ∧ _
  rw [Nat.succ_mul]
  exact ⟨⟨Nat.two_pow_pos _,by omega,by omega⟩,Nat.le_pow_clog (by decide) _⟩

theorem issued (base : ℕ) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M)
    (input : Fin N→Bank) (X : Fin N→Fin H→Fin G→Cell a) (mem : Memory w)
    (safe : ∀j,(input j).Fits w base) (wide : ∀j,H*chunks G (R*M)≤(input j).size)
    (read : ∀j (p : Row H G (R*M)),mem ((input j).base+(row H G (R*M) p).val)=((data (X j) p).val:Word w))
    (room : stop base a H G R M N<2^w) :
    ∃dst,(program base H a size ratio pos input w).Exec mem dst (ticks base H a size ratio pos input) ∧
      CheapCode (program base H a size ratio pos input w) ∧
      (∀j (p : Row H G M),dst ((output base a H G R M j).base+(row H G M p).val)=((data (X j) p).val:Word w)) ∧
      ∀z,z<base ∨ stop base a H G R M N≤z→dst z=mem z := by
  let I:=Subwords.literals (w:=w) base H a size ratio pos
  let out:=Subwords.destination base a H G R M
  let T:=Subwords.chart base a H G R M
  let mid:=I.output mem
  let f:=field base a H G R M input
  let price:=pitch H G M
  let rows:=H*chunks G M
  have parts:rows≤price:=Nat.le_pow_clog (by decide) _
  have last : out+(N+1)*price<2^w:=room
  rw [Nat.succ_mul] at last
  have short:Subwords.finish base a H G R M<2^w:=by change out+rows<_;omega
  have before : base≤out:=Nat.le_add_right ..
  have fixed : Subwords.endAt base a H G R M≤out := by dsimp [out,Subwords.endAt,Subwords.destination];omega
  have page : I.low+I.length<2^w:=by
    change base+_ <_
    rw [Subwords.length_eq]
    change base+(2*rows+R*Subwords.stride a R M)<_
    dsimp [Subwords.endAt] at fixed
    omega
  obtain ⟨emit,resident,preserved⟩:=I.issue mem page
  have rom:=Subwords.actual base H a size ratio pos mid resident
  have rooms (j : Fin N) :=Subwords.geometry (a:=a) base (input j) (safe j) (wide j) short
  have terms (j:ℕ) (ok:j<N) : (f j).Fits w out:=by
    rw [show f j=Subwords.term T (input ⟨j,ok⟩) by simp [f,field,T,ok]]
    let rm:=rooms ⟨j,ok⟩
    exact ⟨rm.dictFit,⟨rm.offsetFit,trivial⟩,rm.dataFit,rm.parentFit,trivial⟩
  obtain ⟨ran,atRow,below⟩:=DescentPackedFlowBatch.execute out rows price N f mid terms (by omega) parts
  refine ⟨_,emit.then ran,cheap_seq I.hardware.1 (program_cheap w _),?_,?_⟩
  · intro j p
    refine (atRow j (row H G M p)).trans ?_
    rw [show f j.val=Subwords.term T (input j) by simp [f,field,T,j.isLt]]
    apply Subwords.word_at T _ out (rooms j) size ratio pos _ mid rom _ p
    intro u
    have lt:=((row H G (R*M) u).isLt.trans_le (wide j))
    exact (preserved _ (.inl ((Nat.add_lt_add_left lt _).trans_le (safe j).2.2))).trans (read j u)
  · intro z hz
    rcases hz with lo|hi
    · exact (below z (lo.trans_le before)).trans (preserved z (.inl lo))
    · have later:out+(0+N)*price≤z:=by change out+(N+1)*price≤z at hi;rw [Nat.succ_mul] at hi;simp only [Nat.zero_add];omega
      exact (DescentPackedFlowBatch.above out rows price f mid 0 N z parts later).trans
        (preserved _ (.inr (by change Subwords.endAt base a H G R M≤_; omega)))

def image (base H a : ℕ) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M)
    (input : Fin N→Bank) (mem : Memory w) : Memory w :=
  result (scans base a H G R M input) ((Subwords.literals (w:=w) base H a size ratio pos).output mem)

/-- Totality and fixed time hold on corrupt input words as well. -/
theorem runs (base : ℕ) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M)
    (input : Fin N→Bank) (safe : ∀j,(input j).Fits w base)
    (wide : ∀j,H*chunks G (R*M)≤(input j).size)
    (room : stop base a H G R M N<2^w) (mem : Memory w) :
    (program base H a size ratio pos input w).Exec mem (image base H a size ratio pos input mem) (ticks base H a size ratio pos input) ∧
      CheapCode (program base H a size ratio pos input w) ∧
      ∀z,z<base ∨ stop base a H G R M N≤z→image base H a size ratio pos input mem z=mem z := by
  let out:=Subwords.destination base a H G R M
  let I:=Subwords.literals (w:=w) base H a size ratio pos
  let amount:=H*chunks G M
  let gap:=pitch H G M
  have parts : amount≤gap:=Nat.le_pow_clog (by decide) _
  have limit : out+(N+1)*gap<2^w:=room
  rw [Nat.succ_mul] at limit
  have short : Subwords.finish base a H G R M<2^w:=by change out+amount<_;omega
  have hdr : I.low+I.length<2^w:=by
    change base+_ < _
    rw [Subwords.length_eq]
    dsimp [out,Subwords.destination,amount] at limit
    omega
  have valid (j : ℕ) (hj:j<N) : (field base a H G R M input j).Fits w out := by
    simp only [field,dite_eq_left hj]
    let rm:=Subwords.geometry (a:=a) base (input ⟨j,hj⟩) (safe _) (wide _) short
    exact ⟨rm.dictFit,⟨rm.offsetFit,trivial⟩,rm.dataFit,rm.parentFit,trivial⟩
  obtain ⟨run,_,below⟩:=DescentPackedFlowBatch.execute out amount gap N (field base a H G R M input) (I.output mem)
    valid (by omega) parts
  obtain ⟨emit,_,fixed⟩:=I.issue mem hdr
  refine ⟨emit.then run,cheap_seq I.hardware.1 (program_cheap w _),?_⟩
  rintro z (lo|hi)
  · exact (below _ (lo.trans_le (Nat.le_add_right ..))).trans (fixed _ (.inl lo))
  · have endAt:out+(0+N)*gap≤z:=by change out+(N+1)*gap≤z at hi;rw [Nat.succ_mul] at hi;simp only [Nat.zero_add];omega
    exact (DescentPackedFlowBatch.above out amount gap _ _ 0 N z parts endAt).trans (fixed _ (.inr (by
      change Subwords.endAt base a H G R M≤_
      have low:Subwords.endAt base a H G R M≤out:=by dsimp [Subwords.endAt,Subwords.destination,out];omega
      omega)))

theorem any_input (base : ℕ) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M)
    (input : Fin N→Bank) (safe : ∀j,(input j).Fits w base)
    (wide : ∀j,H*chunks G (R*M)≤(input j).size)
    (room : stop base a H G R M N<2^w) (mem : Memory w) :
    ∃dst,(program base H a size ratio pos input w).Exec mem dst (ticks base H a size ratio pos input) ∧
      CheapCode (program base H a size ratio pos input w) := by
  obtain ⟨run,cheap,_⟩:=runs (a:=a) base size ratio pos input safe wide room mem
  exact ⟨_,run,cheap⟩

theorem tariff (base H a : ℕ) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) (input : Fin N→Bank) :
    ticks base H a size ratio pos input≤
      8+10*(2*(H*chunks G M)+R*Subwords.stride a R M)+N*(4+(H*chunks G M)*(2*48+4)) := by
  have bound:=DescentPackedFlowBatch.tariff (Subwords.destination base a H G R M) (H*chunks G M) (pitch H G M) N
    (field base a H G R M input) 48 (fun j hj=>by simp [field,hj,Subwords.term,Expr.work])
  unfold ticks
  rw [Subwords.length_eq]
  unfold scans
  omega

end
end Hierarchy.DescentGLPacked.BankImage.SignedFields.Retile

end OAI
