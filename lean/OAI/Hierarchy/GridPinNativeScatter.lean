import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.Hierarchy.GridPinNativeNatural
import OAI.Hierarchy.GridPinLiteralImage

namespace OAI
/-! # Native execution of the captured-bit and labelled endpoint scatters -/

namespace Hierarchy.GridPinNativeLoops
open Computability.VPVNP.BurstRAM PrivateRAM
open FactorBucketRAM GridPinLiteralImage
open ThreeFlat.RAM.PhysicalProcedure
open scoped Fin.CommRing

variable {w : ℕ}

/-- A loop with one destination per row can freely read initially stored
pointer and source arrays disjoint from the destinations. -/
private theorem iter_writes (step : Parameters w → Word w → Memory w → Memory w)
    (v : Parameters w) (m : Memory w) (n : ℕ) (addr : ℕ→ℕ) (src : ℕ→Word w)
    (write : ∀ i<n, ∀ o : Memory w, (∀ a, (∀ j < i, addr j≠a) → o a=m a) →
      step v (i:Word w) o = Function.update o (addr i) (src i)) :
    iterRows step v m n=writeRows addr src m n := by
  have eqn (k : ℕ) (hk : k≤n) : iterRows step v m k=writeRows addr src m k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iterRows,ih (by omega),writeRows]
      exact write k (by omega) _ (fun a ha => untouched _ _ _ _ _ ha)
  exact eqn n le_rfl

theorem initialized_cursors (dst stride start n : ℕ) (m : Memory w)
    (fits : n<2^w) (room : dst+n≤2^w) :
    (procedure seedOps (seedWords w n dst stride start)).Exec m
      (writeRows (fun i=>dst+i) (fun i=>((i*stride+start:ℕ):Word w)) m n) (3+n*(1+seedOps.length)) := by
  have image := iter_writes seedStep (seedWords w n dst stride start) m n
    (fun i=>dst+i) (fun i=>((i*stride+start:ℕ):Word w))
    (fun i hi o _ => seedStep_natural n dst stride start i o (by omega))
  rw [←image]
  intro P R K M
  exact Procedure.Spec.exec (f:=fun src=>iterRows seedStep (seedWords w n dst stride start) src n)
    (loop_spec seedOps seedStep (fun _ _ _ _ _ _ => seed_trace ..)
      (seedWords w n dst stride start) n fits rfl) m trivial M

theorem literals_image (p : SourceBanks) (n : ℕ) (m : Memory w) (dst : ℕ→ℕ)
    (spanFit : p.span < 2^w) (_countFit : n<2^w)
    (bounds : ∀ i<n, let j:=p.external+i; j<2^w ∧ p.blocks+j/p.span<2^w ∧
      p.originals+j<2^w ∧ p.literal+dst i<2^w)
    (offset : ∀ i<n, let j:=p.external+i;
      m (p.blocks+j/p.span)+((j%p.span:ℕ):Word w)=(dst i:Word w))
    (frame : ∀ i<n, ∀ k < i,
      p.literal+dst k≠p.blocks+(p.external+i)/p.span ∧ p.literal+dst k≠p.originals+(p.external+i)) :
    iterRows literalStep (literalWords w n p) m n=writeRows (fun i=>p.literal+dst i) (fun i=>m (p.originals+(p.external+i))) m n := by
  apply iter_writes
  intro i hi o stable
  obtain ⟨jfit,bfit,ofit,dfit⟩ := bounds i hi
  have block := stable _ (fun k hk=>(frame i hi k hk).1)
  have raw := stable _ (fun k hk=>(frame i hi k hk).2)
  rw [literalStep_natural p n i o spanFit _ rfl jfit bfit ofit (dst i)
    (by rw [block];exact offset i hi) dfit,raw]

theorem published_literals (p : SourceBanks) (n : ℕ) (m : Memory w) (dst : ℕ→ℕ)
    (spanFit : p.span < 2^w) (countFit : n<2^w)
    (bounds : ∀ i<n, let j:=p.external+i; j<2^w ∧ p.blocks+j/p.span<2^w ∧
      p.originals+j<2^w ∧ p.literal+dst i<2^w)
    (offset : ∀ i<n, let j:=p.external+i;
      m (p.blocks+j/p.span)+((j%p.span:ℕ):Word w)=(dst i:Word w))
    (frame : ∀ i<n, ∀ k < i,
      p.literal+dst k≠p.blocks+(p.external+i)/p.span ∧ p.literal+dst k≠p.originals+(p.external+i)) :
    (procedure literalOps (literalWords w n p)).Spec (fun o=>o=m)
      (fun _ o=>o=writeRows (fun i=>p.literal+dst i) (fun i=>m (p.originals+(p.external+i))) m n)
      (3+n*(1+literalOps.length)) := by
  rw [←literals_image p n m dst spanFit countFit bounds offset frame]
  intro P R K M
  exact Procedure.Spec.exec (f:=fun src=>iterRows literalStep (literalWords w n p) src n)
    (loop_spec literalOps literalStep (fun _ _ _ _ _ _ => literal_trace ..)
      (literalWords w n p) n countFit rfl) m trivial M

theorem endpoints_image (p : SourceBanks) (n : ℕ) (m : Memory w) (rail : ℕ→ℕ)
    (spanFit : p.span<2^w) (two : 2<2^w) (countFit : n<2^w)
    (real : ∀ i<n, m (p.rails+i/2)=(rail (i/2):Word w))
    (bounds : ∀ i<n, let j:=rail (i/2)*2+i%2;
      p.rails+i/2<2^w ∧ j<2^w ∧ p.blocks+j/p.span<2^w ∧ p.dest+i<2^w)
    (frame : ∀ i<n, ∀ k < i, let j:=rail (i/2)*2+i%2;
      p.dest+k≠p.rails+i/2 ∧ p.dest+k≠p.blocks+j/p.span) :
    iterRows endpointStep (endpointWords w n p) m n=writeRows (fun i=>p.dest+i) (fun i=>
        let j:=rail (i/2)*2+i%2
        m (p.blocks+j/p.span)+((j%p.span:ℕ):Word w)) m n := by
  apply iter_writes
  intro i hi o stable
  obtain ⟨rfit,jfit,bfit,dfit⟩ := bounds i hi
  have ranks := stable _ (fun k hk=>(frame i hi k hk).1)
  have block := stable _ (fun k hk=>(frame i hi k hk).2)
  rw [endpointStep_natural p n i o two (hi.trans countFit) spanFit rfit _ _
    (ranks.trans (real i hi)) rfl jfit bfit dfit,block]

theorem published_endpoints (p : SourceBanks) (n : ℕ) (m : Memory w) (rail : ℕ→ℕ)
    (spanFit : p.span<2^w) (two : 2<2^w) (countFit : n<2^w)
    (real : ∀ i<n, m (p.rails+i/2)=(rail (i/2):Word w))
    (bounds : ∀ i<n, let j:=rail (i/2)*2+i%2;
      p.rails+i/2<2^w ∧ j<2^w ∧ p.blocks+j/p.span<2^w ∧ p.dest+i<2^w)
    (frame : ∀ i<n, ∀ k < i, let j:=rail (i/2)*2+i%2;
      p.dest+k≠p.rails+i/2 ∧ p.dest+k≠p.blocks+j/p.span) :
    (procedure endpointOps (endpointWords w n p)).Spec (fun o=>o=m)
      (fun _ o=>o=writeRows (fun i=>p.dest+i) (fun i=>
        let j:=rail (i/2)*2+i%2
        m (p.blocks+j/p.span)+((j%p.span:ℕ):Word w)) m n)
      (3+n*(1+endpointOps.length)) := by
  rw [←endpoints_image p n m rail spanFit two countFit real bounds frame]
  intro P R K M
  exact Procedure.Spec.exec (f:=fun src=>iterRows endpointStep (endpointWords w n p) src n)
    (loop_spec endpointOps endpointStep (fun _ _ _ _ _ _ => endpoint_trace ..)
      (endpointWords w n p) n countFit rfl) m trivial M

end Hierarchy.GridPinNativeLoops

end OAI
