import OAI.Hierarchy.DescentResetHaloBroadcast

namespace OAI
/-! # One mounted dictionary broadcasts every candidate's public slot number -/
namespace Hierarchy.DescentUniformSlotOperands
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

def site (H : ℕ) (_ : Fin H) : Fin 1:=0
def shelf (base J : ℕ) (j : Fin J) : Bank:=⟨base+j.val,0⟩
def expr (base H G M b : ℕ) {J : ℕ} (j : Fin J) :=
  DescentResetHaloBroadcast.expr (shelf base J j) (base+J) H G M b
def stop (base J H G M b : ℕ) := DescentResetHaloBroadcast.endAt (base+J) H G M b
def program (base J H G M b w : ℕ) :=
  (DescentStaticWordColumn.program w base id J).seq
    (DescentStaticWordColumn.program w (base+J) (DescentResetHaloBroadcast.literal b G M (site H))
      (DescentResetHaloBroadcast.count H G M b))
def result (base J H G M b : ℕ) {w : ℕ} (m : Memory w) :=
  DescentStaticWordColumn.image (base+J) (DescentResetHaloBroadcast.literal b G M (site H))
    (DescentStaticWordColumn.image base id m J) (DescentResetHaloBroadcast.count H G M b)

theorem fits {w J : ℕ} (base H G M b : ℕ) (j : Fin J) (room : stop base J H G M b<2^w) :
    (expr base H G M b j).Fits w (stop base J H G M b) := by
  let n:=H*chunks G M
  let a:=DescentResetHaloBroadcast.bits H G M b
  let top:=stop base J H G M b
  have far : top=base+J+2*n+2^a:=rfl
  have fit (offset : ℕ) (bound : offset≤2*n) : (⟨base+J+offset,a⟩:Bank).Fits w top :=
    ⟨Nat.two_pow_pos _,by change 2^a<2^w; omega,by change base+J+offset+2^a≤top;omega⟩
  have untilSlots : base+J ≤ top :=by
    rw [far]
    exact (Nat.le_add_right (base+J) (2*n)).trans (Nat.le_add_right _ (2^a))
  have jpos : 1 ≤ J := Nat.succ_le_of_lt ((Nat.zero_le j.val).trans_lt j.isLt)
  have raw : (shelf base J j).Fits w top :=
    ⟨by change 0 < 1; decide,
      jpos.trans_lt (((Nat.le_add_left J base).trans untilSlots).trans_lt room),
      (by simpa only [Nat.add_assoc] using Nat.add_le_add_left (Nat.succ_le_of_lt j.isLt) base :
        base+j.val+1 ≤ base+J).trans untilSlots⟩
  have first : (⟨base+J,a⟩:Bank).Fits w top:=by simpa using fit 0 (by omega)
  exact ⟨fit (2*n) le_rfl,⟨fit n (by omega),trivial⟩,raw,first,trivial⟩

theorem produce {w : ℕ} (base J H G M b : ℕ) (m : Memory w)
    (small : J≤2^b) (room : stop base J H G M b<2^w) :
    let N:=DescentResetHaloBroadcast.count H G M b
    let dst:=result base J H G M b m
    (program base J H G M b w).Exec m dst ((4+10*J)+(4+10*N)) ∧
      (∀j:Fin J,Source (expr base H G M b j) (fun _ : Fin H=>fun _ : Fin G=>(j.val:Cell b)) M dst) ∧
      (∀a,a<base ∨ stop base J H G M b≤a→dst a=m a) ∧
      DescentStaticWordColumn.names (program base J H G M b w)=15*(J+1)+15*(N+1) := by
  intro N dst
  let prior:=DescentStaticWordColumn.image base id m J
  let f:=DescentResetHaloBroadcast.literal b G M (site H)
  have fit : base+J+N≤ stop base J H G M b := by
    have size:=Nat.le_pow_clog (by decide : 1<2) (N+1)
    change base+J+N≤base+J+2*(H*chunks G M)+2^(Nat.clog 2 (N+1))
    omega
  have early : base+J<2^w:= (Nat.le_add_right (base+J) N).trans_lt (fit.trans_lt room)
  refine ⟨Procedure.Exec.then (DescentStaticWordColumn.mount base J id m early)
    (DescentStaticWordColumn.mount (base+J) N f prior (fit.trans_lt room)),?_,?_,?_⟩
  · intro j
    have jpos : 1 ≤ J := Nat.succ_le_of_lt ((Nat.zero_le j.val).trans_lt j.isLt)
    have lo : 1 < 2^w := jpos.trans_lt ((Nat.le_add_left J base).trans_lt early)
    have bank : (shelf base J j).Fits w (base+J) :=
      ⟨by change 0 < 1; decide, lo, by change base+j.val+1 ≤ base+J; omega⟩
    have set (i : Fin 1) : prior ((shelf base J j).base+i.val)=(((j.val:Cell b).val:ℕ):Word w) := by
      have zi : i.val=0 := by omega
      simpa [prior,shelf,zi,Fin.val_cast_of_lt (j.isLt.trans_le small)] using (DescentStaticWordColumn.read base J id m j.isLt)
    exact (DescentResetHaloBroadcast.run (shelf base J j) (base+J) (site H)
      (fun _ : Fin 1=>(j.val:Cell b)) prior bank le_rfl set room).2.1
  · intro a away
    apply (DescentStaticWordColumn.frame (base+J) N f prior a
      (away.imp (fun low=>by omega) (fun high=>fit.trans high))).trans
    exact DescentStaticWordColumn.frame base J id m a (away.imp_right (fun high=>(Nat.le_add_right _ N).trans (fit.trans high)))
  · simp only [program,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount,N]

end
end Hierarchy.DescentUniformSlotOperands

end OAI
