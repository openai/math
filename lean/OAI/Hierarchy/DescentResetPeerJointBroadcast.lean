import OAI.Hierarchy.DescentResetHaloBroadcast
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Packing the four joint peer ranks of each compact reset host -/

namespace Hierarchy.DescentResetPeerJointBroadcast

open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

abbrev count := DescentResetHaloBroadcast.count
abbrev endAddress := DescentResetHaloBroadcast.endAt

def program (w base H G M b : ℕ) : Procedure w :=
  DescentStaticWordColumn.program w base (DescentResetHaloBroadcast.literal b G M (id : Fin H→Fin H))
    (count H G M b)

def image {w : ℕ} (base H G M b : ℕ) (m : Memory w) : Memory w :=
  DescentStaticWordColumn.image base (DescentResetHaloBroadcast.literal b G M (id : Fin H→Fin H)) m
    (count H G M b)

def ticks (H G M b : ℕ) := 4+10*count H G M b

def expr (base H G M b : ℕ) (banks : Fin 4→Bank) (j : Fin 4) : Expr :=
  DescentResetHaloBroadcast.expr (banks j) base H G M b

theorem shift (base H G M b : ℕ) : endAddress base H G M b = base+endAddress 0 H G M b := by
  simp only [endAddress,DescentResetHaloBroadcast.endAt,Nat.zero_add,Nat.add_assoc]

theorem amount (base H G M b : ℕ) (banks : Fin 4→Bank) (j : Fin 4) :
    (expr base H G M b banks j).work=25 := rfl

theorem names (w base H G M b : ℕ) :
    DescentStaticWordColumn.names (program w base H G M b)=15*(count H G M b+1) :=
  DescentStaticWordColumn.names_mount ..

theorem cheap (w base H G M b : ℕ) : CheapCode (program w base H G M b) :=
  DescentStaticWordColumn.cheap w base (DescentResetHaloBroadcast.literal b G M (id : Fin H→Fin H)) (count H G M b)

theorem fits {w base H G M b : ℕ} (banks : Fin 4→Bank)
    (old : ∀j,(banks j).Fits w base) (room : endAddress base H G M b < 2^w) (j : Fin 4) :
    (expr base H G M b banks j).Fits w (endAddress base H G M b) :=
  DescentResetHaloBroadcast.schema_fit (banks j) base H G M b (old j) room

/-- Each scalar column has one entry for every current compact host, including a
zero for an absent peer. All four packed sources read the same installed page.
The active group range determines the zero padding of the last packed word. -/
theorem run {w base H G M b : ℕ} (banks : Fin 4→Bank) (m : Memory w)
    (joint : Fin 4→Fin H→ℕ) (short : ∀j h,joint j h < 2^b)
    (old : ∀j,(banks j).Fits w base) (extent : ∀j,H ≤ (banks j).size)
    (stored : ∀j h,m ((banks j).base+h.val)=(joint j h : Word w))
    (room : endAddress base H G M b < 2^w) :
    (program w base H G M b).Exec m (image base H G M b m) (ticks H G M b) ∧
    (∀j,Source (expr base H G M b banks j)
      (fun h (_ : Fin G) => (⟨joint j h,short j h⟩ : Cell b)) M (image base H G M b m)) ∧
    (∀a,a<base ∨ base+count H G M b≤a → image base H G M b m a=m a) ∧
    CheapCode (program w base H G M b) := by
  let value (j : Fin 4) (h : Fin H) : Cell b := ⟨joint j h,short j h⟩
  have one (j : Fin 4) := DescentResetHaloBroadcast.run (banks j) base (id : Fin H→Fin H)
    (value j) m (old j) (extent j) (stored j) room
  exact ⟨(one 0).1,fun j=>(one j).2.1,(one 0).2.2.1,@cheap w base H G M b⟩

end
end Hierarchy.DescentResetPeerJointBroadcast

end OAI
