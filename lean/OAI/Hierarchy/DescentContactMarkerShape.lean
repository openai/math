import OAI.Hierarchy.DescentStaticUnary

namespace OAI
/-! # Extracting the remote shape from an issued sender marker -/
namespace Hierarchy.DescentContactMarkerShape
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def shape (shapes b t : ℕ) (x : Cell b) (_ : Cell 0) : Cell t := ((x.val - 1) % shapes : ℕ)
def flag (b t : ℕ) (x : Cell b) (_ : Cell 0) : Cell t:=if x=0 then 0 else 1
def pages (shapes b t M : ℕ):=binary (shape shapes b t) M
def high (b M root : ℕ):=root+2*2^(b*M)
def program (shapes b t M root w : ℕ):=mount (pages shapes b t M) (b*M) w root
def memory {w : ℕ} (shapes b t M root : ℕ) (m : Memory w):=after (pages shapes b t M) (b*M) root m
def ticks (b M : ℕ):=4+10*(2*2^(b*M))
def port (shapes b t M root : ℕ) (src : Expr):=DescentStaticUnary.query (shape shapes b t) M root src

theorem read {H G M w : ℕ} (shapes b t root : ℕ) (m : Memory w) (room : high b M root<2^w) :
    (program shapes b t M root w).Exec m (memory shapes b t M root m) (ticks b M) ∧
      (∀src : Expr,∀v : Fin H→Fin G→Cell b,src.Fits w root→Source src v M m→
        (port shapes b t M root src).Fits w (high b M root) ∧ Source (port shapes b t M root src)
          (fun h g=>shape shapes b t (v h g) 0) M (memory shapes b t M root m)) ∧
      (∀z,z<root ∨ high b M root≤z→memory shapes b t M root m z=m z) ∧ CheapCode (program shapes b t M root w):=by
  exact DescentStaticUnary.read (shape shapes b t) (by simp [shape]) root m room

theorem any {w : ℕ} (shapes b t M root : ℕ) (m : Memory w) (room : high b M root<2^w) :
    (program shapes b t M root w).Exec m (memory shapes b t M root m) (ticks b M) ∧ CheapCode (program shapes b t M root w) ∧
    ∀z,z<root ∨ high b M root≤z→memory shapes b t M root m z=m z:=by
  have e:=read (H:=0) (G:=0) shapes b t root m room
  exact ⟨e.1,e.2.2.2,e.2.2.1⟩

theorem exact_shape {shapes b t i j : ℕ} {x : Cell b} (marker : x.val=1+i*shapes+j)
    (member_ : j<shapes) (digit : j<2^t) : (shape shapes b t x 0).val=j:=by
  have drop : x.val-1=i*shapes+j:=by omega
  have decoded : (x.val - 1) % shapes = j := by
    rw [drop,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt member_]
  unfold shape
  rw [decoded]
  exact Fin.val_cast_of_lt digit

end
end Hierarchy.DescentContactMarkerShape

end OAI
