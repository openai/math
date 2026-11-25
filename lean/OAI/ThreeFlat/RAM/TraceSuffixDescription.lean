import OAI.ThreeFlat.RAM.TraceSuffixPrepared
import OAI.ThreeFlat.RAM.PreparedMatrixTrace

namespace OAI
/-! # A native read from the self-description returns one genuine H trace pin -/

namespace ThreeFlat.RAM.TraceSuffixOracle

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPrelude Diagonal Diagonal.TraceBitHeader
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [Field F] {w W p r k p' r' k' S g : ℕ} (I : Image F w)

def locations (w p k p' k' description parameters table codeBase : ℕ) : Locations :=
  ⟨description,parameters,table,codeBase,SelfAdvice.textSize w p k,SelfAdvice.textSize w p' k'⟩

theorem read_description (tick : Machine w p r k) (H : Machine w p' r' k') (extra : Fin g → Bool)
    (room : SelfAdvice.Fits w p k p' k' g I.advice) (db pb tb codeBase : ℕ)
    (m : ℕ → ℕ) (par : Fin I.parameters → Bool) (x y : Fin I.endpointBits → Bool)
    (t : Fin S) (suffix : 2*I.endpointBits≤t.val) (hw : 0<w)
    (mount : Mounted I (locations w p k p' k' db pb tb codeBase) m
      (SelfAdvice.description tick H extra) par)
    : read (layout I (locations w p k p' k' db pb tb codeBase)) m t.val =
      (advicePins codeBase (NativeTrace.executable H)
        (I.tapeBit (SelfAdvice.description tick H extra) x y par) t).toNat := by
  let a := locations w p k p' k' db pb tb codeBase
  let D := SelfAdvice.description (q:=I.advice) tick H extra
  have text (j : Fin a.textSize) : m (a.description+a.textOffset+j.val) =
      (SelfAdvice.hText room D j).toNat := by
    let v : Fin I.advice := ⟨a.textOffset+j.val,by have := j.isLt;have := room.room;dsimp [a,locations] at *;omega⟩
    simpa only [v,a,locations,D,SelfAdvice.hText,Nat.add_assoc] using mount.description v
  have e := header_correct I a m D par x y mount (SelfAdvice.hText room D)
    text t suffix hw
  have bits := congrArg Bool.toNat (congrFun
    (NativeTrace.executable_from_description (S:=S) tick H extra room codeBase (I.tapeBit D x y par)) t)
  exact e.trans (by simpa only [a,locations,D] using bits)


end ThreeFlat.RAM.TraceSuffixOracle

end OAI
