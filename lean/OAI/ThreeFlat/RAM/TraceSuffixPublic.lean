import OAI.ThreeFlat.RAM.TraceSuffixFixedFit
import OAI.ThreeFlat.RAM.TraceSuffixDescription
import OAI.ThreeFlat.RAM.TraceSuffixParameterMount
import OAI.ThreeFlat.Diagonal.TracePreparedSuffix

namespace OAI
/-! # Public-at-index API for native scalar source substitution -/

namespace ThreeFlat.RAM.TraceSuffixOracle

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPrelude Diagonal Diagonal.TraceBitHeader DescriptorExpr
open scoped Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {w W p r k p' r' k' K g : ℕ} (I : Image F w)

theorem fixedOracle_eval_publicAt (tick : Machine w p r k) (H : Machine w p' r' k') (extra : Fin g → Bool)
    (room : SelfAdvice.Fits w p k p' k' g I.advice) (db pb tb codeBase : ℕ)
    (slots : Fin 11 → Fin K) (data : Fin K → Word W) (m : Memory W) (par : Fin I.parameters → Bool)
    (t : ℕ) (suffix : 2*I.endpointBits≤t) (hw : 0<w)
    (mount : Mounted I (locations w p k p' k' db pb tb codeBase) (fun j => (m j).val)
      (SelfAdvice.description tick H extra) par)
    (params : ∀ i, data (slots i)=((layout I (locations w p k p' k' db pb tb codeBase)).fields i : Word W))
    (zero : (m 0).val=0) (one : (m 1).val=1)
    (fit : Bounds W (layout I (locations w p k p' k' db pb tb codeBase)) t) :
    (fixedOracle W K slots).eval data m
      (fun _ => (t : Word W)) =
    ((publicAt I codeBase (NativeTrace.executable H) (SelfAdvice.description tick H extra) par t).toNat : Word W) := by
  let i : Fin (t+1) := ⟨t,Nat.lt_succ_self _⟩
  rw [fixedOracle_eval _ slots data m t fit params zero one]
  exact congrArg (fun n : ℕ => (n : Word W)) (read_description I tick H extra room db pb tb codeBase
    (fun j => (m j).val) par (fun _ => false) (fun _ => false) i suffix hw mount)


end ThreeFlat.RAM.TraceSuffixOracle

end OAI
