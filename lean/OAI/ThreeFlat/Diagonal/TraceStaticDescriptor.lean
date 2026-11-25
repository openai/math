import OAI.ThreeFlat.Diagonal.TraceStaticTable
import OAI.ThreeFlat.Diagonal.TraceGuardless

namespace OAI
/-! # Dense record descriptors for a row of the universal trace -/

namespace ThreeFlat.Diagonal.TraceStaticRow

open Computability.VPVNP BurstRAM
variable {F : Type*} [CommRing F] [Fintype F] {w p r k f S d : ℕ}

theorem network_eq_guarded (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k d : ℕ) :
    network hF hw hp base st hs hf r k d =
      GuardedNetwork.network (e:=0) (gateTable hF hw hp base f st r k d)
        (fun v i => portSource hw hs hf base v ((Fintype.equivFin (Port w p r k d)).symm i))
        (fun _ => Fin.elim0) (fun _ => Fin.elim0) :=
  (GuardedNetwork.zero_guards ..).symm

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
