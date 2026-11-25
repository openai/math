import OAI.ThreeFlat.RAM.TickSelectedPins
import OAI.ThreeFlat.Diagonal.TickSharedStates

namespace OAI
/-! # The selected root reads the live wire assignment of the decoded shared history -/

namespace ThreeFlat.RAM.TickSelectedPins
open Diagonal.ApproximateImage Diagonal.TickAuxiliary Diagonal.HistoryContraction

variable {F : Type*} [CommSemiring F] {S : Shape} {a q nt ns np : ℕ}

theorem decoded_wire (P : Plan F S) (E : P.Codes) (bits : P.History → ℕ) (L : Layout a)
    (v : Plan.Terminal P bits) (room : (P.write E v.1).length + bits v.1 ≤ L.wiresEnd-1)
    (D : Fin q → Bool) (team : Fin nt → Bool) (step : Fin ns → Bool) (params : Fin np → Bool)
    (oa na oc nc : Fin a → Bool) (ok : decode P E bits L oa = some v) (i : Fin (bits v.1)) :
    let fit : 1+(P.write E v.1).length+bits v.1 ≤ a := by
      have := L.marker
      have := L.ordered.trans L.fits
      omega
    fields D team step params oa na oc nc (wire q nt ns np fit i) = v.2 i := by
  intro fit
  rw [wire_read]
  let h := P.write E v.1
  have hi := i.isLt
  have hi' : h.length+i.val < L.wiresEnd-1 := by dsimp [h]; omega
  have eq := Plan.encode_decode P E bits (L.wiresEnd-1) (List.ofFn (project L oa).history) v ok
  have atIndex := congrArg (fun l : List Bool => l[h.length+i.val]?) eq
  change (h ++ (List.ofFn v.2 ++ _))[h.length+i.val]? = (List.ofFn (project L oa).history)[h.length+i.val]? at atIndex
  rw [List.getElem?_append_right (by omega : h.length ≤ h.length+i.val),
    Nat.add_sub_cancel_left,List.getElem?_append_left (by simp)] at atIndex
  simp only [List.getElem?_ofFn,dite_eq_left hi,dite_eq_left hi',Option.some.injEq] at atIndex
  refine Eq.trans ?_ atIndex.symm
  apply congrArg oa
  apply Fin.ext
  change 1+h.length+i.val = 1+(h.length+i.val)
  omega

end ThreeFlat.RAM.TickSelectedPins

end OAI
