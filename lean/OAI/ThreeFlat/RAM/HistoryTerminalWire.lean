import OAI.ThreeFlat.RAM.HistoryTerminalTape
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.RAM.TickDecodedWire

namespace OAI
/-! # Real boundary labels at the selected terminal map addresses -/

namespace ThreeFlat.RAM.HistoryTerminalTape

open Diagonal Diagonal.HistoryContraction Diagonal.PhysicalStage Diagonal.TickAuxiliary
open Diagonal.ApproximateImage
open scoped BigOperators

variable {d l : ℕ} (A : State d l)

theorem ordered_address {u teams hidden hist a : ℕ} (q nt ns np capacity : ℕ)
    (room : 1+hist+A.widthSum≤a) (T : Root) (mem : ℕ→ℕ) (localHalf : ℕ)
    (i : Fin A.edgeCount) (j : Fin (A.wireWidth i))
    (origin : T.wireStart=(TickPhysicalABI.mounted u a teams capacity q nt ns np).oldAux+1+hist)
    (number : (half T mem localHalf).edge=i.val)
    («prefix» : mem (T.wirePrefix+i.val)=∑ k : Fin i.val,A.wireWidth (Fin.castLE i.isLt.le k)) :
    source T mem localHalf+j.val=
      BitLayout.sourceAddress (n:=hidden) (.pin (TickSelectedPins.wire q nt ns np room (A.bitAddress i j))) :=
  shared_address q nt ns np capacity room T mem localHalf j.val (A.bitAddress i j) origin
    (by rw [number,«prefix»,A.bitAddress_val])

theorem read_label {F : Type*} [CommSemiring F] {S : Shape} {a q nt ns np : ℕ}
    (P : Plan F S) (E : P.Codes) (bits : P.History→ℕ) (L : Layout a)
    (v : Plan.Terminal P bits) (n : bits v.1=A.widthSum)
    (room : (P.write E v.1).length+bits v.1≤L.wiresEnd-1)
    (D : Fin q→Bool) (team : Fin nt→Bool) (step : Fin ns→Bool) (params : Fin np→Bool)
    (oa na oc nc : Fin a→Bool) (ok : decode P E bits L oa=some v)
    (i : Fin A.edgeCount) (j : Fin (A.wireWidth i)) :
    let fit : 1+(P.write E v.1).length+bits v.1≤a := by
      have := L.marker
      have := L.ordered.trans L.fits
      omega
    fields D team step params oa na oc nc (TickSelectedPins.wire q nt ns np fit ((A.bitAddress i j).cast n.symm)) =
      ((A.boundaryBits.symm (fun z => v.2 (z.cast n.symm))) (A.wireOrder.symm i)).val.testBit j.val := by
  intro fit
  rw [A.bitAddress_read]
  exact TickSelectedPins.decoded_wire P E bits L v room D team step params oa na oc nc ok _

end ThreeFlat.RAM.HistoryTerminalTape

end OAI
