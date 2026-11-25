import OAI.Hierarchy.DescentDonorTrimCode
import OAI.Hierarchy.DescentPackedDonorEncoding
import OAI.Hierarchy.DescentSixPartyGadget
import OAI.Hierarchy.DescentSixPartySeed

namespace OAI
/-! # The fixed lookup on an encoded ordinary donor -/
namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup DescentHostDirectory SiteDecode DescentSixParty
open scoped Classical Fin.CommRing
noncomputable section
/-- One output holds both equality flags plus an unsigned whole-grain count. -/
def cell {c : ℕ} (before after : Bool) (units : Cell c) : Cell (2+c) :=
  pair 2 c (pair 1 1 (tag before,tag after),units)

def samePre {c : ℕ} (v : Cell (2+c)) := flag ((pair 1 1).symm ((pair 2 c).symm v).1).1
def samePost {c : ℕ} (v : Cell (2+c)) := flag ((pair 1 1).symm ((pair 2 c).symm v).1).2
def grains {c : ℕ} (v : Cell (2+c)) : ℕ := ((pair 2 c).symm v).2.val
def score {c : ℕ} (v : Cell (2+c)) := if samePost v then grains v else 0
def preScore {c : ℕ} (v : Cell (2+c)) := if samePre v then grains v else 0

/-- Both host names are expressed as slots in one bounded neighborhood.
The remaining bits are the original within-position venue number and hub flag. -/
def endpoint (loc a : ℕ) : (Cell loc×Cell 1)×Cell a ≃ Cell (loc+1+a) :=
  ((pair loc 1).prodCongr (Equiv.refl _)).trans (pair (loc+1) a)

def input (loc a c : ℕ) :
    (Cell (loc+1+a) × Cell (loc+1+a)) × Cell c ≃ Cell ((loc+1+a)+(loc+1+a)+c) :=
  ((pair (loc+1+a) (loc+1+a)).prodCongr (Equiv.refl _)).trans (pair _ c)

def output (k g slots loc a c : ℕ) (word : Cell ((loc+1+a)+(loc+1+a)+c)) : Cell (2+c) :=
  let raw:=(input loc a c).symm word
  let s:=(endpoint loc a).symm raw.1.1
  let t:=(endpoint loc a).symm raw.1.2
  let nearby:=s.1.1=t.1.1
  cell (decide (nearby ∧ s.2=t.2))
    (decide (nearby ∧ trim k g slots (flag s.1.2) s.2.val=trim k g slots (flag t.1.2) t.2.val)) raw.2

variable {a loc c : ℕ}
local notation "E" => Cell (loc+1+a)
/-- Three old sites suffice for all six motif parties: the matched thick source,
its old target, and the old thin target. Each token contains its bounded host
ordinal, previous hub bit and local within-position pack name. -/
def motif (k g slots : ℕ) (layout : Bool) (old : Fin 3→E) (sizes : Fin 8→Cell c)
    (s : Fin 8) : Cell (2+c) :=
  output k g slots loc a c (input loc a c
    ((old (cluster layout (supplySrc s)), old (cluster layout (supplyDst s))),sizes s))

def oldCable (k g slots : ℕ) (picked : Bool) (src dst : E) (units : Cell c) : Cell (2+c) :=
  if picked then cell true true units else output k g slots loc a c (input loc a c ((src,dst),units))

def report (k g slots : ℕ) (d : Donor loc a c) : Fin 11→Cell (2+c) :=
  let head:=if d.live then oldCable k g slots d.picked d.left d.right d.oldUnits else 0
  let arms (_:Fin 2):=if d.first then cell true true d.armUnits else 0
  let wires (j:Fin 8):=if d.first then motif k g slots d.layout d.anchors d.supplyUnits j else 0
  Fin.cons head (Fin.append arms wires)

def donorROM (k g slots loc a c : ℕ) (x : Cell (bundleBits loc a c)) : Cell ((2+c)*11) :=
  encode (2+c) 11 (report k g slots (unpackDonor x))


end
end Hierarchy.DescentRawCablePanel

end OAI
