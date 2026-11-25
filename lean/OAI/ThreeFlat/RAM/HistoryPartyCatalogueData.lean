import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # The public header and port rows of a history party -/

namespace ThreeFlat.RAM.HistoryPartyHeader

/-- The fixed grid/party catalogue carries these seven bounded integers. Its
selector and tile pages are the actual shared bounded lookup tables. -/
structure Kind where
  ports : ℕ
  letters : ℕ
  codeBits : ℕ
  tileHead : ℕ
  digit : ℕ
  tilePage : ℕ
  selectorPage : ℕ

def Kind.words (v : Kind) : Fin 7→ℕ := ![v.ports,v.letters,v.codeBits,v.tileHead,v.digit,v.tilePage,v.selectorPage]

end ThreeFlat.RAM.HistoryPartyHeader

namespace ThreeFlat.RAM.HistoryPortCatalogue
open scoped BigOperators Classical
noncomputable section

/-- Constant-size description of one base tile at a party. The raw port
number includes side for refresh loops. The first column of the native
demand-digit table is a local ordinal in the demand scan below. -/
structure Page (n e : ℕ) where
  demand : Fin n→ℕ
  supply : Fin e→ℕ
  baseWidth : Fin n→ℕ
  anchor : ℕ

variable {n e : ℕ}

def Page.digits (G : Page n e) := ∑ u,G.baseWidth u

def Page.decode (G : Page n e) (i : Fin G.digits) : Σ u,Fin (G.baseWidth u) :=
  finSigmaFinEquiv.symm i

def stride (D E H : ℕ) := 3+2*D+E+2*H
def demandBase := 3
def supplyBase (D : ℕ) := 3+2*D
def headerBase (D E : ℕ) := supplyBase D+E

def Page.at (G : Page n e) (D E : ℕ) (i : ℕ) : ℕ :=
  if i=0 then n else if i=1 then e else if i=2 then G.anchor else
    if i < supplyBase D then
      let j := (i-demandBase)/2
      if v : j<n then if (i-demandBase)%2=0 then G.demand ⟨j,v⟩ else G.baseWidth ⟨j,v⟩ else 0
    else if i<headerBase D E then
      if h : i-supplyBase D<e then G.supply ⟨_,h⟩ else 0
    else let k := i-headerBase D E
         if h : k/2<G.digits then
           let x := G.decode ⟨k/2,h⟩
           if k%2=0 then x.1.val else x.2.val
         else 0

end
end ThreeFlat.RAM.HistoryPortCatalogue

end OAI
