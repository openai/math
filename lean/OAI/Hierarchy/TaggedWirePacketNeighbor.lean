import OAI.Hierarchy.TaggedWirePacketScan
import OAI.Hierarchy.TaggedWidePortPartition
import OAI.LinearAlgebra.SpectralBooks.ChordGraph.BoundedPatchReplacementWiring
import Mathlib.Data.List.Forall2

namespace OAI
/-! # Look up the gathered physical chord by its reached site's genuine original role slots -/
noncomputable section
namespace Hierarchy.WireTelescope.PacketNeighbor
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM Tagged
open scoped Classical Fin.CommRing
variable {S D K W : ℕ} {s : Fin S} {total : (portGraph S).Port s→ℕ}

def other (p : (portGraph S).Port s) := (portGraph S).vertex p.1.1 (!p.1.2)

theorem other_injective : Function.Injective (other (s:=s)) := by
  rintro ⟨⟨⟨⟨a,b⟩,ab⟩,f⟩,atA⟩ ⟨⟨⟨⟨c,d⟩,cd⟩,g⟩,atB⟩ eq
  apply Subtype.ext
  change a<b at ab
  change c<d at cd
  cases f <;> cases g <;>
    simp only [other,portGraph,PortGraph.vertex,Bool.not_true,Bool.not_false] at atA atB eq
  all_goals first | (subst_vars;rfl) | (exfalso;omega)

variable (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K total)

/-- Vacant original degree positions are silent, including those on a
candidate bank whose previous positive port has disappeared. -/
def amount (q : Fin D) := (parts.owner q).elim 0 (fun _=>parts.width q)
def word (q : Fin D) (target : Fin S) : ℕ := (parts.owner q).elim 0
  (fun p=>if 0<parts.width q ∧ other p=target then 1 else 0)
def index (target : Fin S) := (List.ofFn (fun q=>word parts q target)).idxOf 1

theorem word_one (q : Fin D) (target : Fin S) :
    word parts q target=1 ↔ ∃p,parts.owner q=some p ∧ 0<parts.width q ∧ other p=target := by
  cases h:parts.owner q <;> simp [word,h]

theorem found_live (p : (portGraph S).Port s) (live : 0<total p) :
    ∃q : Fin D,q.val=index parts (other p) ∧ parts.owner q=some p ∧ 0<parts.width q := by
  obtain ⟨u,owner,j,_⟩:=parts.covers p ⟨0,live⟩
  have hit:= (word_one parts u _).mpr ⟨p,owner,Nat.zero_lt_of_lt j.isLt,rfl⟩
  let xs:=List.ofFn (fun q=>word parts q (other p))
  have mem : 1∈xs:=List.mem_ofFn.mpr ⟨u,hit⟩
  have bound:=List.idxOf_lt_length_of_mem mem
  let q : Fin D:=⟨xs.idxOf 1,by simpa [xs] using bound⟩
  have selected : word parts q (other p)=1 := by
    simpa only [xs,q,List.getElem_ofFn] using (List.getElem_idxOf bound)
  obtain ⟨p',own,pos,eq⟩:=(word_one parts q _).mp selected
  exact ⟨q,rfl,own.trans (congrArg some (other_injective eq)),pos⟩

theorem found (p : (portGraph S).Port s) (live : 0<total p) :
    ∃q : Fin D,q.val=index parts (other p) ∧ parts.owner q=some p := by
  obtain ⟨q,atQ,own,_⟩:=found_live parts p live
  exact ⟨q,atQ,own⟩

theorem index_le (target : Fin S) : index parts target≤D := by
  simpa [index] using List.idxOf_le_length (a:=1) (l:=List.ofFn fun q=>word parts q target)

def compare (width neighbor target : Expr) : Expr :=
  .branch .eq width (.lit 0) (.lit 0) (.branch .eq neighbor target (.lit 1) (.lit 0))

def selectExpr (width neighbor : Fin D→Expr) (target : Expr) : Expr :=
  PacketScan.first (.lit 1) (List.ofFn (fun i=>compare (width i) (neighbor i) target))

theorem select_eval (width neighbor : Fin D→Expr) (seek : Expr) (target : Fin S)
    (mem : Memory W) (row : Word W) (one : 1<2^W) (sites : S≤2^W)
    (atTarget : seek.eval mem row=(target.val : Word W)) (fits : ∀i,amount parts i<2^W)
    (atWidth : ∀i,(width i).eval mem row=(amount parts i : Word W))
    (atSite : ∀i p,parts.owner i=some p→0<parts.width i→(neighbor i).eval mem row=((other p).val : Word W)) :
    (selectExpr width neighbor seek).eval mem row=(index parts target : Word W) := by
  have read (q : Fin D) : (compare (width q) (neighbor q) seek).eval mem row=(word parts q target : Word W) ∧
        word parts q target<2^W := by
    rw [compare,PacketScan.eq_select mem row _ _ _ _ (atWidth q) rfl (fits q) (Nat.two_pow_pos W)]
    cases h:parts.owner q with
    | none=>simp [amount,word,h,Expr.eval]
    | some p=>
      simp only [amount,word,h,Option.elim_some]
      by_cases used:parts.width q=0
      · simp [used,Expr.eval]
      · have pos:=Nat.pos_of_ne_zero used
        rw [ite_eq_right used,PacketScan.eq_select mem row _ _ _ _ (atSite q p h pos) atTarget
          ((other p).isLt.trans_le sites) (target.isLt.trans_le sites)]
        by_cases hit:other p=target
        · simp [hit,pos,Expr.eval,one]
        · simp [hit,pos,Fin.ext_iff.not.mp hit,Expr.eval]
  apply PacketScan.first_eval mem row (.lit 1) rfl one
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro j ha hb
  simpa using read ⟨j,by simpa using ha⟩

end Hierarchy.WireTelescope.PacketNeighbor

namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM Tagged
open scoped Fin.CommRing
variable {W D K S : ℕ} {s : Fin S} {total : (portGraph S).Port s→ℕ} (mem : Memory W) (row : Word W)
    (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K total) (width nbr : Fin D→Expr)

structure NeighborReads : Prop where
  one : 1<2^W
  fits : ∀q,PacketNeighbor.amount parts q<2^W
  widthAt : ∀q,(width q).eval mem row=(PacketNeighbor.amount parts q : Word W)
  siteAt : ∀q p,parts.owner q=some p→0<parts.width q→(nbr q).eval mem row=((PacketNeighbor.other p).val : Word W)

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
