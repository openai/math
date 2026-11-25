import OAI.Hierarchy.DescentParallelIncidentStream

namespace OAI
/-! # Produce each directed local position from all neighbors by the paid short comparison scan -/
namespace Hierarchy.DescentParallelBase.Incidence
open DescentSharedCableNames DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {U E : Type} [DecidableEq U] [Fintype E] {n H G M w cap c q k : ℕ} {B : Ends U n} (C : Blocks B E)

structure Census (C:Blocks B E) (q k cap c:ℕ) where
  addr : ∀v,Local C v↪Fin c
  source : ∀v,Local C v→Fin q
  ticket : ∀v,Local C v→Fin k
  mass : ∀v,Local C v→Fin (cap+1)
  weight : ∀v e,(mass v e).val=C.count e.val
  chronology : ∀v e f,C.first e.val<C.first f.val ↔ source v e<source v f ∨ source v e=source v f ∧ ticket v e<ticket v f

variable (Z:Census C q k cap c)

def entry (v:U) (e:Local C v):=row (Z.source v e) (Z.ticket v e) (Z.mass v e)
def items (hosts:Fin H→Fin G→Option U) (j:Fin c) (v:Fin H) (g:Fin G):=(hosts v g).bind (fun h=>place (Z.addr h) (entry C Z h) j)

def pos (fit:∀u,(B.incident u).card≤cap) (v:U) (e:Local C v):=(B.position fit v (candidate C v e ⟨0,e.property.1⟩)).val

theorem at_parent (hosts:Fin H→Fin G→Option U) (fit:∀u,(B.incident u).card≤cap) (v:Fin H) (g:Fin G) (u:U) (hit:hosts v g=some u) (e:Local C u):
    (∑i,Stream.qty (items C Z hosts (Z.addr u e) v g) (items C Z hosts i v g))=pos C fit u e:=by
  simp only [items, hit, Option.bind_some, place_at]
  unfold entry pos
  exact streamed C u fit (Z.addr u) (Z.source u) (Z.ticket u) (Z.mass u) (Z.weight u) (Z.chronology u) e

theorem capacity (hosts:Fin H→Fin G→Option U) (fit:∀u,(B.incident u).card≤cap) (j:Fin c) (v:Fin H) (g:Fin G):
    (∑i,Stream.qty (items C Z hosts j v g) (items C Z hosts i v g))<2^(Packed.bits cap):=by
  cases eqn:hosts v g with
  | none=>simp [items,eqn,Stream.qty]
  | some u=>
    by_cases live:∃e,Z.addr u e=j
    · obtain ⟨e,rfl⟩:=live;rw [at_parent C Z hosts fit v g u eqn e]
      exact (B.position fit u (candidate C u e ⟨0,e.property.1⟩)).isLt.trans_le
        ((Nat.le_succ cap).trans (Nat.le_pow_clog (by decide) _))
    · have none:=place_empty (Z.addr u) (entry C Z u) j (not_exists.mp live)
      simp [items,eqn,none,Stream.qty]

/-- The paid output is the entire physical source-rank word, indexed by the
same local parent roster independently at either observation endpoint. -/
theorem run (hosts:Fin H→Fin G→Option U) (fit:∀u,(B.incident u).card≤cap) (j:Fin c) (T:Tables) (field:Fin c→Expr) (out:Bank) (m:Memory w)
    (rooms:∀i,DescentPackedZip.Fits T (field j) (field i) (PackedBase.width 1 (q*k) cap) (PackedBase.width 1 (q*k) cap) M out.base w)
    (pins:Static T (Stream.compareWord 1 (q*k) cap) M m)
    (old:∀i,Source (field i) (fun h g=>PackedBase.word (items C Z hosts i h g)) M m) (space:out.base+H*chunks G M<2^w):
    let cells:=items C Z hosts
    let f:=Stream.instruction T (field j) field
    let done:=image out.base (H*chunks G M) f m
    (scan w out.base (H*chunks G M) f).Exec m done (4+H*chunks G M*(2*f.work+4)) ∧
    Reads out (Stream.totalWord (cells j) cells (capacity C Z hosts fit j)) M done ∧ CheapCode (scan w out.base (H*chunks G M) f):=
  Stream.run T (field j) field out m rooms _ _ (capacity C Z hosts fit j) pins (old j) old space

end
end Hierarchy.DescentParallelBase.Incidence

end OAI
