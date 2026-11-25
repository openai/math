import OAI.Hierarchy.DescentReachedAtomHaloRAM
import OAI.Hierarchy.DescentPackedNodeDigit

namespace OAI
/-! # Native scalar operands from a whole previous book or an actual born-field bank -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {a K cap H G M w P r t : ℕ}

/-- The branch is by the fixed candidate ordinal and compiles once. Only
its short old-scalar projection requires a lookup after the actual donor
rack has been fetched. The born case reads the newly published role word. -/
def operand (ports : Ports P) (old : Fin r→Bank) (fresh : Fin r→Fin cap→Fin 6→Bank) (dict : Fin K→Bank)
    (H : ℕ) (rack : Fin P) (b : Fin r) (j : Fin (K+cap*6)) : Expr :=
  (finSumFinEquiv.symm j).elim (fun t=>project dict (peerExpr ports (old b) H rack) t)
    (fun u=>let x:=finProdFinEquiv.symm u;peerExpr ports (fresh b x.1 x.2) H rack)

def item (old : Fin r→Fin H→Fin G→Cell (a*K)) (fresh : Fin r→Fin cap→Fin 6→Fin H→Fin G→Cell a)
    (b : Fin r) (j : Fin (K+cap*6)) (h : Fin H) (g : Fin G) :=
  (finSumFinEquiv.symm j).elim (fun t=>take t (old b h g)) (fun u=>let x:=finProdFinEquiv.symm u;fresh b x.1 x.2 h g)

theorem source (P_ : Ports P) (old : Fin r→Bank) (fresh : Fin r→Fin cap→Fin 6→Bank) (dict : Fin K→Bank) (out : ℕ) (m : Memory w)
    (next : Fin H→Fin P→Option (Fin H)) (wired : Mounted P_ next m G M)
    (past : Fin r→Fin H→Fin G→Cell (a*K)) (born : Fin r→Fin cap→Fin 6→Fin H→Fin G→Cell a)
    (prior : ∀b,Reads (old b) (past b) M m) (formed : ∀b i j,Reads (fresh b i j) (born b i j) M m)
    (access : ∀b,Accessible P_ (old b) H G M w out) (newAccess : ∀b i j,Accessible P_ (fresh b i j) H G M w out)
    (fit : ∀j,(dict j).Fits w out ∧ (dict j).bits=(a*K)*M) (tables : ∀j (x : Cell ((a*K)*M)),m ((dict j).base+x.val)=((DescentSIMDLookup.table (M:=M) (take (a:=a) j) x).val:Word w))
    (rack : Fin P) (b : Fin r) (j : Fin (K+cap*6)) :
    Source (operand P_ old fresh dict H rack b j) (fun h g=>(next h rack).elim 0 (fun u=>item past born b j u g)) M m :=by
  obtain ⟨key,rfl⟩:=finSumFinEquiv.surjective j;rcases key with node|role
  · have prev:=peerSource P_ (old b) out (access b) next m wired (past b) (prior b) rack
    have get:=fetched dict _ node out m _ prev (fit node).1 (fit node).2 (tables node)
    simp only [operand,item,Equiv.symm_apply_apply,Sum.elim_inl]
    convert get using 1
    funext h g;cases next h rack <;> simp [take_zero]
  · obtain ⟨⟨s,who⟩,rfl⟩:=finProdFinEquiv.surjective role
    simpa only [operand,item,Equiv.symm_apply_apply,Sum.elim_inr] using peerSource P_ (fresh b s who) out (newAccess b s who) next m wired (born b s who) (formed b s who) rack

variable {D k n mb : ℕ}
local notation "P₀" => breadth D
local notation "donors" => (breadth D*2^k)
local notation "actors" => DescentPackedActorMask.actors donors cap
local notation "nodes" => DescentPackedActorMask.nodes donors K cap

/-- Complete real compaction directly from previously packed whole-book
words and from the new six-party word (each through the physical halo). -/
theorem run_books (T : TablesAt) (gates : Fin nodes→Tables) (ports : Ports P₀) (oldBank : Fin (2^k)→Bank) (bornBank : Fin (2^k)→Fin cap→Fin 6→Bank) (dict : Fin K→Bank)
    (want addr counts : Expr) (out K' : ℕ) (m : Memory w) (walks : Fin H→Fin P₀→Option (Fin H))
    (wired : Mounted ports (DescentSortedRoster.indexed walks) m G M)
    (past : Fin (2^k)→Fin H→Fin G→Cell (a*K)) (born : Fin (2^k)→Fin cap→Fin 6→Fin H→Fin G→Cell a)
    (prior : ∀b,Reads (oldBank b) (past b) M m) (formed : ∀b i j,Reads (bornBank b i j) (born b i j) M m)
    (access : ∀b,Accessible ports (oldBank b) H G M w out) (newAccess : ∀b i j,Accessible ports (bornBank b i j) H G M w out)
    (fit : ∀j,(dict j).Fits w out ∧ (dict j).bits=(a*K)*M) (tables : ∀j (x : Cell ((a*K)*M)),m ((dict j).base+x.val)=((DescentSIMDLookup.table (M:=M) (take (a:=a) j) x).val:Word w))
    (wanted : Fin H→Fin G→Cell n) (address : Fin H→Fin G→Fin actors→Cell n) (count : Fin H→Fin G→Fin donors→Cell mb)
    (wants : Source want wanted M m) (locations : Source addr (fun h g=>encode n actors (address h g)) M m)
    (tallies : Source counts (fun h g=>encode mb donors (count h g)) M m)
    (targetRoom : DescentPackedZip.Fits T.targets want addr n (n*actors) M out w)
    (actorRoom : DescentPackedZip.Fits T.actors (T.targets.read want addr) counts (1*actors) (mb*donors) M out w)
    (fieldRoom : Gather.Bounds (w:=w) (d:=a) (M:=M) gates (fun j=>operand ports oldBank bornBank dict H (bookRoot D k K cap j) (bookBlock D k K cap j) (bookItem D k K cap j)) out)
    (resultRoom : DescentPackedZip.Fits T.emitted (masked T want addr counts) (Gather.assembly gates (fun j=>operand ports oldBank bornBank dict H (bookRoot D k K cap j) (bookBlock D k K cap j) (bookItem D k K cap j))) (1*nodes) (a*nodes) M out w)
    (room : out+H*chunks G M<2^w) (targetROM : Static T.targets (DescentPackedActorMask.target n actors) M m)
    (actorROM : Static T.actors (DescentPackedActorMask.occupied donors K cap mb) M m) (fieldROM : ∀j,Static (gates j) (Gather.setField (d:=a) j) M m)
    (resultROM : Static T.emitted (DescentPackedLocalAtoms.pack a nodes K') M m) :
    let src:=fun j=>operand ports oldBank bornBank dict H (bookRoot D k K cap j) (bookBlock D k K cap j) (bookItem D k K cap j)
    let e:=resultExpr T gates src want addr counts;let state:=image out (H*chunks G M) e m
    let mask:=fun h g=>DescentPackedActorMask.occupied donors K cap mb (DescentPackedActorMask.target n actors (wanted h g) (encode n actors (address h g))) (encode mb donors (count h g))
    let field:=fun h g j=>(DescentSortedRoster.indexed walks h (bookRoot D k K cap j)).elim 0 (fun v=>item past born (bookBlock D k K cap j) (bookItem D k K cap j) v g)
    (scan w out (H*chunks G M) e).Exec m state (4+(H*chunks G M)*(2*e.work+4)) ∧
      (∀p : Row H G M,state (out+(row H G M p).val)=((data (fun h g=>DescentPackedLocalAtoms.pack a nodes K' (mask h g) (encode a nodes (field h g))) p).val:Word w)) ∧ CheapCode (scan w out (H*chunks G M) e) :=by
  intro src e state mask field
  apply run T gates src want addr counts out K' m targetRoom actorRoom fieldRoom resultRoom room targetROM actorROM fieldROM resultROM wanted address count field wants locations tallies
  intro j
  exact source ports oldBank bornBank dict out m _ wired past born prior formed access newAccess fit tables _ _ _

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

end OAI
