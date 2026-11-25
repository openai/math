import OAI.Hierarchy.DescentResetCandidateSheet
import OAI.Hierarchy.DescentResetActualSourcePull

namespace OAI
/-! # Shared sparse parent-number columns for the next stage’s parallel-wire rank and signed ports -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentPacking DescentSharedCableNames DescentParallelBase DescentCompiler DescentResetFieldAssembler
open DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
variable {HP M b bw : ℕ}
local notation "sectors" => CandidateSheet.Sector (stemsCount B) (contactCount B) (privateCount B)
local notation "idx" => CandidateSheet.index (stemsCount B) (contactCount B) (privateCount B)
local notation "Q" => S.groupCount (i+1)

def parentWord (rack : Fin HP→Option B.next.V) (b : ℕ) (x : Fin (2^k)) (j : Fin (totalLocal B))
    (v : Fin HP) (u : Fin Q) : Cell b := (actualParentNumber B rack x j v u:ℕ)

theorem parent_number_sheet (rack : Fin HP→Option B.next.V) (base bits : ℕ) (m : Memory bw)
    (stem : Fin (2^k)→Fin (stemsCount B)→Expr) (trunk : Fin (2^k)→Expr)
    (contact : Fin (2^k)→Fin (contactCount B)→Expr) (priv : Fin (2^k)→Fin (privateCount B)→Expr)
    (sf : ∀x j,(stem x j).Fits bw base) (tf : ∀x,(trunk x).Fits bw base)
    (cf : ∀x j,(contact x j).Fits bw base) (pf : ∀x j,(priv x j).Fits bw base)
    (sr : ∀x j,Source (stem x j) (parentWord B rack b x (idx (.inl j))) M m)
    (tr : ∀x,Source (trunk x) (parentWord B rack b x (idx (.inr (.inl 0)))) M m)
    (cr : ∀x j,Source (contact x j) (parentWord B rack b x (idx (.inr (.inr (.inl j))))) M m)
    (pr : ∀x j,Source (priv x j) (parentWord B rack b x (idx (.inr (.inr (.inr j))))) M m)
    (rows : HP*chunks Q M≤2^bits) (space : base+(2^k*totalLocal B)*2^bits<2^bw) :
    let src:=fun x=>Sum.elim (stem x) (Sum.elim (fun _ : Fin 1=>trunk x) (Sum.elim (contact x) (priv x)))
    let ps:=DescentPackedFlowBatch.passes base (HP*chunks Q M) (2^bits) (CandidateSheet.terms src) 0 (2^k*totalLocal B)
    (program bw ps).Exec m (result ps m) (clock ps) ∧ CheapCode (program bw ps) ∧
      (∀x j,Reads (CandidateSheet.output (s:=stemsCount B) (c:=contactCount B) (p:=privateCount B) base bits x j)
        (parentWord B rack b x j) M (result ps m)) ∧
      ∀a,a<base ∨ base+(2^k*totalLocal B)*2^bits≤a → result ps m a=m a := by
  let src (x : Fin (2^k)) : sectors→Expr :=
    Sum.elim (stem x) (Sum.elim (fun _ : Fin 1=>trunk x) (Sum.elim (contact x) (priv x)))
  have fits (x j) : (src x j).Fits bw base:=by
    rcases j with j|j|j|j
    · exact sf x j
    · exact tf x
    · exact cf x j
    · exact pf x j
  have words (x j) : Source (src x j) (parentWord B rack b x (idx j)) M m:=by
    rcases j with j|j|j|j
    · exact sr x j
    · have only : j=0:=Subsingleton.elim _ _
      subst j;exact tr x
    · exact cr x j
    · exact pr x j
  exact CandidateSheet.run src base bits (parentWord B rack b) m fits words rows space

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
