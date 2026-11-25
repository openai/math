import OAI.Hierarchy.DescentResetCandidateMeta
import OAI.Hierarchy.DescentClosedRosterCoverage
import OAI.Hierarchy.DescentPackedColumnBatch

namespace OAI
/-! # One receiver sheet for all four disjoint reset-parent families -/
namespace Hierarchy.DescentResetFieldAssembler.CandidateSheet
open DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

abbrev Sector (stems contacts privates : ℕ) :=
  Fin stems ⊕ (Fin 1 ⊕ (Fin contacts ⊕ Fin privates))
def size (stems contacts privates : ℕ) := stems+(1+(contacts+privates))
def index (stems contacts privates : ℕ) : Sector stems contacts privates ≃ Fin (size stems contacts privates) :=
  ((Equiv.refl _).sumCongr (((Equiv.refl _).sumCongr finSumFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

theorem stem_val {s c p : ℕ} (j : Fin s) : (index s c p (.inl j)).val=j.val:=rfl
theorem trunk_val (s c p : ℕ) : (index s c p (.inr (.inl 0))).val=s := by change s+0=s; omega
theorem contact_val {s c p : ℕ} (j : Fin c) :
    (index s c p (.inr (.inr (.inl j)))).val=s+1+j.val := by change s+(1+j.val)=_; omega
theorem private_val {s c p : ℕ} (j : Fin p) :
    (index s c p (.inr (.inr (.inr j)))).val=s+1+c+j.val := by change s+(1+(c+j.val))=_; omega

variable {s c p H G M b w X : ℕ}
def terms (src : Fin X→Sector s c p→Expr) (j : ℕ) : Expr :=
  if hit : j<X*size s c p then
    let q : Fin X×Fin (size s c p):=finProdFinEquiv.symm ⟨j,hit⟩
    src q.1 ((index s c p).symm q.2)
  else .lit 0

def output (base bits : ℕ) (x : Fin X) (j : Fin (size s c p)) : Bank :=
  ⟨base+(finProdFinEquiv (x,j)).val*2^bits,bits⟩

theorem run (src : Fin X→Sector s c p→Expr) (base bits : ℕ)
    (value : Fin X→Fin (size s c p)→Fin H→Fin G→Cell b) (mem : Memory w)
    (safe : ∀x a,(src x a).Fits w base)
    (reads : ∀x a,Source (src x a) (value x (index s c p a)) M mem)
    (rows : H*chunks G M≤2^bits) (space : base+(X*size s c p)*2^bits<2^w) :
    let ps:=DescentPackedFlowBatch.passes base (H*chunks G M) (2^bits) (terms src) 0 (X*size s c p)
    (ProtocolRAM.program w ps).Exec mem (result ps mem) (clock ps) ∧ CheapCode (ProtocolRAM.program w ps) ∧
      (∀x j,Reads (output base bits x j) (value x j) M (result ps mem)) ∧
      ∀a,a<base ∨ base+(X*size s c p)*2^bits≤a → result ps mem a=mem a := by
  have early (j : ℕ) (ij : j<X*size s c p) : (terms src j).Fits w base:=by rw [terms,dite_eq_left ij];apply safe
  obtain ⟨exec,done,low⟩:=DescentPackedFlowBatch.execute base (H*chunks G M) (2^bits) (X*size s c p)
    (terms src) mem early space rows
  refine ⟨exec,@ProtocolRAM.program_cheap _ _,?_,?_⟩
  · intro x j a
    let key:=finProdFinEquiv (x,j)
    have data:=done key (row H G M a)
    have actual:=reads x ((index s c p).symm j) a
    have source : terms src key.val=src x ((index s c p).symm j) := by
      rw [terms,dite_eq_left key.isLt]
      change src (finProdFinEquiv.symm (finProdFinEquiv (x,j))).1
        ((index s c p).symm (finProdFinEquiv.symm (finProdFinEquiv (x,j))).2)=_
      rw [Equiv.symm_apply_apply]
    rw [source] at data
    exact data.trans (by simpa only [Equiv.apply_symm_apply] using actual)
  · intro a ha
    rcases ha with before|after
    · exact low a before
    · exact DescentPackedFlowBatch.above _ _ _ _ _ 0 _ _ rows (by simpa using after)

end
end Hierarchy.DescentResetFieldAssembler.CandidateSheet

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

def metaWord (rack : Fin HP→Option B.next.V) (b : ℕ) (x : Fin (2^k)) (j : Fin (totalLocal B))
    (v : Fin HP) (u : Fin Q) : Cell (b*7) :=
  DescentResetFieldAssembler.raw b ((rack v).elim Meta.blank (fun r=>«meta» B ((u,r),x) (localOrigin B ((u,r),x) j)))

/-- Every real positive parent and every padding cell is carried through the same finite
receiver table. Each family supplies its own prior physical expression on its own sector. -/
theorem candidate_sheet (rack : Fin HP→Option B.next.V) (base bits : ℕ) (m : Memory bw)
    (stem : Fin (2^k)→Fin (stemsCount B)→Expr) (trunk : Fin (2^k)→Expr)
    (contact : Fin (2^k)→Fin (contactCount B)→Expr) (priv : Fin (2^k)→Fin (privateCount B)→Expr)
    (sf : ∀x j,(stem x j).Fits bw base) (tf : ∀x,(trunk x).Fits bw base)
    (cf : ∀x j,(contact x j).Fits bw base) (pf : ∀x j,(priv x j).Fits bw base)
    (sr : ∀x j,Source (stem x j) (metaWord B rack b x (idx (.inl j))) M m)
    (tr : ∀x,Source (trunk x) (metaWord B rack b x (idx (.inr (.inl 0)))) M m)
    (cr : ∀x j,Source (contact x j) (metaWord B rack b x (idx (.inr (.inr (.inl j))))) M m)
    (pr : ∀x j,Source (priv x j) (metaWord B rack b x (idx (.inr (.inr (.inr j))))) M m)
    (rows : HP*chunks Q M≤2^bits) (space : base+(2^k*totalLocal B)*2^bits<2^bw) :
    let src:=fun x=>Sum.elim (stem x) (Sum.elim (fun _ : Fin 1=>trunk x) (Sum.elim (contact x) (priv x)))
    let ps:=DescentPackedFlowBatch.passes base (HP*chunks Q M) (2^bits) (CandidateSheet.terms src) 0 (2^k*totalLocal B)
    (ProtocolRAM.program bw ps).Exec m (result ps m) (clock ps) ∧ CheapCode (ProtocolRAM.program bw ps) ∧
      (∀x j,Reads (CandidateSheet.output (s:=stemsCount B) (c:=contactCount B) (p:=privateCount B) base bits x j)
        (metaWord B rack b x j) M (result ps m)) ∧
      ∀a,a<base ∨ base+(2^k*totalLocal B)*2^bits≤a → result ps m a=m a := by
  let src (x : Fin (2^k)) : sectors→Expr :=
    Sum.elim (stem x) (Sum.elim (fun _ : Fin 1=>trunk x) (Sum.elim (contact x) (priv x)))
  have fits (x j) : (src x j).Fits bw base:=by
    rcases j with j|j|j|j
    · exact sf x j
    · exact tf x
    · exact cf x j
    · exact pf x j
  have words (x j) : Source (src x j) (metaWord B rack b x (idx j)) M m:=by
    rcases j with j|j|j|j
    · exact sr x j
    · have only : j=0:=Subsingleton.elim _ _
      subst j;exact tr x
    · exact cr x j
    · exact pr x j
  exact CandidateSheet.run src base bits (metaWord B rack b) m fits words rows space

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
