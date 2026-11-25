import OAI.Hierarchy.DescentReachedArgumentPointer
import OAI.Hierarchy.DescentOrdinaryIssuedPointers
import OAI.Hierarchy.DescentPackedSourceAccess

namespace OAI
/-! The four physical ordinary result columns realize the original reached pointer for every live argument. -/
namespace Hierarchy.DescentSixParty.Reached
open Computability.BorderVNP.Crossing DescentKernelHistory DescentLocalPrivateNames DescentLocalArchiveOrder DescentBundleHistory
open Chronology DescentSIMDLookup DescentPackedOperand DescentOperandStateBanks DescentDatedPriorOperand
open DescentPackedColony DescentOrdinaryFinal DescentSharedCableNames
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist p R : ℕ}
    (cap : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (shape : WorldShape p R B) (hp : 0<p) (pin : P→ℕ)
local notation:max "recipe" v:arg => ((shape.sites v).recipe hp)

variable (cpu:PhysicalOrdinary F P) (v:W.graph.Site)
local notation "L" => cpu.resolver
local notation "D" => cpu.finalChart
variable (population:Fintype.card (B.recipe v).Node≤(L).nodes) (args:∀u,(recipe v).arity u≤(L).operands)
local notation "onsite" => (number v).toEmbedding.trans (Fin.castLEEmb population)
local notation "mouth" => (D).mouths (recipe v) onsite args
variable (hidden:(recipe v).UsedWord↪Key) (metaRows:cpu.MetaWords) (old:Books (L))
    (jobs:Fin (L).jobs→DescentDatedPriorOperand.Source (L))
    (x:Fin (L).blocks) (h:Fin (L).hosts) (g:Fin (L).groups)
local notation:max "fragment" u:arg j:arg => cpu.issuedFragment jobs x h g (mouth ⟨u,j⟩)
local notation:max "expected" u:arg j:arg => argumentPointer cap B number shape hp pin (L).operands ⟨v,u⟩ (Fin.val j)

theorem mouth_address (t:Slot (recipe v)) :
    (number v t.1).val*(L).operands+t.2.val=(mouth t).val :=by
  change _ = (finProdFinEquiv ((onsite t.1),t.2.castLE (args t.1))).val
  rw [finProdFinEquiv_apply_val]
  simp only [Fin.val_castLE, Nat.mul_comm, Nat.add_comm]
  rfl

variable {w:ℕ} (floor:ℕ) (safe:(D).Early (cpu.finalSources floor) (cpu.metaEnd floor) w)
  (room:cpu.afterEnd floor<2^w) (m:Memory w)
  (newRead:∀f b,Reads (cpu.nodeChart.bank (cpu.nodeBankBase floor) f b) (metaRows f b) (L).lanes m)
  (spanRead:∀b pg,Reads (previousBank (L) (cpu.vectorOutput floor) b pg) (old b pg) (L).lanes m)
  (keyRead:∀i,Reads (Banks.wordBank (L) (cpu.normalizedEnd floor) i)
    (fun h' g'=>word ((jobs i).compiled h' g')) (L).lanes m)
  (pos:0<(L).lanes) (bitsFit:(D).field*(L).nodes*(L).lanes≤w)
  (count:∀u,digit (D).arityBits (onsite u).val (metaRows 1 x h g).val=(recipe v).arity u)
  (empty:∀n,(∀u,onsite u≠n)→digit (D).arityBits n.val (metaRows 1 x h g).val=0)
  (keys:cpu.SourceKeys jobs x h g (recipe v) onsite args hidden)
local notation "out" => (cpu.argumentsAfter floor safe room).image m
local notation:max "bank_" f:arg j:arg => previousBank (L) ((D).out (cpu.metaEnd floor)) x
    ((D).pages ((f:Fin 4).castLE (by decide),(j:Fin ((recipe v).arity _)).castLE (args _)))

include newRead spanRead keyRead pos bitsFit count empty keys in
theorem issued_argument_header (u:(B.recipe v).Node) (j:Fin ((recipe v).arity u))
    (cable:∀(e:Incident W.graph v) k (live:(k+1)*p≤W.graph.width e.val),
      (recipe v).operand u j=.inl ⟨.inl e,k,live⟩→
        Pointer.ofKey 0 (resolve (fragment u j))=firstCable cap hp v e k live)
    (exterior:∀(z:Attached W.graph v) k (live:(k+1)*p≤bits z.val),
      (recipe v).operand u j=.inl ⟨.inr z,k,live⟩→ resolve (fragment u j)=Key.pin (pin z.val) k)
    (f:Fin 4) (fit:(expected u j).header f<2^(D).field) :
    cpu.headerDigit h g out (bank_ f j) (onsite u)=(expected u j).header f :=by
  let s:Slot (recipe v):=⟨u,j⟩
  cases assigned:(recipe v).operand u j with
  | inr a=>
    let actual:(recipe v).UsedWord:=⟨a,⟨u,j,assigned⟩⟩
    have typed:=argumentPointer_private cap B number shape hp pin (L).operands v u j mouth
      (mouth_address B number shape hp cpu v population args) actual assigned
    have read:DescentLocalPrivateNames.read (recipe v) s=some actual:=(read_some _ u j actual).mpr assigned
    rw [typed] at fit ⊢
    exact cpu.issued_private_header metaRows old jobs x h g (recipe v) onsite args hidden floor safe room m
      newRead spanRead keyRead pos bitsFit count empty keys s actual read f fit
  | inl b=>
    have none : DescentLocalPrivateNames.read (recipe v) s = none := by
      cases hit : DescentLocalPrivateNames.read (recipe v) s with
      | none => rfl
      | some word₀ =>
        have wrong := (read_some (recipe v) u j word₀).mp hit
        rw [assigned] at wrong
        contradiction
    have pub:(Pointer.ofKey 0 (resolve (fragment u j)))=(expected u j):=by
      rcases b with ⟨e|z,k,alive⟩
      · rw [argumentPointer_cable cap B number shape hp pin (L).operands v u j e k alive assigned]
        exact cable e k alive assigned
      · rw [argumentPointer_pin cap B number shape hp pin (L).operands v u j z k alive assigned,
            exterior z k alive assigned]
        rfl
    rw [←pub] at fit ⊢
    exact cpu.issued_public_header metaRows old jobs x h g (recipe v) onsite args hidden floor safe room m
      newRead spanRead keyRead pos bitsFit count keys s none f fit

end
end Hierarchy.DescentSixParty.Reached

end OAI
