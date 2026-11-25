import OAI.Hierarchy.TaggedWideControlJoin
import OAI.Hierarchy.TaggedWideCutParts

namespace OAI
/-! # Paid terminal evaluation of the fixed wide physical board -/

noncomputable section
namespace Hierarchy.Tagged
open ThreeFlat Routing TaggedPrune Computability.VPVNP.BurstRAM
open scoped Classical BigOperators

def NativeRouting.workspace {F : Type*} [Field F] {k h w M : ℕ} (r : NativeRouting F k h w M)
    (H : Type) [Fintype H] : NativeRouting F k h w M :=
  {r with Shared := H, finiteShared := inferInstance}

def CutFormat.mapPins {F : Type*} {U V : Type} [Field F] (b : CutFormat F U) (wire : U→V) : CutFormat F V :=
  {b with readPin := wire ∘ b.readPin}

namespace WideControlJoin
variable {F : Type*} [Field F] {k h w M n : ℕ} {D : Type} [Fintype D]
variable (r : NativeRouting F k h w M) (A B : Gate)
local notation "E" => OpenPins h w r.catalyst
local notation "Q" => Fin r.selectors
local notation "V" => SitePins E Q D B

def parentTag (r : NativeRouting F k h w M) : Row h×Fin h→(OpenPins h w r.catalyst)⊕Fin r.selectors :=
  fun i=>.inl (.inl (portIndex h w (.inr (.inl i))))

omit [Fintype D] in
private theorem pull_site (e : E→Bool) (s : Q→Bool) (v : Shared D A B→Bool) :
    (Sum.elim e (Sum.elim s v)) ∘ sitePin A B =
      Sum.elim e (Sum.elim s (Sum.elim (dataView v) (oneView v ∘ B.seenPin))) := by
  funext i
  rcases i with i|i|i|i <;> rfl

/-- The terminal hypothesis concerns the actual signed local-site product on
the observed paid memory, summed over the original physical data bits. All
CPU histories, tag, 56 memory-sort sockets, finite raw selector strings, and
numbered positive shorter banks are compiled by this construction. -/
theorem guarded_board (b : Fin n→CutFormat F V) (cap : Fin n→ℕ)
    (prefixPins : A.Head→(E⊕Q)⊕Bool) (paid : B.Head→(E⊕Q)⊕Bool)
    (flag : Fin A.u) (site : BitNetwork F (Fintype.card V))
    (head₀ : (E→Bool)→(Q→Bool)→ℕ→Word A.W) (head₁ : (E→Bool)→(Q→Bool)→ℕ→Word B.W)
    (reads₀ : ∀ e s,headerRead prefixPins e s=A.headBits (head₀ e s))
    (reads₁ : ∀ e s,headerRead paid e s=B.headBits (head₁ e s))
    (admitted : (E→Bool)→(Q→Bool)→Prop)
    (accept : ∀ e s,authentic (parentTag r) e s→
      A.observed (head₀ e s) (A.zeroFlag flag)=if admitted e s then (1:F) else 0)
    (tape : ∀ e s,authentic (parentTag r) e s→
      (admitted e s ↔ ∃ a,reads r.encoding e s a))
    (out : (E→Bool)→(Q→Bool)→Memory B.W)
    (run : ∀ e s,authentic (parentTag r) e s→admitted e s→B.Ran (head₁ e s) (out e s))
    (slots : B.S+(B.f+B.u)≤2^B.m) (room : B.W+1≤4*B.m)
    (terminal : ∀ e s a,reads r.encoding e s a →
      (∑ d : D→Bool, (∏ i,(b i).closed (Sum.elim e (Sum.elim s (Sum.elim d (B.terminal (out e s)))))) *
        localSite B site e s d (B.terminal (out e s))) =
          if (r.links a).Keep (2^h) then r.route a e else 0) :
    let H := Shared D A B
    let t := WideHost.dualControlSizes h A.m B.m
    let localPart := localPart A B prefixPins paid flag site
    ∃ board : StaticBoard F k h w M (fun i=>(b i).bank (cap i)) t,
      board.selectors=r.selectors ∧ board.cost ≤
        localPart.cells+localPart.internal+((∑ i,(b i).cost)+∑ j,28*pins (t j) (t j))+
        (r.selectors+Fintype.card H)+(Fintype.card E+
        ((∑ i,((b i).modules*2)*pins (b i).height (b i).width)+∑ j,pins (t j) (t j))) := by
  intro H t net
  let rt := r.workspace (Shared D A B)
  let fmt := fun i=> (b i).mapPins (sitePin A B)
  apply CutFormat.static_board rt fmt cap t net (read A B (parentTag r))
  intro e s
  let bank (d : D→Bool) (obs : B.Seen→Bool) := ∏ i,(b i).closed (Sum.elim e (Sum.elim s (Sum.elim d obs)))
  let val := ∑ d : D→Bool,bank d (B.terminal (out e s))*localSite B site e s d (B.terminal (out e s))
  calc
    _ = contraction A B prefixPins paid flag (parentTag r) site bank e s := by
      unfold contraction
      apply Finset.sum_congr (congrArg (@Finset.univ (Shared D A B → Bool)) (Subsingleton.elim _ _))
      intro y _
      dsimp only
      have pin := pull_site r A B e s y
      have each (i : Fin n) : (fmt i).closed (Sum.elim e (Sum.elim s y)) =
          (b i).closed (Sum.elim e (Sum.elim s (Sum.elim (dataView y) (oneView y ∘ B.seenPin)))) := by
        unfold CutFormat.closed
        apply congrArg (TaggedShorterBank.close _ _)
        exact congrArg (fun z=>z ∘ (b i).readPin) pin
      refine congrArg₂ (· * ·) ?_ rfl
      refine congrArg₂ (· * ·) ?_ rfl
      apply Finset.prod_congr rfl
      exact fun i _ => each i
    _ = if authentic (parentTag r) e s ∧ admitted e s then val else 0 :=
      guarded A B prefixPins paid flag (parentTag r) site bank e s (head₀ e s) (head₁ e s)
        (reads₀ e s) (reads₁ e s) _ (accept e s) (out e s) (run e s) slots room
    _ = _ := by
      have signed := WideHost.selected_of_prefix (fun a=>(rt.links a).Keep (2^h))
        rt.encoding rt.route e s (admitted e s) (if admitted e s then 1 else 0) val
        (fun _=>rfl) (tape e s) (terminal e s)
      refine Eq.trans ?_ signed
      have tagRead : authentic (parentTag r) e s ↔ Function.Bijective (tag (fun i=>e (.inl i))) :=
        Iff.rfl
      by_cases valid : Function.Bijective (tag (fun i=>e (.inl i)))
      · have real := tagRead.mpr valid
        by_cases pass : admitted e s
        · have both : authentic (parentTag r) e s ∧ admitted e s := ⟨real,pass⟩
          rw [ite_eq_left both,ite_eq_left valid,ite_eq_left pass,one_mul,one_mul]
        · have reject : ¬(authentic (parentTag r) e s ∧ admitted e s) := fun h=>pass h.2
          rw [ite_eq_right reject,ite_eq_left valid,ite_eq_right pass,one_mul,zero_mul]
      · have reject : ¬(authentic (parentTag r) e s ∧ admitted e s) := fun h=>valid (tagRead.mp h.1)
        rw [ite_eq_right reject,ite_eq_right valid,zero_mul,zero_mul]

end WideControlJoin
end Hierarchy.Tagged

end
end OAI
