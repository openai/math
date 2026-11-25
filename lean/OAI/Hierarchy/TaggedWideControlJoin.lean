import OAI.Hierarchy.TaggedWideControlGateEval
import OAI.Hierarchy.TaggedWideControlBoard
import OAI.Hierarchy.TaggedWideDualWorkspace

namespace OAI
/-! # Closing the 57 control occurrences of the wide physical host -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin
open ThreeFlat Routing Diagonal TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory TaggedShorterControlHistory
open scoped Classical BigOperators

variable {F : Type*} [Field F] {E Q D : Type} [Fintype E] [Fintype Q] [Fintype D] {h : ℕ}

/-- The tag is read from the fixed public input and selector wires, before any control history. -/
def authentic (tag : Row h × Fin h→E⊕Q) (e : E→Bool) (q : Q→Bool) : Prop :=
  Function.Bijective (fun i : Row h => (Computability.VPVNP.RAMSerialization.wordBits h).symm
    (fun j=>Sum.elim e q (tag (i,j))))

omit [Fintype E] [Fintype Q] [Fintype D] in
theorem control_eval (A B : Gate) (tag : Row h × Fin h→E⊕Q) (e : E→Bool) (q : Q→Bool)
    (y : Shared D A B→Bool) :
    let v := Sum.elim e (Sum.elim q y)
    let t := WideHost.dualControlSizes h A.m B.m
    (∏ j,coeff F (t j) (t j) (v ∘ read A B tag j)) =
      (if authentic tag e q then 1 else 0)*A.sorts (zeroView y)*B.sorts (oneView y) := by
  have pub (j : E⊕Q) : Sum.elim e (Sum.elim q y) (publicPin A B j) = Sum.elim e q j := by
    cases j <;> rfl
  have eq := WideHost.dual_control_product (F:=F) (publicPin (D:=D) A B ∘ tag)
    (fun i=>leftPin A B ∘ A.sortPin i) (fun i=>rightPin A B ∘ B.sortPin i)
    (Sum.elim e (Sum.elim q y))
  simp only [Function.comp_apply,pub] at eq
  dsimp only
  unfold authentic
  by_cases ok : Function.Bijective (fun i : Row h =>
    (Computability.VPVNP.RAMSerialization.wordBits h).symm (fun j=>Sum.elim e q (tag (i,j))))
  · simp only [ite_eq_left ok] at eq ⊢
    exact eq
  · simp only [ite_eq_right ok] at eq ⊢
    exact eq

/-- Every bank may jointly inspect the guessed site bits and all designated paid terminal
words. The shared paid verifier and its 28 sort slices occur only once. -/
def contraction (A B : Gate) (prefixPins : A.Head→(E⊕Q)⊕Bool) (paid : B.Head→(E⊕Q)⊕Bool)
    (flag : Fin A.u) (tag : Row h × Fin h→E⊕Q)
    (site : BitNetwork F (Fintype.card (SitePins E Q D B))) (bank : (D→Bool)→(B.Seen→Bool)→F)
    (e : E→Bool) (q : Q→Bool) : F :=
  ∑ y : Shared D A B→Bool, let v := Sum.elim e (Sum.elim q y)
    let t := WideHost.dualControlSizes h A.m B.m
    bank (dataView y) (oneView y ∘ B.seenPin) *
      (∏ j, coeff F (t j) (t j) (v ∘ read A B tag j)) *
      TypedWiring.value (localPart A B prefixPins paid flag site) v

theorem separated (A B : Gate) (prefixPins : A.Head→(E⊕Q)⊕Bool) (paid : B.Head→(E⊕Q)⊕Bool)
    (flag : Fin A.u) (tag : Row h × Fin h→E⊕Q)
    (site : BitNetwork F (Fintype.card (SitePins E Q D B))) (bank : (D→Bool)→(B.Seen→Bool)→F)
    (e : E→Bool) (q : Q→Bool) :
    contraction A B prefixPins paid flag tag site bank e q =
      (if authentic tag e q then 1 else 0) *
      (∑ a : A.Hidden→Bool, A.value (headerRead prefixPins e q) a * A.sorts a * A.zeroFlag flag (a ∘ A.seenPin)) *
      ∑ d : D→Bool, ∑ b : B.Hidden→Bool, B.value (headerRead paid e q) b * B.sorts b *
        (bank d (b ∘ B.seenPin) * localSite B site e q d (b ∘ B.seenPin)) := by
  let valid : F := if authentic tag e q then 1 else 0
  let first := fun a : A.Hidden→Bool => A.value (F:=F) (headerRead prefixPins e q) a * A.sorts a *
    A.zeroFlag flag (a ∘ A.seenPin)
  let last := fun (d : D→Bool) (b : B.Hidden→Bool) => B.value (F:=F) (headerRead paid e q) b * B.sorts b *
    (bank d (b ∘ B.seenPin) * localSite B site e q d (b ∘ B.seenPin))
  calc
    _ = ∑ y : Shared D A B→Bool, valid * first (zeroView y) * last (dataView y) (oneView y) := by
      unfold contraction
      apply Finset.sum_congr rfl
      intro y _
      dsimp only
      erw [control_eval A B tag e q y,localPart_eval A B prefixPins paid flag site e q y]
      dsimp only [valid,first,last,dataView,zeroView,oneView]
      ac_rfl
    _ = ∑ d : D→Bool, valid * (∑ a,first a) * (∑ b,last d b) :=
      separate (D:=D) (H₀:=A.Hidden) (H₁:=B.Hidden) (F:=F)
        (fun _ : D→Bool => valid) (fun _ => first) last
    _ = _ := (Finset.mul_sum ..).symm

theorem observed_contract (A B : Gate) (prefixPins : A.Head→(E⊕Q)⊕Bool) (paid : B.Head→(E⊕Q)⊕Bool)
    (flag : Fin A.u) (tag : Row h × Fin h→E⊕Q)
    (site : BitNetwork F (Fintype.card (SitePins E Q D B))) (bank : (D→Bool)→(B.Seen→Bool)→F)
    (e : E→Bool) (q : Q→Bool) (head₀ : ℕ→Word A.W) (head₁ : ℕ→Word B.W)
    (reads₀ : headerRead prefixPins e q = A.headBits head₀) (reads₁ : headerRead paid e q = B.headBits head₁) :
    contraction A B prefixPins paid flag tag site bank e q =
      (if authentic tag e q then 1 else 0)*A.observed head₀ (A.zeroFlag flag) *
        ∑ d : D→Bool, B.observed head₁ (fun seen=>bank d seen * localSite B site e q d seen) := by
  rw [separated,reads₀,reads₁,A.sum_hidden]
  apply congrArg (fun z : F => (if authentic tag e q then (1:F) else 0) *
    A.observed head₀ (A.zeroFlag flag) * z)
  apply Finset.sum_congr rfl
  intro d _
  exact B.sum_hidden head₁ (fun seen=>bank d seen * localSite B site e q d seen)

/-- The prefix output can use the universal chronological admission theorem directly. -/
theorem prefix_observed (A : Gate) (head : ℕ→Word A.W) (flag : Fin A.u) :
    A.observed head (A.zeroFlag (F:=F) flag) =
      observationSum (m:=A.m) 28 A.machine A.word A.labels A.start A.addr head A.headerBound A.clock
        (fun obs=>if (obs flag).val=0 then 1 else 0) := by
  apply congrArg (observationSum (m:=A.m) 28 A.machine A.word A.labels A.start A.addr head A.headerBound A.clock)
  funext obs
  exact A.zeroFlag_words flag obs

/-- A native admission trace determines the prefix scalar without a paid execution. -/
theorem prefix_run (A : Gate) (head : ℕ→Word A.W) (flag : Fin A.u) (out : Memory A.W)
    (run : A.Ran head out) (slots : A.S+(A.f+A.u)≤2^A.m) (room : A.W+1≤4*A.m) :
    A.observed head (A.zeroFlag (F:=F) flag) = if (out (A.addr flag).val).val=0 then 1 else 0 := by
  rw [A.observed_run head out run slots room]
  exact A.zeroFlag_words flag (fun i=>wide (out (A.addr i).val))

/-- A paid run is needed only on a tag and selector accepted by the prefix. Its real observed
memory can then be contracted against the entire signed product of bank and local site factors. -/
theorem guarded (A B : Gate) (prefixPins : A.Head→(E⊕Q)⊕Bool) (paid : B.Head→(E⊕Q)⊕Bool)
    (flag : Fin A.u) (tag : Row h × Fin h→E⊕Q)
    (site : BitNetwork F (Fintype.card (SitePins E Q D B))) (bank : (D→Bool)→(B.Seen→Bool)→F)
    (e : E→Bool) (q : Q→Bool) (head₀ : ℕ→Word A.W) (head₁ : ℕ→Word B.W)
    (reads₀ : headerRead prefixPins e q = A.headBits head₀) (reads₁ : headerRead paid e q = B.headBits head₁)
    (admitted : Prop) [Decidable admitted]
    (accept : authentic tag e q → A.observed head₀ (A.zeroFlag flag) = if admitted then (1:F) else 0)
    (out : Memory B.W) (run : authentic tag e q → admitted → B.Ran head₁ out)
    (slots : B.S+(B.f+B.u)≤2^B.m) (room : B.W+1≤4*B.m) :
    contraction A B prefixPins paid flag tag site bank e q =
      if authentic tag e q ∧ admitted then
        ∑ d : D→Bool,bank d (B.terminal out) * localSite B site e q d (B.terminal out) else 0 := by
  rw [observed_contract A B prefixPins paid flag tag site bank e q head₀ head₁ reads₀ reads₁]
  by_cases valid : authentic tag e q
  · rw [ite_eq_left valid,one_mul,accept valid]
    by_cases ok : admitted
    · simp only [valid,ok,ite_true,true_and,one_mul]
      apply Finset.sum_congr rfl
      intro d _
      exact B.observed_run head₁ out (run valid ok) slots room _
    · simp [ok]
  · simp [valid]

end Hierarchy.Tagged.WideControlJoin

end
end OAI
