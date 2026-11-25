import OAI.Hierarchy.TaggedWideControlGate
import OAI.Hierarchy.TaggedWideHost
import OAI.Hierarchy.TaggedWideDualControlWires

namespace OAI
/-! # Two native CPU checks and a site on a single physical pin board -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin
open ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} {E Q D V I : Type} [Field F] [Fintype E] [Fintype Q] [Fintype D] [Fintype V] [Fintype I]

abbrev Shared (D : Type) (A B : Gate) := D ⊕ (A.Hidden ⊕ B.Hidden)
abbrev BoardPins (E Q D : Type) (A B : Gate) := E ⊕ (Q ⊕ Shared D A B)
abbrev SitePins (E Q D : Type) (B : Gate) := E ⊕ (Q ⊕ (D ⊕ B.Seen))

theorem shared_card (A B : Gate) : Fintype.card (Shared D A B) =
    Fintype.card D + (A.f*((5+A.r)*(A.W+1)) + A.u*(A.W+1) + 28*pins A.m A.m) +
      (B.f*((5+B.r)*(B.W+1)) + B.u*(B.W+1) + 28*pins B.m B.m) := by
  change Fintype.card (D ⊕ (A.Hidden ⊕ B.Hidden))=_
  rw [(Fintype.card_sum : Fintype.card (D ⊕ (A.Hidden ⊕ B.Hidden)) = _),
    (Fintype.card_sum : Fintype.card (A.Hidden ⊕ B.Hidden) = _),
    A.hidden_card,B.hidden_card]
  omega

def publicPin (A B : Gate) : E ⊕ Q → BoardPins E Q D A B := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
def leftPin (A B : Gate) (i : A.Hidden) : BoardPins E Q D A B := .inr (.inr (.inr (.inl i)))
def rightPin (A B : Gate) (i : B.Hidden) : BoardPins E Q D A B := .inr (.inr (.inr (.inr i)))

def sitePin (A B : Gate) : SitePins E Q D B → BoardPins E Q D A B
  | .inl e => .inl e
  | .inr (.inl q) => .inr (.inl q)
  | .inr (.inr (.inl d)) => .inr (.inr (.inl d))
  | .inr (.inr (.inr i)) => rightPin A B (B.seenPin i)

def headPin (A B : Gate) (w : I → (E ⊕ Q) ⊕ Bool) (i : I) : BoardPins E Q D A B ⊕ Bool :=
  Sum.map (publicPin A B) id (w i)

private def place (N : BitNetwork F (Fintype.card I)) (wire : I→V⊕Bool) :=
  WideHost.localFamily (I:=Unit) (A:=fun _=>I) (fun _=>N) (fun _=>wire)

private theorem place_eval (N : BitNetwork F (Fintype.card I)) (wire : I→V⊕Bool) (v : V→Bool) :
    TypedWiring.value (place N wire) v = TypedWiring.value N (Sum.elim v id ∘ wire) := by
  rw [place,WideHost.localFamily_eval,Fintype.prod_unique]

omit [Field F] in
private theorem place_fee (N : BitNetwork F (Fintype.card I)) (wire : I→V⊕Bool) :
    (place N wire).cells + (place N wire).internal = N.cells+N.internal := by
  rw [place,WideHost.localFamily_size,Fintype.sum_unique]

private def pair (M N : BitNetwork F (Fintype.card V)) :=
  WideHost.localFamily (I:=Bool) (A:=fun _=>V) (fun j=>if j then M else N) (fun _=>Sum.inl)

private theorem pair_eval (M N : BitNetwork F (Fintype.card V)) (v : V→Bool) :
    TypedWiring.value (pair M N) v = TypedWiring.value M v * TypedWiring.value N v := by
  rw [pair,WideHost.localFamily_eval,Fintype.prod_bool]; rfl

omit [Field F] in
private theorem pair_fee (M N : BitNetwork F (Fintype.card V)) :
    (pair M N).cells+(pair M N).internal = (M.cells+M.internal)+(N.cells+N.internal) := by
  rw [pair,WideHost.localFamily_size,Fintype.sum_bool]; rfl

private def cpuPins (G : Gate) (head : G.Head→V⊕Bool) (hid : G.Hidden→V) : G.Pin→V⊕Bool :=
  Sum.elim (Sum.elim head (Sum.elim (fun i=>.inl (hid (.inl i))) (fun i=>.inl (hid (G.seenPin i)))))
    (fun z=>.inl (hid (.inr (.inr z))))

def cpu (G : Gate) (head : G.Head→V⊕Bool) (hid : G.Hidden→V) :=
  place (G.hardware (F:=F)) (cpuPins G head hid)

theorem cpu_eval (G : Gate) (head : G.Head→V⊕Bool) (hid : G.Hidden→V) (v : V→Bool) :
    TypedWiring.value (cpu (F:=F) G head hid) v = G.value (Sum.elim v id ∘ head) (v ∘ hid) := by
  rw [cpu,place_eval]
  apply congrArg (TypedWiring.value (G.hardware (F:=F)))
  funext i
  rcases i with ((a | (b | c)) | z) <;> rfl

/-- The reject gate uses one ternary cell per bit of the observed prefix flag. -/
def flagTest (n : ℕ) (wire : Fin n→V) : BitNetwork F (Fintype.card V) where
  internal := 0
  cells := n
  source i _ := .pin (Fintype.equivFin V (wire i))
  table _ b := if b 0 = false then 1 else 0

theorem flagTest_eval (n : ℕ) (wire : Fin n→V) (v : V→Bool) :
    TypedWiring.value (flagTest (F:=F) n wire) v = if ∀ i,v (wire i)=false then 1 else 0 := by
  unfold TypedWiring.value BitNetwork.eval BitNetwork.weight BitNetwork.factor
  simp only [flagTest,BitSource.read,Equiv.symm_apply_apply]
  change (∑ _ : Fin 0→Bool,∏ i : Fin n,if v (wire i)=false then (1:F) else 0)=_
  have empty (a : F) : (∑ _ : Fin 0→Bool,a)=a := by
    simp [Finset.sum_const]
  rw [empty]
  by_cases good : ∀ i,v (wire i)=false
  · simp [good]
  · obtain ⟨i,bad⟩ := not_forall.mp good
    rw [ite_eq_right good]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right bad)

def localPart (A B : Gate) (prefixPins : A.Head→(E ⊕ Q) ⊕ Bool) (paid : B.Head→(E ⊕ Q) ⊕ Bool)
    (flag : Fin A.u) (site : BitNetwork F (Fintype.card (SitePins E Q D B))) :
    BitNetwork F (Fintype.card (BoardPins E Q D A B)) :=
  pair (cpu A (headPin A B prefixPins) (leftPin A B))
    (pair (flagTest (A.W+1) (fun j=>leftPin A B (A.seenPin (flag,j))))
      (pair (cpu B (headPin A B paid) (rightPin A B)) (WideHost.onPins site (sitePin A B))))

theorem localPart_fee (A B : Gate) (prefixPins : A.Head→(E ⊕ Q) ⊕ Bool) (paid : B.Head→(E ⊕ Q) ⊕ Bool)
    (flag : Fin A.u) (site : BitNetwork F (Fintype.card (SitePins E Q D B))) :
    let N := localPart A B prefixPins paid flag site
    N.cells+N.internal =
      ((A.hardware (F:=F)).cells+(A.hardware (F:=F)).internal)+(A.W+1)+
      ((B.hardware (F:=F)).cells+(B.hardware (F:=F)).internal)+(site.cells+site.internal) := by
  dsimp only
  simp only [localPart,pair_fee,cpu,place_fee,flagTest,WideHost.onPins,BitNetwork.restrictPins,Nat.add_zero]
  omega

/-- This list has one genuine parent tag and twenty-eight slices of each of two independent
native memory histories. There is no copy of an occurrence for an unobserved selector. -/
def read {h : ℕ} (A B : Gate) (tag : Row h × Fin h → E ⊕ Q) :=
  WideHost.dualControlWires (publicPin (D:=D) A B ∘ tag)
    (fun i=>leftPin A B ∘ A.sortPin i) (fun i=>rightPin A B ∘ B.sortPin i)

/-- Readback gates and open socket pins together contribute 29 units for each
bit of a real control occurrence. The rest of the static board is accounted separately. -/
theorem control_socket_fee (h : ℕ) (A B : Gate) :
    let t := WideHost.dualControlSizes h A.m B.m
    (∑ j,28*pins (t j) (t j))+(∑ j,pins (t j) (t j)) =
      29*(pins h h + 28*pins A.m A.m + 28*pins B.m B.m) := by
  dsimp only
  rw [← Finset.mul_sum,WideHost.dual_control_sum h A.m B.m (fun m=>pins m m)]
  ring

def localSite (B : Gate) (site : BitNetwork F (Fintype.card (SitePins E Q D B)))
    (e : E→Bool) (q : Q→Bool) (d : D→Bool) (seen : B.Seen→Bool) : F :=
  TypedWiring.value site (Sum.elim e (Sum.elim q (Sum.elim d seen)))

def headerRead (w : I→(E ⊕ Q)⊕Bool) (e : E→Bool) (q : Q→Bool) : I→Bool :=
  Sum.elim (Sum.elim e q) id ∘ w

omit [Fintype E] [Fintype Q] [Fintype D] [Fintype I] in
private theorem headPin_read (A B : Gate) (w : I→(E ⊕ Q)⊕Bool) (e : E→Bool) (q : Q→Bool)
    (y : Shared D A B→Bool) :
    Sum.elim (Sum.elim e (Sum.elim q y)) id ∘ headPin A B w = headerRead w e q := by
  funext j
  rcases hh : w j with (a | a) | b <;> simp [headPin,publicPin,headerRead,Function.comp_def,hh]

theorem localPart_eval (A B : Gate) (prefixPins : A.Head→(E ⊕ Q) ⊕ Bool) (paid : B.Head→(E ⊕ Q) ⊕ Bool)
    (flag : Fin A.u) (site : BitNetwork F (Fintype.card (SitePins E Q D B)))
    (e : E→Bool) (q : Q→Bool) (y : Shared D A B→Bool) :
    let v := Sum.elim e (Sum.elim q y)
    let a := fun i=>y (.inr (.inl i))
    let b := fun i=>y (.inr (.inr i))
    TypedWiring.value (localPart A B prefixPins paid flag site) v =
      A.value (headerRead prefixPins e q) a * (A.zeroFlag flag (a ∘ A.seenPin) *
      (B.value (headerRead paid e q) b * localSite B site e q (y ∘ Sum.inl) (b ∘ B.seenPin))) := by
  dsimp only
  rw [localPart,pair_eval,pair_eval,pair_eval,cpu_eval,cpu_eval,flagTest_eval,WideHost.onPins_value,
    headPin_read,headPin_read]
  have ports : Sum.elim e (Sum.elim q y) ∘ sitePin A B =
      Sum.elim e (Sum.elim q (Sum.elim (y ∘ Sum.inl) (fun i=>y (.inr (.inr (B.seenPin i)))))) := by
    funext i
    rcases i with a | (b | (c | x)) <;> rfl
  rw [ports]; rfl

end Hierarchy.Tagged.WideControlJoin

end
end OAI
