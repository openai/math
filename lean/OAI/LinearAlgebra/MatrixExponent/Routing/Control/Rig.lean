import OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Decor
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Keys
import OAI.LinearAlgebra.MatrixExponent.Transport.System
import OAI.LinearAlgebra.MatrixExponent.Protocol.Wired
import OAI.LinearAlgebra.MatrixExponent.Coloring.Formula
import OAI.LinearAlgebra.MatrixExponent.Protocol.Focus
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Computability

/-!
# Fixed slots for core transports

A slot records the entire chart, a directed local edge, an end, a
copy number and a hop generator. Its chart word recovers the center
from the endpoint. This makes placement injective without using the
ambient size as part of the slot alphabet.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open scoped Classical Pointwise

variable {G I : Type} [Group G] [MulAction G I]

abbrev Address (H : Finset G) (r : ℕ) := Σ b : Board H r, ↥b.1.2.edges
abbrev Socket (H : Finset G) (r R : ℕ) := Address H r × Bool × Fin R × ↥H

namespace Address
variable {H : Finset G} {r : ℕ} (e : Address H r)

def point (b : Bool) : e.1.Site := if b then e.2.val.2 else e.2.val.1

def word (b : Bool) : G := e.1.word (e.point b)

def test (x : Root G) (u : ↥H) : Prop :=
  x.see (u.val⁻¹ * e.word false) (e.word true) = true ∨
    x.see (u.val⁻¹ * e.word true) (e.word false) = true

def generator (hH : 1 ∈ H) (x : Root G) : ↥H :=
  if h : ∃ u, e.test x u then h.choose else ⟨1, hH⟩

theorem local_generator (hH : 1 ∈ H) : Root.Local (e.generator hH) := by
  have h (u : ↥H) : Root.Local (fun x => e.test x u) :=
    ((Root.local_see (u.val⁻¹ * e.word false) (e.word true)).pair
      (Root.local_see (u.val⁻¹ * e.word true) (e.word false))).map
        (fun p => p.1 = true ∨ p.2 = true)
  apply (Root.local_pi h).of_eq
  intro x y he
  unfold generator
  rw [he]

end Address

namespace Socket
variable {H : Finset G} {r R : ℕ}

def peer (a : Socket H r R) : Socket H r R := (a.1, !a.2.1, a.2.2)
def word (a : Socket H r R) : G := a.1.word a.2.1
def hop (a : Socket H r R) := a.peer.word * a.word⁻¹

@[simp] theorem peer_peer (a : Socket H r R) : a.peer.peer = a := by simp [peer]

end Socket

variable (H : Finset G) (hH : 1 ∈ H) (r : ℕ) (g : G) (hg : g ∈ H ^ r) {R : ℕ}

def address (e : (market (I := I) H hH r g hg).Edge) : Address H r :=
  ⟨board H hH r g hg e.1, e.2⟩

def attach (e : (market (I := I) H hH r g hg).Edge) (b : Bool) (j : Fin R) :
    I × Socket H r R :=
  let a := address H hH r g hg e
  (a.word b • e.1, a, b, j, a.generator hH ⟨I, e.1⟩)

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! # Injectivity and range of the core slot placement -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open scoped Classical Pointwise

variable {G I : Type} [Group G] [MulAction G I]
    (H : Finset G) (hH : 1 ∈ H) (r : ℕ) (g : G) (hg : g ∈ H ^ r) {R : ℕ}
    (e : (market (I := I) H hH r g hg).Edge) (b : Bool) (j : Fin R)

theorem attach_owner :
    (attach H hH r g hg e b j).1 =
      if b then (market H hH r g hg).name e.1 e.2.val.2
      else (market H hH r g hg).name e.1 e.2.val.1 := by
  cases b <;> rfl

theorem attach_center :
    ((attach H hH r g hg e b j).2.word)⁻¹ • (attach H hH r g hg e b j).1 = e.1 :=
  inv_smul_smul _ _

theorem attach_peer :
    let t := attach H hH r g hg e b j
    attach H hH r g hg e (!b) j = (t.2.hop • t.1, t.2.peer) := by
  simp only [attach, Socket.hop, Socket.word, Socket.peer, mul_smul, inv_smul_smul]

theorem attach_inj (f : (market (I := I) H hH r g hg).Edge) (c : Bool) (k : Fin R)
    (he : attach H hH r g hg e b j = attach H hH r g hg f c k) :
    e = f ∧ b = c ∧ j = k := by
  have hc := attach_center H hH r g hg e b j
  rw [he, attach_center] at hc
  have ha := congrArg (fun i => i.2.1) he
  refine ⟨?_, congrArg (fun i => i.2.2.1) he, congrArg (fun i => i.2.2.2.1) he⟩
  rcases e with ⟨a, u⟩
  rcases f with ⟨a', u'⟩
  change a' = a at hc
  subst a'
  exact congrArg (Sigma.mk a) (eq_of_heq (Sigma.mk.inj ha).2)

theorem attach_link :
    let x := attach H hH r g hg e b j
    let y := attach H hH r g hg e (!b) j
    (x.2.2.2.2 : G) • x.1 = y.1 ∨ (x.2.2.2.2 : G) • y.1 = x.1 := by
  let q := address H hH r g hg e
  let c : Root G := ⟨I, e.1⟩
  have he : ∃ u, q.test c u :=
    ((Board.valid_choose H r hH g hg c).2.2.2.2 _ _).mp e.2.property
  have hu : q.test c (q.generator hH c) := by
    unfold Address.generator
    rw [dite_eq_left he]
    exact he.choose_spec
  simp only [Address.test, Root.see, Root.label, decide_eq_true_eq, mul_smul, inv_smul_eq_iff] at hu
  cases b
  · exact hu.symm.imp Eq.symm Eq.symm
  · exact hu.imp Eq.symm Eq.symm

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! # Programming a fixed socket by inspecting its center -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Socket
open scoped Classical Pointwise

variable {G I : Type} [Group G] [MulAction G I] {H : Finset G} {r R q : ℕ}
  (s : Socket H r R) (hH : 1 ∈ H) (g : G) (hg : g ∈ H ^ r)
  (cnt : Decor G q → Address H r → ℕ)

def enabled (x : Decor G q) : Bool :=
  let y := x.shift s.word⁻¹
  decide (Board.choose H r hH g hg y.toRoot = s.1.1 ∧
    s.1.generator hH y.toRoot = s.2.2.2 ∧ s.2.2.1.val < cnt y s.1)

theorem local_enabled (hc : Decor.Local cnt) : Decor.Local (s.enabled hH g hg cnt) := by
  have hd := (Board.local_choose H r hH g hg).pair (s.1.local_generator hH)
  have hl := ((Decor.local_root hd).pair hc).map
    (fun p => decide (p.1.1 = s.1.1 ∧ p.1.2 = s.2.2.2 ∧ s.2.2.1.val < p.2 s.1))
  exact hl.shift s.word⁻¹

variable (mark : I → Fin (2 ^ q))

theorem enabled_at (i : I) :
    s.enabled hH g hg cnt ⟨⟨I, i⟩, mark⟩ = true ↔
      let c := s.word⁻¹ • i
      board H hH r g hg c = s.1.1 ∧ s.1.generator hH ⟨I, c⟩ = s.2.2.2 ∧
        s.2.2.1.val < cnt ⟨⟨I, c⟩, mark⟩ s.1 := by
  simp only [enabled, decide_eq_true_eq]
  rfl

theorem enabled_attach (e : (market (I := I) H hH r g hg).Edge) (b : Bool) (j : Fin R) :
    let a := attach H hH r g hg e b j
    a.2.enabled hH g hg cnt ⟨⟨I, a.1⟩, mark⟩ = true ↔
      j.val < cnt ⟨⟨I, e.1⟩, mark⟩ (address H hH r g hg e) := by
  dsimp only
  rw [enabled_at, attach_center]
  simp only [attach, address, true_and]

private theorem exists_edge (c : I) (hb : board H hH r g hg c = s.1.1) :
    ∃ e : (market (I := I) H hH r g hg).Edge, e.1 = c ∧ address H hH r g hg e = s.1 := by
  rcases s with ⟨⟨a, e⟩, b, j, u⟩
  change board H hH r g hg c = a at hb
  subst a
  exact ⟨⟨c, e⟩, rfl, rfl⟩

theorem of_enabled {i : I} (he : s.enabled hH g hg cnt ⟨⟨I, i⟩, mark⟩ = true) :
    ∃ e : (market (I := I) H hH r g hg).Edge,
      attach H hH r g hg e s.2.1 s.2.2.1 = (i, s) ∧
        s.2.2.1.val < cnt ⟨⟨I, e.1⟩, mark⟩ (address H hH r g hg e) := by
  obtain ⟨hb, hgen, hcount⟩ := (s.enabled_at hH g hg cnt mark i).mp he
  obtain ⟨e, hc, ha⟩ := exists_edge s hH g hg _ hb
  refine ⟨e, ?_, by rwa [hc, ha]⟩
  simp only [attach, ha, hc, hgen]
  exact Prod.ext (smul_inv_smul _ i) rfl

end OAI.LinearAlgebra.MatrixExponent.Routing.Socket
end

/-!
# Encoding sockets by a fixed number of bits

The command names the generator word by the physical index of its
own slot. A separate finite list of actions resolves these words into
the addresses of the opposite endpoints.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open scoped Classical Pointwise
open Coloring

variable {G I : Type} [Group G] [MulAction G I] {H : Finset G} {r R p q : ℕ}

abbrev Bank (H : Finset G) (r R p : ℕ) := Socket H r R ↪ B p

namespace Bank
variable (bank : Bank H r R p)

def read (i : B p) : Option (Socket H r R) :=
  if h : ∃ s, bank s = i then some h.choose else none

@[simp] theorem read_slot (s : Socket H r R) : bank.read (bank s) = some s := by
  have h : ∃ t, bank t = bank s := ⟨s, rfl⟩
  rw [read, dite_eq_left h, bank.injective h.choose_spec]

theorem of_read {i : B p} {s : Socket H r R} (he : bank.read i = some s) : bank s = i := by
  unfold read at he
  split at he
  · rename_i h
    rw [← Option.some.inj he]
    exact h.choose_spec
  · cases he

def hop (j : B p) : G := (bank.read j).elim 1 Socket.hop

def generator (hH : 1 ∈ H) (j : B p) : ↥H :=
  (bank.read j).elim ⟨1, hH⟩ (fun s => s.2.2.2)

variable (hH : 1 ∈ H) (g : G) (hg : g ∈ H ^ r) (cnt : Decor G q → Address H r → ℕ)

def program (x : Decor G q) (j : B p) : Bool × Bool × B p × B p :=
  match bank.read j with
  | none => (false, false, j, j)
  | some s => (s.enabled hH g hg cnt x, s.2.1, j, bank s.peer)

theorem program_local (hc : Decor.Local cnt) : Decor.Local (bank.program hH g hg cnt) := by
  apply Decor.local_pi
  intro j
  unfold program
  cases bank.read j with
  | none => exact ⟨∅, fun _ _ _ _ => rfl⟩
  | some s =>
    exact (s.local_enabled hH g hg cnt hc).map (fun b => (b, s.2.1, j, bank s.peer))

def orders (mark : I → B q) (a : I × B p) : Bool × Bool × I × B p :=
  let k := bank.program hH g hg cnt ⟨⟨I, a.1⟩, mark⟩ a.2
  (k.1, k.2.1, bank.hop k.2.2.1 • a.1, k.2.2.2)

def pin (e : (market (I := I) H hH r g hg).Edge) (b : Bool) (j : Fin R) : I × B p :=
  Prod.map id bank (attach H hH r g hg e b j)

theorem orders_pin (mark : I → B q) (e : (market (I := I) H hH r g hg).Edge)
    (b : Bool) (j : Fin R) (hj : j.val < cnt ⟨⟨I, e.1⟩, mark⟩ (address H hH r g hg e)) :
    bank.orders hH g hg cnt mark (bank.pin hH g hg e b j) =
      (true, b, bank.pin hH g hg e (!b) j) := by
  have he := (Socket.enabled_attach hH g hg cnt mark e b j).mpr hj
  simp only [orders, pin, Prod.map, id_eq, program, read_slot, hop, Option.elim_some, he]
  rw [attach_peer H hH r g hg e b j]
  rfl

theorem covered (mark : I → B q) (i : I × B p)
    (hi : (bank.orders hH g hg cnt mark i).1 = true) :
    ∃ (e : (market (I := I) H hH r g hg).Edge) (b : Bool) (j : Fin R),
      bank.pin hH g hg e b j = i ∧ j.val < cnt ⟨⟨I, e.1⟩, mark⟩ (address H hH r g hg e) := by
  rcases i with ⟨i, k⟩
  simp only [orders, program] at hi
  cases hr : bank.read k with
  | none => simp [hr] at hi
  | some s =>
    simp only [hr] at hi
    obtain ⟨e, he, hj⟩ := s.of_enabled hH g hg cnt mark hi
    exact ⟨e, s.2.1, s.2.2.1, by simp [pin, he, bank.of_read hr], hj⟩

end Bank
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# From counted edges to transport commands

Every copy has its own two slots. The two chart words give opposite
orders even for a loop or parallel copies. Only a hop generator of the
fixed menu is needed to prove the two slots share a transport group.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Bank
open Coloring Transport
open scoped Classical Pointwise

variable {G I : Type} [Group G] [MulAction G I] {H : Finset G} {r R p q h : ℕ}
  (bank : Bank H r R p) (hH : 1 ∈ H) (g : G) (hg : g ∈ H ^ r)

def endpoints (m : (market (I := I) H hH r g hg).Edge → ℕ) (hr : ∀ e, m e ≤ R) :
    Protocol.End m ↪ I × B p where
  toFun a := bank.pin hH g hg a.1.1 a.2 (a.1.2.castLE (hr _))
  inj' := by
    rintro ⟨⟨e, j⟩, b⟩ ⟨⟨f, k⟩, c⟩ he
    have hx := congrArg Prod.fst he
    have hh : attach H hH r g hg e b (j.castLE (hr e)) =
        attach H hH r g hg f c (k.castLE (hr f)) :=
      Prod.ext hx (bank.injective (congrArg Prod.snd he))
    obtain ⟨rfl, rfl, eq⟩ := attach_inj H hH r g hg e b _ f c _ hh
    have hk : j = k := Fin.ext (congrArg (fun x : Fin R => x.val) eq)
    subst k
    rfl

variable [MulAction G (Site h)] (cnt : Decor G q → Address H r → ℕ)
    (mark : Site h → B q) (m : (market (I := Site h) H hH r g hg).Edge → ℕ)

def placement (hr : ∀ e, m e ≤ R)
    (hc : ∀ e, cnt ⟨⟨Site h, e.1⟩, mark⟩ (address H hH r g hg e) = m e)
    (group : Port h p → ℕ)
    (same : ∀ x y i j, bank.generator hH i = bank.generator hH j →
      (bank.generator hH i).val • x = y → group (x, i) = group (y, j))
    (a : Orders h p) (ha : a = bank.orders hH g hg cnt mark) :
    Protocol.Placement
      (fun e => (market H hH r g hg).name e.1 e.2.val.1)
      (fun e => (market H hH r g hg).name e.1 e.2.val.2) m group a where
  embed := bank.endpoints hH g hg m hr
  owner i := attach_owner H hH r g hg _ _ (i.1.2.castLE (hr _))
  cmd i := by
    rw [ha]
    apply bank.orders_pin
    rw [hc]
    exact i.1.2.isLt
  cover i hi := by
    rw [ha] at hi
    obtain ⟨e, b, j, he, hj⟩ := bank.covered hH g hg cnt mark i (Finset.mem_filter.mp hi).2
    rw [hc] at hj
    exact ⟨⟨⟨e, ⟨j.val, hj⟩⟩, b⟩, he⟩
  group i := by
    let j := i.1.2.castLE (hr i.1.1)
    let x := attach H hH r g hg i.1.1 i.2 j
    let y := attach H hH r g hg i.1.1 (!i.2) j
    have hgen (k : Socket H r R) : bank.generator hH (bank k) = k.2.2.2 := by
      simp [generator]
    have he : bank.generator hH (bank x.2) = bank.generator hH (bank y.2) := by
      rw [hgen, hgen]; rfl
    change group (y.1, bank y.2) = group (x.1, bank x.2)
    rcases attach_link H hH r g hg i.1.1 i.2 j with h | h
    · exact (same _ _ _ _ he (by rw [hgen]; exact h)).symm
    · exact same _ _ _ _ he.symm (by rw [hgen]; exact h)

end OAI.LinearAlgebra.MatrixExponent.Routing.Bank
end

/-!
# Finite selectors and local verification

A selector contains one bounded transcript per center. A local test
checks all rounds at once using the neighbor transcripts. As the
encoding is injective, inactive and spare symbols have no multiplicity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral
open scoped Classical

variable {K S I : Type} [Field K] [Fintype S] [DecidableEq S]
  [Fintype I] [DecidableEq I] {N M : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)}
  (a : Atlas N A M ρ) (m R : ℕ)

namespace Atlas

abbrev Film (k : ℕ) := Σ s : Shape N, a.Timeline m R s k

instance (k : ℕ) : Fintype (a.Film m R k) := Fintype.ofFinite _

def frame {k : ℕ} (x : a.Film m R (k + 1)) : Σ s : Shape N, a.Cell m R s :=
  ⟨x.1, x.2.1, x.2.2.1, a.start m R _ _ x.2.2.2⟩

def tail {k : ℕ} (x : a.Film m R (k + 1)) : a.Film m R k := ⟨x.1, x.2.2.2⟩

def Watch (t μ d : ℕ) (v : Mask N t A) :
    (k : ℕ) → a.Film m R k → (Fin (2 ^ t) → a.Film m R k) → Prop
  | 0, _, _ => True
  | k + 1, x, y =>
    a.test m t R μ d (a.frame m R x, v) (fun j => (a.frame m R (y j), v)) ∧
      Watch t μ d v k (a.tail m R x) (fun j => a.tail m R (y j))

abbrev bits (k : ℕ) := Fintype.card (a.Film m R k)
abbrev Symbol (k : ℕ) := Fin (2 ^ a.bits m R k)

def write {k : ℕ} : a.Film m R k ↪ a.Symbol m R k := Coloring.encode _

def Accept (t μ d k : ℕ) (s : Shape N) (v : Mask N t A)
    (x : a.Symbol m R k) (y : Fin (2 ^ t) → a.Symbol m R k) : Prop :=
  ∃ (u : a.Timeline m R s k) (w : Fin (2 ^ t) → a.Film m R k),
    a.write m R ⟨s, u⟩ = x ∧ (∀ j, a.write m R (w j) = y j) ∧
      (∀ j, (a.start m R s k u j).val = 0) ∧ a.Watch m R t μ d v k ⟨s, u⟩ w

end Atlas

namespace Market
variable (b : Market I N) {t : ℕ} (g : b.Ports t) (μ d : ℕ)

def film {k : ℕ} (x : b.Logset a m R k) (i : I) : a.Film m R k := ⟨_, x i⟩

theorem watch_iff (k : ℕ) (x : b.Logset a m R k) :
    (∀ i, a.Watch m R t μ d (b.mask A g i) k (b.film a m R x i)
      (fun j => b.film a m R x (g.addr j i))) ↔ b.checkedLog a μ d m R k x := by
  induction k with
  | zero => simp [Atlas.Watch, checkedLog]
  | succ k ih =>
    let y (i : I) := (x i).2.2
    let c (i : I) : a.Cell m R (b.code i) := ((x i).1, (x i).2.1, a.start m R _ _ (y i))
    simp only [Atlas.Watch, checkedLog, forall_and]
    exact and_congr (b.checked a g c μ d) (ih y)

def selector (k : ℕ) (u : b.Path a μ d m k 0) : I → a.Symbol m R k :=
  a.write m R ∘ b.film a m R (b.encodeLog a μ d m R k 0 u)

theorem selector_injective (k : ℕ) : Function.Injective (b.selector a m R μ d k) := by
  intro u v h
  apply b.encodeLog_injective a μ d m R k 0
  exact funext fun i => eq_of_heq (Sigma.mk.inj ((a.write m R).injective (congrFun h i))).2

def Legal (k : ℕ) (z : I → a.Symbol m R k) :=
  ∀ i, a.Accept m R t μ d k (b.code i) (b.mask A g i) (z i) (fun j => z (g.addr j i))

variable [Nonempty S] (room : a.Room m) (hm : 1 ≤ M) (hd : d ≤ M) (k : ℕ)
  (hk : k * rateBound a m ≤ R)

include room hm hd hk in
theorem legal_iff (z : I → a.Symbol m R k) :
    b.Legal a m R g μ d k z ↔ ∃ u, b.selector a m R μ d k u = z := by
  have hbound : ∀ i : b.Request A, (0 : ℕ) + k * rateBound a m ≤ R := fun _ => by
    rw [zero_add]
    exact hk
  have h := b.encodeLog_spec a μ d m R room hm hd k 0 hbound
  constructor
  · intro hz
    choose x y hx hy h₀ hvalid using hz
    have he (i) : y i = fun j => b.film a m R x (g.addr j i) :=
      funext fun j => (a.write m R).injective ((hy i j).trans (hx _).symm)
    have hv : b.checkedLog a μ d m R k x := (b.watch_iff a m R g μ d k x).mp fun i => by
      rw [← he]
      exact hvalid i
    obtain ⟨u, hu⟩ := (h x).mp ⟨funext fun i => funext (h₀ i), hv⟩
    exact ⟨u, by unfold selector; rw [hu]; exact funext hx⟩
  · rintro ⟨u, rfl⟩
    let x := b.encodeLog a μ d m R k 0 u
    obtain ⟨h₀, hv⟩ := (h x).mpr ⟨u, rfl⟩
    exact fun i => ⟨x i, fun j => b.film a m R x (g.addr j i), rfl, fun _ => rfl,
      fun j => congrFun (congrFun h₀ i) j, (b.watch_iff a m R g μ d k x).mpr hv i⟩

def branches : b.Path a μ d m k 0 ≃ {z // b.Legal a m R g μ d k z} := by
  have h := b.legal_iff a m R g μ d room hm hd k hk
  exact Equiv.ofBijective (fun u => ⟨_, (h _).mpr ⟨u, rfl⟩⟩)
    ⟨fun _ _ e => b.selector_injective a m R μ d k (congrArg Subtype.val e),
      fun z => let ⟨u, hu⟩ := (h _).mp z.property; ⟨u, Subtype.ext hu⟩⟩

end Market
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Local replay of the number of wires at an edge

The edge belongs to a single center. At termination only requests
whose designated depot is there can contribute to its width.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral Finset
open scoped Classical

variable {K S I : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype I] [DecidableEq I] {N t M : ℕ} {ρ : ℝ} (A : Finset (Tensor K S))

namespace Market
variable (b : Market I N) (g : b.Ports t) (d M : ℕ)

def here (i : I) (x : (b.code i).Req A) : Bool :=
  decide (b.depot A g (b.request A i x) = ⟨i, x⟩)

omit [Nonempty S] [Fintype I] [DecidableEq I] [DecidableEq S] in
theorem request_inj (i : I) : Function.Injective (b.request A i) :=
  fun x y h => Sum.inl.inj (b.assign_injective A i (a₁ := .inl x) (a₂ := .inl y) (congrArg Sum.inl h))

theorem tally_here (i : I) (x : (b.code i).Req A) (e : (b.shape i).edges) :
    b.tally A d M g (b.request A i x) ⟨i, e⟩ =
      if b.here A g i x then (b.code i).route A d M x e else 0 := by
  by_cases h : b.depot A g (b.request A i x) = ⟨i, x⟩
  · rw [tally, h, ite_eq_left (show b.here A g i x = true from decide_eq_true h)]
    exact Stock.collect_inj (g := fun e => (⟨i, e⟩ : b.Edge))
      (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2) _ _
  · rw [ite_eq_right (show b.here A g i x ≠ true from fun he => h (of_decide_eq_true he))]
    by_contra! hz
    have hi := Protocol.tally_origin A d M b g _ _ hz
    have hu := (b.depot_spec A g (b.request A i x)).1
    generalize b.depot A g (b.request A i x) = u at hi hu h
    rcases u with ⟨j, y⟩
    change j = i at hi
    subst j
    exact h (congrArg (fun v => (⟨i, v⟩ : b.Source A)) (b.request_inj A i hu))

theorem tally_at (z : b.Request A → ℕ) (i : I) (e : (b.shape i).edges) :
    (∑ x, b.tally A d M g x ⟨i, e⟩ * z x) =
      ∑ x, (if b.here A g i x then (b.code i).route A d M x e else 0) * b.localStock A z i x := by
  let U := univ.image (b.request A i)
  have zero (x : b.Request A) (hx : x ∉ U) : b.tally A d M g x ⟨i, e⟩ = 0 := by
    by_contra hz
    have hi := Protocol.tally_origin A d M b g _ _ hz
    have hu := (b.depot_spec A g x).1
    generalize b.depot A g x = u at hi hu
    rcases u with ⟨j, v⟩
    change j = i at hi
    subst j
    exact hx (mem_image.mpr ⟨v, mem_univ _, hu⟩)
  rw [← sum_subset (subset_univ U) (fun x _ hx => by rw [zero x hx, zero_mul])]
  rw [show U = univ.image (b.request A i) from rfl, sum_image (b.request_inj A i).injOn]
  exact sum_congr rfl fun x _ => congrArg (· * z (b.request A i x)) (b.tally_here A g d M i x e)

end Market
variable {A} (a : Atlas N A M ρ) (μ d m R : ℕ)

def Atlas.edgeCount (s : Shape N) (owner : s.Req A → Bool) (e : s.2.edges) :
    (k : ℕ) → a.Timeline m R s k → ℕ
  | 0, x => ∑ j, (if owner j then s.route A d M j e else 0) * (x.down j).val
  | k + 1, x => a.changeAt s m x.2.1 true (.inr e) + edgeCount s owner e k x.2.2

namespace Market
variable (b : Market I N) (g : b.Ports t)

omit [Fintype I] [Nonempty S] [DecidableEq S] in
private theorem read_core {E J : Type} [Fintype J] [DecidableEq J] [DecidableEq E]
    {T : J → Tensor K S} {H : ℝ} (q : Proposal T H)
    (f : J → I ⊕ E) (hf : Function.Injective f) (U : Finset J) (j : J) (e : E)
    (he : f j = .inr e) (u : (q.flex f U m).choice) :
    (q.flex f U m).core u e =
      q.output U (m + Fintype.card q.move.letter) u.val j := by
  change Stock.collect f _ (.inr e) = _
  rw [← he, Stock.collect_inj hf]

omit [Nonempty S] in
theorem step_count (p : b.Request A → ℝ) (i : I) (e : (b.shape i).edges)
    (u : (b.policy a p m).choice) :
    (b.policy a p m).core u ⟨i, e⟩ = a.changeAt (b.code i) m (b.record a p m u i) true (.inr e) := by
  let F (j : b.active a p) := (b.localMove a p m j).core (u j) ⟨i, e⟩
  change (∑ j, F j) = _
  have he (j : b.active a p) (hj : j.val ≠ i) : F j = 0 := by
    by_contra hn
    exact hj (b.core_owner a p m j (u j) _ hn)
  by_cases hi : i ∈ b.active a p
  · let j : b.active a p := ⟨i, hi⟩
    rw [Fintype.sum_eq_single j (fun k hk => he k fun h => hk (Subtype.ext h))]
    have hh := b.record_active a p m u j
    change b.record a p m u i = _ at hh
    rw [hh]
    let q := b.moveAt a p j
    refine (read_core m q (b.assign A i) (b.assign_injective A i) ((b.shape i).links A)
      (.inr e) ⟨i, e⟩ rfl (u j)).trans ?_
    congr
  · rw [sum_eq_zero (fun j _ => he j fun h => hi (h ▸ j.property))]
    rw [show b.record a p m u i = none from dite_eq_right hi]
    rfl

theorem edge_count (room : a.Room m) (hm : 1 ≤ M) (hd : d ≤ M)
    (k : ℕ) (z : b.Request A → ℕ) (hz : ∀ i, z i + k * rateBound a m ≤ R)
    (u : b.Path a μ d m k z) (i : I) (e : (b.shape i).edges) :
    Protocol.edges (b.payload A) (b.decision a μ d m) (b.tally A d M g) k z u ⟨i, e⟩ =
      a.edgeCount d m R (b.code i) (b.here A g i) e k (b.encodeLog a μ d m R k z u i) := by
  induction k generalizing z with
  | zero =>
    refine (b.tally_at A g d M z i e).trans ?_
    refine sum_congr rfl fun j _ => congrArg _ (min_eq_left ?_).symm
    exact (Nat.le_add_right _ _).trans (hz (b.request A i j))
  | succ k ih =>
    have hb (x) : b.after a μ d m z u.1 x + k * rateBound a m ≤ R := by
      have h := b.after_bound a μ d m room hm hd z u.1 x
      have hh := hz x
      rw [Nat.succ_mul] at hh
      unfold rateBound at hh ⊢
      omega
    exact congrArg₂ (· + ·) (b.step_count a m (b.stockPrice (M := M) μ d z) i e u.1)
      (ih _ hb u.2)

end Market
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# A local guard for each selector

On a group action, all these guards pass precisely for those
selectors representing a branch of the scheduled protocol.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
open scoped Classical Pointwise

variable {K G J : Type} [Field K] [Group G] {U : J → Subgroup G} {g : G}
  (p : Parameters K U g)

/-- Positive scale and bounded stock fit every branch simultaneously. -/
structure Clock where
  height : ℕ
  μ : ℕ
  width : ℕ
  room : p.offers.Room (2 ^ height)
  wide : 4 ≤ width
  runs : ∀ (I : Type) [Fintype I] [Nonempty I] [MulAction G I],
    let b := p.balls I
    Runs (b.payload p.table) (b.cap p.table p.path p.limit)
      (b.decision p.offers μ p.path (2 ^ height)) (1203 * Fintype.card I * width) width 0 0

theorem has_clock : Nonempty p.Clock := by
  let _ : Nonempty p.sites := ⟨⟨1, p.start⟩⟩
  obtain ⟨h, μ, W, hm, _, hw, h⟩ := p.offers.schedule (p.path_pos.trans_le p.pay) p.pos
  exact ⟨⟨_, μ, W, hm, hw, fun I _ _ _ => h I (p.balls I) _ p.pay (p.frequent I)⟩⟩

variable {p} (c : p.Clock)
namespace Clock

abbrev batch := 2 ^ c.height
abbrev bound := c.width * Market.rateBound p.offers c.batch
abbrev bits := p.offers.bits c.batch c.bound c.width
abbrev Input := Decor G c.bits

variable {t : ℕ} (w : Fin (2 ^ t) → G)

def guard (x : c.Input) : Bool :=
  decide (p.offers.Accept c.batch c.bound t c.μ p.path c.width
    (Board.choose p.core p.radius p.unit g p.reach x.toRoot).1
    (observations p.table p.core p.radius p.unit g p.reach w x.toRoot)
    (x.mark (x.label 1)) (fun j => x.mark (x.label (w j))))

theorem guard_local : Decor.Local (c.guard w) := by
  have ha := Board.local_choose p.core p.radius p.unit g p.reach
  have hb := local_observations p.table p.core p.radius p.unit g p.reach w
  have hm : Decor.Local (fun x : c.Input => fun j => x.mark (x.label (w j))) :=
    Decor.local_pi fun j => Decor.local_mark _
  exact ((Decor.local_root (ha.pair hb)).pair ((Decor.local_mark 1).pair hm)).map fun y =>
    decide (p.offers.Accept c.batch c.bound t c.μ p.path c.width y.1.1.1 y.1.2 y.2.1 y.2.2)

variable (hw : Set.range w = offsets p.core p.radius)
  {I : Type} [Fintype I] [MulAction G I] (z : I → Fin (2 ^ c.bits))

abbrev path (I : Type) [Fintype I] [MulAction G I] :=
  (p.balls I).Path p.offers c.μ p.path c.batch c.width 0

def selector (u : c.path I) : I → Fin (2 ^ c.bits) :=
  (p.balls I).selector p.offers c.batch c.bound c.μ p.path c.width u

include hw in
theorem guard_iff :
    (∀ i, c.guard w ⟨⟨I, i⟩, z⟩ = true) ↔ ∃! u : c.path I, c.selector u = z := by
  let _ : Nonempty p.sites := ⟨⟨1, p.start⟩⟩
  let b := p.balls I
  let a := marketPorts (I := I) p.core p.radius p.unit g p.reach w hw
  have he (i) := observations_eq p.table p.core p.radius p.unit g p.reach w hw (i : I)
  have h : (∀ i, c.guard w ⟨⟨I, i⟩, z⟩ = true) ↔
      b.Legal p.offers c.batch c.bound a c.μ p.path c.width z := by
    unfold guard
    simp only [decide_eq_true_eq, he, Root.label, one_smul]
    rfl
  rw [h, b.legal_iff p.offers c.batch c.bound a c.μ p.path c.room
    (p.path_pos.trans_le p.pay) p.pay _ le_rfl]
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu, fun _ he =>
    b.selector_injective p.offers c.batch c.bound c.μ p.path c.width (he.trans hu.symm)⟩,
    fun h => h.exists⟩

end Clock
end OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
end

/-! # A finite local test for the designated depot -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral
open scoped Classical Pointwise

variable {G K S : Type} [Group G] [Field K] [Fintype S] [Nonempty S]
  (A : Finset (Tensor K S)) (H : Finset G) (r : ℕ) (hH : 1 ∈ H) (g : G) (hg : g ∈ H ^ r)
  {t : ℕ} (w : Fin (2 ^ t) → G) (j₀ : Fin (2 ^ t))

def owns (x : Root G) (u : Key (H ^ r).card A) : Bool :=
  decide (∀ j v, observations A H r hH g hg w x j u v = true →
    keys H r w A hH g hg x j₀ u ≤ keys H r w A hH g hg x j u)

theorem owns_local : Root.Local (owns A H r hH g hg w j₀) :=
  ((local_observations A H r hH g hg w).pair (local_keys H r w A hH g hg)).map
    fun p u => decide (∀ j v, p.1 j u v = true → p.2 j₀ u ≤ p.2 j u)

variable {I : Type} [MulAction G I] [Fintype I] [DecidableEq I]
  (hw : Set.range w = offsets H r) (h₀ : w j₀ = 1)

include h₀ in
theorem owns_here (i : I) (u : ((market H hH r g hg).code i).Req A) :
    let b := market H hH r g hg
    owns A H r hH g hg w j₀ ⟨I, i⟩ ⟨b.code i, u⟩ =
      b.here A (marketPorts H r hH g hg w hw) i u := by
  let b := market (I := I) H hH r g hg
  let P := marketPorts (I := I) H r hH g hg w hw
  let x := b.home A (b.request A i u)
  apply Bool.eq_iff_iff.mpr
  simp only [owns, Market.here, decide_eq_true_eq]
  rw [observations_eq A H r hH g hg w hw i]
  simp only [keys_eq H r w A hH g hg hw, h₀, one_smul]
  change (∀ j v, b.mask A P i j ⟨_, u⟩ v = true → P.key x i ≤ P.key x (P.addr j i)) ↔
    b.depot A P (b.requestOf A ⟨i, u⟩) = ⟨i, u⟩
  rw [b.depot_iff]
  constructor
  · intro h j hj v hv
    change j ∈ b.neighbors i at hj
    rw [← P.image] at hj
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
    exact h _ ⟨_, v⟩ ((b.mask_test A P i l u v).mpr ⟨hl, hv.symm⟩)
  · intro h j v hv
    rw [Market.mask, decide_eq_true_eq] at hv
    obtain ⟨hj, a, c, he, _, hreq⟩ := hv
    have he' : u = a := eq_of_heq (Sigma.mk.inj he).2
    subst a
    exact h _ (b.overlap_neighbor A _ _ _ _ hreq) c hreq.symm

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Programming edge widths from the bounded transcript
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
open scoped Classical Pointwise

variable {K G J : Type} [Field K] [Group G] {U : J → Subgroup G} {g : G}
  {p : Parameters K U g}

instance inhabitedSites : Nonempty p.sites := ⟨⟨1, p.start⟩⟩

namespace Clock

variable (c : p.Clock)
abbrev Spot := Address p.core p.radius
abbrev Index := Key (p.core ^ p.radius).card p.table

def read (v : Fin (2 ^ c.bits)) (here : Index (p := p) → Bool) (e : Spot (p := p)) : ℕ :=
  if h : ∃ x, p.offers.write c.batch c.bound ⟨e.1.1, x⟩ = v then
    p.offers.edgeCount p.path c.batch c.bound e.1.1 (fun u => here ⟨_, u⟩) e.2 c.width h.choose
  else 0

theorem read_eq (here : Index (p := p) → Bool) (e : Spot (p := p))
    (u : p.offers.Timeline c.batch c.bound e.1.1 c.width) :
    c.read (p.offers.write c.batch c.bound ⟨e.1.1, u⟩) here e =
      p.offers.edgeCount p.path c.batch c.bound e.1.1 (fun j => here ⟨_, j⟩) e.2 c.width u := by
  have h : ∃ x, p.offers.write c.batch c.bound ⟨e.1.1, x⟩ = p.offers.write c.batch c.bound ⟨e.1.1, u⟩ :=
    ⟨u, rfl⟩
  have he := (p.offers.write c.batch c.bound).injective h.choose_spec
  rw [read, dite_eq_left h, eq_of_heq (Sigma.mk.inj he).2]

variable {t : ℕ} (w : Fin (2 ^ t) → G) (j₀ : Fin (2 ^ t))

def count (x : c.Input) := c.read (x.mark (x.label 1))
  (owns p.table p.core p.radius p.unit g p.reach w j₀ x.toRoot)

theorem count_local : Decor.Local (c.count w j₀) :=
  ((Decor.local_mark 1).pair (Decor.local_root
    (owns_local p.table p.core p.radius p.unit g p.reach w j₀))).map (fun x => c.read x.1 x.2)

theorem count_bound : ∃ B : ℕ, ∀ x e, c.count w j₀ x e ≤ B := by
  let T := Fin (2 ^ c.bits) × (Index (p := p) → Bool) × Spot (p := p)
  let _ : Fintype T := Fintype.ofFinite _
  let f (v : T) := c.read v.1 v.2.1 v.2.2
  refine ⟨Finset.univ.sup f, fun x e => ?_⟩
  exact Finset.le_sup (f := f) (Finset.mem_univ (x.mark (x.label 1),
    owns p.table p.core p.radius p.unit g p.reach w j₀ x.toRoot, e))

variable (hw : Set.range w = offsets p.core p.radius) (h₀ : w j₀ = 1)
  {I : Type} [Fintype I] [MulAction G I]

def widthAt (u : c.path I) : (p.balls I).Edge → ℕ :=
  let b := p.balls I
  let a := marketPorts (I := I) p.core p.radius p.unit g p.reach w hw
  Protocol.edges (b.payload p.table) (b.decision p.offers c.μ p.path c.batch)
    (b.tally p.table p.path p.limit a) c.width 0 u

include h₀ in
theorem count_branch (u : c.path I) (e : (p.balls I).Edge) :
    c.count w j₀ ⟨⟨I, e.1⟩, c.selector u⟩ (address p.core p.unit p.radius g p.reach e) =
      c.widthAt w hw u e := by
  rcases e with ⟨i, e⟩
  let b := p.balls I
  let a := marketPorts (I := I) p.core p.radius p.unit g p.reach w hw
  let v := b.encodeLog p.offers c.μ p.path c.batch c.bound c.width 0 u i
  let here := owns p.table p.core p.radius p.unit g p.reach w j₀ ⟨I, i⟩
  let o := address p.core p.unit p.radius g p.reach (⟨i, e⟩ : b.Edge)
  have he : (fun j => here ⟨b.code i, j⟩) = b.here p.table a i :=
    funext fun j => owns_here _ _ _ _ _ _ w j₀ hw h₀ i j
  simp only [count, Root.label, one_smul]
  refine (c.read_eq here o v).trans ?_
  change p.offers.edgeCount _ _ _ (b.code i) (fun j => here ⟨b.code i, j⟩) e _ v = _
  rw [he]
  exact (b.edge_count p.offers c.μ p.path c.batch c.bound a c.room
    (p.path_pos.trans_le p.pay) p.pay _ _ (fun _ => by simp [bound]) u i e).symm

theorem width_total [Nonempty I] (u : c.path I) :
    (∑ e, c.widthAt w hw u e) ≤ 1203 * Fintype.card I * c.width := by
  let b := p.balls I
  let a := marketPorts (I := I) p.core p.radius p.unit g p.reach w hw
  have h := Protocol.edges_cost (b.payload p.table) (b.decision p.offers c.μ p.path c.batch)
    (b.tally p.table p.path p.limit a) (b.tally_cost _ _ _ _ (p.ready I) p.local_supply) (c.runs I) u
  rw [zero_add] at h
  change (↑(∑ e, c.widthAt w hw u e) : ℝ) ≤ _ at h
  exact_mod_cast h

end Clock
end OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
end

/-!
# Fixed choices for a transport program

The clock, offset list, and bank of physical slots are fixed across
actions, input permutations and scales.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Coloring Transport
open scoped Classical Pointwise

variable {F G J : Type} [Field F] [Group G] {U : J → Subgroup G} {g : G}
    (a : Parameters F U g)

structure Rig where
  clock : a.Clock
  t : ℕ
  w : B t → G
  hw : Set.range w = offsets a.core a.radius
  j₀ : B t
  h₀ : w j₀ = 1
  R : ℕ
  bound : ∀ x e, clock.count w j₀ x e ≤ R
  p : ℕ
  bank : Bank a.core a.radius R p

theorem Parameters.rig : Nonempty (Rig a) := by
  obtain ⟨c⟩ := a.has_clock
  obtain ⟨t, w, hw⟩ := exists_offsets a.core a.radius a.unit
  have hx : (1 : G) ∈ Set.range w := by
    rw [hw]
    have h := Finset.one_mem_pow (n := a.radius) a.unit
    change 1 ∈ a.core ^ a.radius * (a.core ^ a.radius)⁻¹
    simpa only [inv_one, mul_one] using Finset.mul_mem_mul h (Finset.inv_mem_inv h)
  obtain ⟨j, hj⟩ := hx
  obtain ⟨R, hR⟩ := c.count_bound w j
  let V := Socket a.core a.radius R
  let _ : Fintype V := Fintype.ofFinite V
  exact ⟨⟨c, t, w, hw, j, hj, R, hR, _, Coloring.encode V⟩⟩

namespace Rig
variable {a} (s : Rig a) {I : Type} [Fintype I] [MulAction G I]

abbrev count := s.clock.count s.w s.j₀
abbrev widthAt (u : s.clock.path I) := s.clock.widthAt s.w s.hw u

theorem bounded (u : s.clock.path I) (e : (a.balls I).Edge) : s.widthAt u e ≤ s.R := by
  rw [widthAt, ← s.clock.count_branch s.w s.j₀ s.hw s.h₀]
  exact s.bound _ _

def endpoints (u : s.clock.path I) : Protocol.End (s.widthAt u) ↪ I × B s.p :=
  s.bank.endpoints a.unit g a.reach (s.widthAt u) (s.bounded u)

def program {l : ℕ} (f : s.clock.Input → B l) (x : s.clock.Input) : Decor.Plan l s.p s.p :=
  (f x, s.bank.program a.unit g a.reach s.count x)

theorem program_local {l : ℕ} {f : s.clock.Input → B l} (hf : Decor.Local f) :
    Decor.Local (s.program f) :=
  hf.pair (s.bank.program_local a.unit g a.reach s.count (s.clock.count_local s.w s.j₀))

end Rig
end OAI.LinearAlgebra.MatrixExponent.Routing
end
