import OAI.Computability.NearSquareRoot.CRTControlledBenesPrefix
import OAI.Computability.NearSquareRoot.CRTControlledBenesRead
import OAI.Computability.NearSquareRoot.CRTControlledMask

/-! # Compiled Beneš switches in the packed XOR stage

A prepared prefix contains the external controls and all nontarget bits of each
active block. A polynomial command reads the header and this prefix to select each
block's permutation table and address. The mask is then computed from these tables
by the finite P192 compiler and table reader.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic
open IntegerMultiplication.Packed IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Loom NearSquareRoot.Controlled

abbrev SwitchQuery := (Tally × RawTable) × Bool × Tally × List Bool

/-- Generate the actual local switch table and read its selected column and row. -/
def queryBit (q : SwitchQuery) : Bool :=
  switchBit (generateTables q.1,q.2)

theorem queryBit_poly : Poly queryBit :=
  ((Easy.fst.poly.compose generateTables_poly).pair Easy.snd.poly).compose switchBit_poly

def query (d : ℕ) (t : RawTable) (side : Bool) (j : ℕ) (s : Word d) : SwitchQuery :=
  ((tally d,t),side,tally j,List.ofFn s)

/-- A header supplies the per-block table descriptions and the physical prefix
supplies the nontarget bits. Compiling and reading all local queries is charged. -/
theorem queryVectorTrace {X Hdr : Type} [Codec Hdr] {r : Regime X} {P : X → Tape}
    (i : X → ℕ) (queries : (x : X) → Pin (P x) → Fin (i x) → SwitchQuery)
    (header : X → Hdr) (hh : r.Has header) (prefixWord : (x : X) → Pin (P x) → List Bool)
    (hp : Strip.Trace r (fun x => layout (P x)) fun x a => send (prefixWord x a))
    (prepare : Hdr × List Bool → List SwitchQuery) (hprepare : Poly prepare)
    (prepared : ∀ x a, prepare (header x,prefixWord x a) = List.ofFn (queries x a)) :
    Strip.Trace r (fun x => layout (P x)) (fun x a => send (List.ofFn fun b => queryBit (queries x a b))) := by
  let hat := fun (x : X) (a : Pin (P x)) => send (prefixWord x a)
  let rr := onboard r hat hp.meter
  have h₁ : rr.Has (fun y : Sigma (fun x => Pin (P x)) => header y.1) :=
    onboard_small hat hp.meter _ hh
  have h₂ : rr.Has (fun y : Sigma (fun x => Pin (P x)) => prefixWord y.1 y.2) :=
    onboard_hat hat hp.meter
  apply hp.tune
  change rr.Has (fun y : Sigma (fun x => Pin (P x)) => List.ofFn fun b => queryBit (queries y.1 y.2 b))
  have z := ((h₁.pair h₂).thenDo hprepare).thenDo (Poly.maps queryBit queryBit_poly)
  simpa only [prepared,List.map_ofFn,Function.comp_def] using z

/-- Reinsert the separately stored target bit in a block. A padded stage may have
its depth beyond the end of this block. -/
def fillBit {d : ℕ} (j : ℕ) (s : Word d) (v : Bool) : Word d :=
  if h : j < d then Function.update s ⟨j,h⟩ v else s

theorem rawSetting_fill {d : ℕ} (t : RawTable) (j : ℕ) (s : Word d) (v : Bool) :
    rawSetting t j (List.ofFn (fillBit j s v)) = rawSetting t j (List.ofFn s) := by
  unfold fillBit
  split
  · exact rawSetting_update t _ s v
  · rfl

private theorem clear_digit (a : Fin 2) : maskDigit (title a) = a := by fin_cases a <;> decide

/-- Physical destination digit for one slot of a batch, obtained by applying its
compiled word permutation to the reconstructed input word. -/
def switchedDigit {d : ℕ} (t : RawTable) (side : Bool) (j : ℕ) (s : Word d)
    (v : Fin 2) : Fin 2 :=
  if h : j < d then maskDigit (stagePerm t side j (fillBit j s (title v)) ⟨j,h⟩) else v

theorem switchedDigit_correct {d : ℕ} {t : RawTable} {p : Equiv.Perm (Word d)}
    (h : RawRepresents p t) (side : Bool) (j : ℕ) (s : Word d) (v : Fin 2) :
    maskDigit (title v ^^ queryBit (query d t side j s)) = switchedDigit t side j s v := by
  unfold queryBit query switchedDigit
  rw [switchBit_generated h]
  by_cases hj : j < d
  · simp [hj,stagePerm_apply,fillBit,rawSetting_update t (⟨j,hj⟩ : Fin d) s (title v)]
  · simp [hj,clear_digit]

theorem fill_switchedDigit {d : ℕ} (t : RawTable) (side : Bool) (j : ℕ)
    (s : Word d) (v : Fin 2) :
    fillBit j s (title (switchedDigit t side j s v)) = stagePerm t side j (fillBit j s (title v)) := by
  by_cases hj : j < d
  · funext k
    by_cases e : j = k.val
    · subst j
      have digit (z : Bool) : title (maskDigit z) = z := by cases z <;> decide
      simp [fillBit,switchedDigit,digit]
    · simp [fillBit,switchedDigit,hj,stagePerm_apply,e,Fin.ext_iff,Ne.symm e]
  · simp [fillBit,hj,stagePerm_past_end t side (Nat.le_of_not_gt hj)]

def switchedQueue {H L i : ℕ} (w : Fin i → ℕ) (t : Fin i → RawTable)
    (s : (b : Fin i) → Word (w b)) (side : Bool) (j : ℕ) (q : Queue H L i) : Queue H L i :=
  (q.1,fun b => ((q.2.1 b).1,(q.2.1 b).2.1,switchedDigit (t b) side j (s b) (q.2.1 b).2.2),q.2.2)

theorem maskTarget_compiled {H L i : ℕ} (w : Fin i → ℕ) (t : Fin i → RawTable)
    (p : (b : Fin i) → Equiv.Perm (Word (w b))) (ht : ∀ b, RawRepresents (p b) (t b))
    (s : (b : Fin i) → Word (w b)) (side : Bool) (j : ℕ) (q : Queue H L i) :
    maskTarget (fun b => queryBit (query (w b) (t b) side j (s b))) q = switchedQueue w t s side j q := by
  simp only [maskTarget,switchedQueue,switchedDigit_correct (ht _)]

/-- Zero-based prefix bit positions. Any offset at or beyond the end reads false
and can be used as the placeholder for the missing target. -/
def prefixBit (a : List Bool × Tally) := (a.1.drop a.2.length).headD false

theorem prefixBit_poly : Poly prefixBit :=
  (easy_cut Easy.exchange).sndCompose.poly.compose easyWordHead.poly

def prefixBits (a : List Bool × List Tally) := a.2.map fun k => prefixBit (a.1,k)

theorem prefixBits_poly : Poly prefixBits :=
  Poly.push [] [] prefixBit_poly

abbrev BlockPlan (A : Type) := A × Tally × List Tally
abbrev BatchPlan (A : Type) := (Bool × Tally × List Tally) × List (BlockPlan A)

private abbrev Frame := Bool × Tally × List Bool × List Bool

private def buildQuery {A : Type} (table : A × List Bool → RawTable)
    (q : Frame × BlockPlan A) : SwitchQuery :=
  ((q.2.2.1, table (q.2.1,q.1.2.2.1)),q.1.1,q.1.2.1,prefixBits (q.1.2.2.2,q.2.2.2))

private theorem buildQuery_poly {A : Type} [Codec A] (table : A × List Bool → RawTable)
    (ht : Poly table) : Poly (buildQuery table) := by
  let X := Frame × BlockPlan A
  have ft := (show Poly (fun q : X => (q.2.1,q.1.2.2.1)) by fun_prop).compose ht
  have ft' := (show Poly (fun q : X => q.2.2.1) by fun_prop).pair ft
  have fx := (show Poly (fun q : X => (q.1.2.2.2,q.2.2.2)) by fun_prop).compose prefixBits_poly
  exact ft'.pair ((show Poly (fun q : X => q.1.1) by fun_prop).pair
    ((show Poly (fun q : X => q.1.2.1) by fun_prop).pair fx))

/-- Assemble all queries from one header and the actual nontarget prefix.
The supplied table program receives only the designated external controls. -/
def buildBatch {A : Type} (table : A × List Bool → RawTable) (q : BatchPlan A × List Bool) :=
  q.1.2.map fun b => buildQuery table
    ((q.1.1.1,q.1.1.2.1,prefixBits (q.2,q.1.1.2.2),q.2),b)

theorem buildBatch_poly {A : Type} [Codec A] (a : A) (table : A × List Bool → RawTable)
    (ht : Poly table) : Poly (buildBatch table) := by
  let X := BatchPlan A × List Bool
  have ext := (show Poly (fun q : X => (q.2,q.1.1.2.2)) by fun_prop).compose prefixBits_poly
  have ctx := (show Poly (fun q : X => q.1.1.1) by fun_prop).pair
    ((show Poly (fun q : X => q.1.1.2.1) by fun_prop).pair (ext.pair Easy.snd.poly))
  exact (ctx.pair (show Poly (fun q : X => q.1.2) by fun_prop)).compose
    (Poly.push (false,[],[],[]) (a,[],[]) (buildQuery_poly table ht))

def makePlan {A : Type} {i : ℕ} (side : Bool) (j : ℕ) (outer : List Tally)
    (w : Fin i → ℕ) (tag : Fin i → A) (pos : (b : Fin i) → Fin (w b) → ℕ) : BatchPlan A :=
  ((side,tally j,outer),List.ofFn fun b => (tag b,tally (w b),List.ofFn fun k => tally (pos b k)))

def prefixWordAt {d : ℕ} (pos : Fin d → ℕ) (z : List Bool) : Word d :=
  fun k => prefixBit (z,tally (pos k))

theorem buildBatch_plan {A : Type} {i : ℕ} (table : A × List Bool → RawTable)
    (side : Bool) (j : ℕ) (outer : List Tally) (w : Fin i → ℕ) (tag : Fin i → A)
    (pos : (b : Fin i) → Fin (w b) → ℕ) (z : List Bool) :
    buildBatch table (makePlan side j outer w tag pos,z) = List.ofFn (fun b =>
      query (w b) (table (tag b,prefixBits (z,outer))) side j (prefixWordAt (pos b) z)) := by
  simp [buildBatch,buildQuery,makePlan,query,prefixBits,List.map_ofFn,Function.comp_def]
  rfl

/-- The represented batch descriptor specifies external-control positions once, and
a tag, block size, and nontarget prefix positions for each slot. -/
theorem binaryQueriesTrace {A X : Type} [Codec A] (blank : A) {r : Regime X}
    (table : A × List Bool → RawTable) (compute : Poly table) (n i : X → ℕ)
    (side : X → Bool) (j : X → ℕ) (outer : X → List Tally)
    (w : (x : X) → Fin (i x) → ℕ) (tag : (x : X) → Fin (i x) → A)
    (pos : (x : X) → (b : Fin (i x)) → Fin (w x b) → ℕ)
    (hn : r.Has (tally ∘ n))
    (hh : r.Has (fun x => makePlan (side x) (j x) (outer x) (w x) (tag x) (pos x))) :
    Strip.Trace r (fun x => layout (List.replicate (n x) 2)) (fun x a => send (List.ofFn fun b =>
      queryBit (query (w x b) (table (tag x b,prefixBits (pinBits a,outer x))) (side x) (j x)
        (prefixWordAt (pos x b) (pinBits a))))) := by
  exact queryVectorTrace i _ _ hh (fun _ a => pinBits a) (prefixTrace n hn)
    (buildBatch table) (buildBatch_poly blank table compute)
    (fun _ _ => buildBatch_plan ..)

/-- Charged simultaneous switches on a binary prepared prefix. Every output target
digit is the selected bit of its compiled word permutation, and the physical stage
preserves all the guard and spectator digits. -/
theorem compiledMaskedStage {A X : Type} [Codec A] (blank : A) {r : Regime X} {l : X → ℕ}
    (table : A × List Bool → RawTable) (compute : Poly table)
    (H L i n : X → ℕ) (G S : X → Tape) (side : X → Bool) (j : X → ℕ) (outer : X → List Tally)
    (w : (x : X) → Fin (i x) → ℕ) (tag : (x : X) → Fin (i x) → A)
    (pos : (x : X) → (b : Fin (i x)) → Fin (w x b) → ℕ)
    (p : (x : X) → Pin (List.replicate (n x) 2) → (b : Fin (i x)) → Equiv.Perm (Word (w x b)))
    (correct : ∀ x a b, RawRepresents (p x a b) (table (tag x b,prefixBits (pinBits a,outer x))))
    (hn : r.Has (tally ∘ n))
    (hh : r.Has (fun x => makePlan (side x) (j x) (outer x) (w x) (tag x) (pos x)))
    (ρ : ℝ) {U : X → Type} (u : (x : X) → Series (U x))
    (hc : r.Has (tally ∘ extent H L i)) (shape : r.Has fun x => signs (H x) (L x) (i x))
    (sparse : ∀ x, (3 * extent H L i x + 1) * (32 * i x) ≤ 2 ^ width (H x) (L x))
    (hg : Told r G) (hs : Told r S)
    (guard : ∀ x a, a ∈ List.replicate (n x) 2 ++ G x ++ S x → a ≤ Net.Shuttle.base)
    (sw : RectInterchange r (extent H L i) ρ) (z : ∀ x, (u x).count ≤ l x) (hr : 0 ≤ ρ)
    (f : (x : X) → RotationAddress H L i (fun y => List.replicate (n y) 2) G S x → U x → Bead) :
    let rows := rotationLayout H L i (fun y => List.replicate (n y) 2) G S
    Breeze (Spindle.modes (extent H L i) (τ := ρ)) r (fun x => (rows x).count) l
      (together r.header (cloth rows u f)) (cloth rows u fun x a => f x (a.1,
        switchedQueue (w x) (fun b => table (tag x b,prefixBits (pinBits a.1,outer x)))
          (fun b => prefixWordAt (pos x b) (pinBits a.1)) (side x) (j x) a.2.1,
        a.2.2.1,a.2.2.2.1,a.2.2.2.2)) := by
  let P := fun x : X => List.replicate (n x) 2
  have read := binaryQueriesTrace blank table compute n i side j outer w tag pos hn hh
  have hP : Told r P := by
    simpa only [P,field_replicate] using (Told.carrier (q := 2) (by decide) n hn)
  have run := maskedXorStage H L i P G S ρ u _ hc shape sparse hP hg hs guard sw read z hr f
  simpa only [maskTarget_compiled _ _ _ (correct _ _)] using run

/-- Passing the same direction bit in each local tag selects the common forward
or inverse routing on the batch. -/
def directedTable {A : Type} (table : A × List Bool → RawTable) (q : (Bool × A) × List Bool) :=
  let t := table (q.1.2,q.2)
  bif q.1.1 then inverseTable t else t

theorem directedTable_poly {A : Type} [Codec A] (table : A × List Bool → RawTable)
    (ht : Poly table) : Poly (directedTable table) := by
  let X := (Bool × A) × List Bool
  have t := (show Poly (fun q : X => (q.1.2,q.2)) by fun_prop).compose ht
  exact Poly.choose (show Poly (fun q : X => q.1.1) by fun_prop) (t.compose inverseTable_poly) t

theorem directedTable_represents {A : Type} {d : ℕ} {p : Equiv.Perm (Word d)}
    (table : A × List Bool → RawTable) (tag : A) (controls : List Bool) (rev : Bool)
    (ht : RawRepresents p (table (tag,controls))) :
    RawRepresents (bif rev then p.symm else p) (directedTable table ((rev,tag),controls)) := by
  cases rev
  · exact ht
  · exact inverseTable_represents ht

end Benes

end NearSquareRoot
end Computability
end OAI
