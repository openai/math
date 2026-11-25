import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenSuffix
import OAI.Computability.BorderVNP.CubeISAOwnedTrace
import OAI.Computability.BorderVNP.CubeScatterPaddingTail
import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

/-! # Native control returns and the two physical padding pins

At the return of the owned packet scans the signed evaluator runs the same
four instructions as the finite evaluator. Across all teams, this part of a
preparation has a unique returning chronology exactly when both ends of every
unused physical slot are zero. Its output is the memory on which the private
bottom-report stage actually starts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.OpenSuffix

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator BorderVNP.Cube DiagonalResidueRAM

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {start : Bank w} {mem : Memory w}

/-- The trace consumes no private choices, carries only positive signs, fits the
physical cost bound, and returns the actual host, bundle and control writes. -/
def Inputs.ReturnImage (H : Inputs) (ret : Returns SignedPrep.controls pub mac start mem) : Prop :=
  TraceOK ret.val.1 [] ret.val.1.length ∧ traceCost ret.val.1 ≤ H.cost (pub 0).val (readings mem) ∧
    readings ret.val.2.2 = H.image (pub 0).val (readings mem)

/-- Equality of the event stream, final register bank and complete RAM of two
returning executions of the four native control stages. -/
theorem control_return_unique (p q : Returns SignedPrep.controls pub mac start mem) : p=q := by
  have eqn := p.property.unique_of_deterministic (by decide) q.property
  exact Subtype.ext (Prod.ext eqn.1 (Prod.ext eqn.2.1 eqn.2.2))

variable (H : Inputs) (ready : Ready H (pub 0).val (readings mem) w)

include ready in
/-- The native four-stage return exists and is unique exactly when the padding
test on its starting word memory passes. -/
theorem unique_return_iff_valid :
    (∃! ret : Returns SignedPrep.controls pub mac start mem, H.ReturnImage ret) ↔
      (Padding.Layout.fromFrame (pub 0).val (readings mem)).Valid (readings mem) := by
  constructor
  · rintro ⟨ret,_,_⟩
    exact ((run H ready).sound ret.property).1
  · intro valid
    obtain ⟨es,r,m,path,clean,cost,words⟩ := Owned.traceRun_unsigned
      ((run (s := start) H ready).complete valid) (by decide)
    exact ⟨⟨(es,r,m),path⟩,⟨clean,cost,words⟩,fun other _ => control_return_unique other _⟩

include ready in
/-- Any actual return, including one extracted from a longer preparation, passes
the local guard and has the indicated trace, cost and complete post-control memory. -/
theorem control_return_facts (ret : Returns SignedPrep.controls pub mac start mem) :
    (Padding.Layout.fromFrame (pub 0).val (readings mem)).Valid (readings mem) ∧ H.ReturnImage ret := by
  have valid := ((run H ready).sound ret.property).1
  obtain ⟨p,hp,_⟩ := (unique_return_iff_valid (start := start) H ready).2 valid
  exact ⟨valid,control_return_unique p ret ▸ hp⟩

section ControlFamily

variable {Team : Type*}

/-- Simultaneous returns from the real post-ownership banks, including every
team's complete event stream, final registers and word memory. -/
abbrev TeamControls (pub : Team → Arg → Word w) (mac : Team → TeamOpcode.Macros w 8)
    (reg : Team → Bank w) (mem : Team → Memory w) :=
  ∀ u, Returns SignedPrep.controls (pub u) (mac u) (reg u) (mem u)

/-- The exact relation of the native controls to a given physical condition.
Every returning family satisfies the image description, including families
extracted from longer preparations with arbitrary subsequent report choices. -/
structure ControlFamily (program : Team → Inputs) (pub : Team → Arg → Word w)
    (mac : Team → TeamOpcode.Macros w 8) (reg : Team → Bank w) (mem : Team → Memory w)
    (pins : Prop) : Prop where
  /-- Unique successful family including its physical trace and output conditions. -/
  unique : (∃! ret : TeamControls pub mac reg mem, ∀ u, (program u).ReturnImage (ret u)) ↔ pins
  /-- A simultaneous return exists exactly on the admitted physical assignments. -/
  returns : Nonempty (TeamControls pub mac reg mem) ↔ pins
  /-- Every returning family computes the specified outputs at all report inputs. -/
  images : ∀ ret : TeamControls pub mac reg mem, ∀ u, (program u).ReturnImage (ret u)

/-- On the actual four-stage entry operands, any returning family is the one
physical family singled out by the success condition. -/
theorem ControlFamily.of_ready {program : Team → Inputs} {publicWord : Team → Arg → Word w}
    {macros : Team → TeamOpcode.Macros w 8} {reg : Team → Bank w} {ram : Team → Memory w}
    {pins : Prop} (readyTeam : ∀ u, Ready (program u) (publicWord u 0).val (readings (ram u)) w)
    (unique : (∃! ret : TeamControls publicWord macros reg ram, ∀ u, (program u).ReturnImage (ret u)) ↔ pins) :
    ControlFamily program publicWord macros reg ram pins := by
  have images (ret : TeamControls publicWord macros reg ram) (u : Team) :=
    (control_return_facts (program u) (readyTeam u) (ret u)).2
  refine ⟨unique,⟨?_,?_⟩,images⟩
  · rintro ⟨ret⟩
    exact unique.mp ⟨ret,images ret,fun other _ => funext fun u => control_return_unique (other u) (ret u)⟩
  · intro passed
    exact ⟨(unique.mpr passed).exists.choose⟩

end ControlFamily

open VPVNP.MotifBase HostAddress Crossing Physical NativeIntervals

variable {Team : Type*} {n d blocks b h K s D m : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
variable {N : Network D P bits} {cell : N.Site → Cell} {interval : NativeIntervals.Layout}
variable {before dir : ℕ → ℕ} {ord : N.CrossingEdge cell ≃ Fin m} {row : Fin m ↪o Fin interval.count}
variable {cells : Cell ↪ ℕ} {label : Cell → Label (n+1) d} {hz : d^(n+1) = interval.alphabet}
variable (rows : PhysicalRows N cell interval before ord row cells label (productCode n d interval.alphabet hz))
variable (image : interval.Image before interval.count dir)
variable (cap : ∀ p, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
  (crossWidth N cell ∘ ord.symm) p ≤ blocks*(h*b))
variable {i : Fin (n+1)} {group : Fin d → Team} {number : Team ↪ ℕ}
variable {single : SingleSlot n d blocks (h*b) → Bool} {ends : Packet n d blocks → Ends n → Fin (h*b) → Bool}

section Teams

variable (program : Team → Inputs) (publicWord : Team → Arg → Word w)
variable (macros : Team → TeamOpcode.Macros w 8) (reg : Team → Bank w) (ram : Team → Memory w)

variable (readyTeam : ∀ t, Ready (program t) (publicWord t 0).val (readings (ram t)) w)
variable (banks : EndBanks i group (fun t => (Padding.Layout.fromFrame (publicWord t 0).val (readings (ram t))).packets)
  (fun t => (Padding.Layout.fromFrame (publicWord t 0).val (readings (ram t))).singles)
  (fun t => readings (ram t)) single ends K s)
variable (headers : ∀ t, Padding.TailHeader i group number t
  (Padding.Layout.fromFrame (publicWord t 0).val (readings (ram t))) (readings (ram t))
  (fun k => dir (interval.widths+k)) blocks b h K s)

include rows image readyTeam banks headers in
/-- A simultaneous returning control path exists precisely when the two physical
pins vanish on every unused slot. This path is unique as a dependent family
of actual traces, final register banks and word memories. -/
theorem team_returns_iff_pins :
    (∃! ret : ∀ t, Returns SignedPrep.controls (publicWord t) (macros t) (reg t) (ram t),
      ∀ t, (program t).ReturnImage (ret t)) ↔
    ∀ q ∉ Set.range (packedSlotEmbedding N cell ord label blocks (h*b) cap),
      readEnd single ends false q = false ∧ readEnd single ends true q = false := by
  have physical := Padding.valid_iff_pins (layout := fun t => Padding.Layout.fromFrame (publicWord t 0).val (readings (ram t)))
    rows image cap banks headers
  constructor
  · rintro ⟨ret,_,_⟩
    exact physical.mp fun t => (control_return_facts (program t) (readyTeam t) (ret t)).1
  · intro pins
    have valid := physical.mpr pins
    choose ret result using fun t => ((unique_return_iff_valid (start := reg t) (mac := macros t)
      (program t) (readyTeam t)).mpr (valid t)).exists
    exact ⟨ret,result,fun other _ => funext fun t => control_return_unique (other t) (ret t)⟩

end Teams

section Visits

variable (id : TableEntry n b h K s → ℕ) (program : Team → Inputs)
variable (publicWord : Team → Arg → Word w) (macros : Team → TeamOpcode.Macros w 8)
variable {initial : Team → Bank w} {input : Team → Memory w}
variable (v : ∀ t, SignedPrep.Visits id (publicWord t) (macros t) (initial t) (input t))

variable (readyTeam : ∀ t, Ready (program t) (publicWord t 0).val (readings (v t).owned.val.2.2) w)
variable (banks : EndBanks i group (fun t => (Padding.Layout.fromFrame (publicWord t 0).val (readings (v t).owned.val.2.2)).packets)
  (fun t => (Padding.Layout.fromFrame (publicWord t 0).val (readings (v t).owned.val.2.2)).singles)
  (fun t => readings (v t).owned.val.2.2) single ends K s)
variable (headers : ∀ t, Padding.TailHeader i group number t
  (Padding.Layout.fromFrame (publicWord t 0).val (readings (v t).owned.val.2.2)) (readings (v t).owned.val.2.2)
  (fun k => dir (interval.widths+k)) blocks b h K s)

include rows image readyTeam banks headers in
/-- Extract both zero pins from arbitrary returning signed preparations and identify
the precise memory, empty tape and positive trace at every actual report input. -/
theorem visits_control_pins :
    (∀ q ∉ Set.range (packedSlotEmbedding N cell ord label blocks (h*b) cap),
      readEnd single ends false q = false ∧ readEnd single ends true q = false) ∧
    ∀ t, (program t).ReturnImage (v t).controls := by
  have fact (t : Team) := control_return_facts (program t) (readyTeam t) (v t).controls
  have physical := Padding.valid_iff_pins
    (layout := fun t => Padding.Layout.fromFrame (publicWord t 0).val (readings (v t).owned.val.2.2))
    rows image cap banks headers
  exact ⟨physical.mp (fun t => (fact t).1),fun t => (fact t).2⟩

end Visits
end FiniteEvaluator.OpenSuffix

end BorderVNP
end Computability
end OAI
