import OAI.LinearAlgebra.MatrixExponent.Protocol.Focus
import OAI.LinearAlgebra.MatrixExponent.Protocol.Alignment
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Rig

/-!
# Local enumeration of terminal supplies

A request may be visible in several charts. Only its depot contributes
copies, including when the depot has no pins for that request at this site.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Spectral Finset Classical

variable {K S I I' : Type} [Field K] [Fintype S] [Nonempty S] [DecidableEq S]
  [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] {N t t' : ℕ}
  {A : Finset (Tensor K S)} {b : Market I N} {c : Market I' N} {s : I} {v : I'}
  {g : b.Ports t} {g' : c.Ports t'} {z : b.Request A → ℕ} {z' : c.Request A → ℕ}

def Match.Stocks (r : Match A b c s v) (z : b.Request A → ℕ) (z' : c.Request A → ℕ) : Prop :=
  ∀ (j : Near b s) (x : (b.code j.1).Req A) (x' : (c.code (r.near j).1).Req A),
    HEq x x' → z (b.request A j.1 x) = z' (c.request A (r.near j).1 x')

def assigned (g : b.Ports t) (z : b.Request A → ℕ) (j : Near b s) (x : (b.code j.1).Req A) :=
  if (b.depot A g (b.request A j.1 x)).1 = j.1 then z (b.request A j.1 x) else 0

abbrev SupplyUnit (g : b.Ports t) (z : b.Request A → ℕ) (s : I) :=
  Σ j : Near b s, Σ x : (b.code j.1).Req A, Fin (assigned g z j x)

namespace SupplyUnit

variable (u : SupplyUnit g z s)

def req := b.request A u.1.1 u.2.1

theorem depot : b.depot A g u.req = ⟨u.1.1, u.2.1⟩ := by
  have ha := u.2.2.pos
  unfold assigned at ha
  split at ha
  · rename_i he
    have hh := (b.depot_spec A g u.req).1
    change (b.depot A g u.req).1 = _ at he
    generalize b.depot A g u.req = w at *
    rcases w with ⟨i, x⟩
    change i = _ at he
    subst i
    have h : b.assign A _ (.inl x) = b.assign A _ (.inl u.2.1) := congrArg Sum.inl hh
    rw [Sum.inl.inj (b.assign_injective A _ h)]
  · exact (Nat.lt_irrefl _ ha).elim

def copy : Fin (z u.req) :=
  Fin.cast (ite_eq_left (congrArg Sigma.fst (depot u))) u.2.2

def unit : Units A b z := ⟨u.req, u.copy⟩

theorem injective : Function.Injective (unit : SupplyUnit g z s → Units A b z) := by
  rintro ⟨⟨i, a⟩, x, k⟩ ⟨⟨i', a'⟩, x', k'⟩ h
  have he := congrArg (fun p : Units A b z => b.depot A g p.1) h
  simp only [unit, depot] at he
  have hi : i = i' := congrArg Sigma.fst he
  subst i'
  have ha : a = a' := Subtype.ext ((b.name i).injective (a.property.trans a'.property.symm))
  subst a'
  have hx : x = x' := eq_of_heq (Sigma.mk.inj he).2
  subst x'
  have hk : k = k' := Fin.ext (congrArg (fun p : Units A b z => p.2.val) h)
  rw [hk]

theorem exists_unit (w : Units A b z) (h : ∃ i, b.name (b.depot A g w.1).1 i = s) :
    ∃ u : SupplyUnit g z s, u.unit = w := by
  have he := (b.depot_spec A g w.1).1
  generalize hd : b.depot A g w.1 = j at h he
  rcases j with ⟨j, x⟩
  rcases w with ⟨w, k⟩
  change b.request A j x = w at he
  subst w
  obtain ⟨i, hi⟩ := h
  let l : Near b s := ⟨j, ⟨i, hi⟩⟩
  have hk : assigned g z l x = z (b.request A j x) := ite_eq_left (congrArg Sigma.fst hd)
  exact ⟨⟨l, x, Fin.cast hk.symm k⟩, rfl⟩

@[to_additive sum_units]
theorem prod_units {P : Type} [CommMonoid P] (f : Units A b z → P)
    (hf : ∀ w, (∀ i, b.name (b.depot A g w.1).1 i ≠ s) → f w = 1) :
    ∏ w, f w = ∏ u : SupplyUnit g z s, f u.unit := by
  let e : SupplyUnit g z s ↪ Units A b z := ⟨unit, injective⟩
  change _ = ∏ u, f (e u)
  rw [← prod_map]
  symm
  refine prod_subset (subset_univ _) fun w _ hw => hf w fun i hi => ?_
  obtain ⟨u, rfl⟩ := exists_unit w ⟨i, hi⟩
  exact hw (mem_map_of_mem e (mem_univ u))

end SupplyUnit

variable (r : Match A b c s v) (hd : r.depots g g') (hz : r.Stocks z z')

include hd hz in
theorem Match.assigned_eq (j : Near b s)
    (x : (b.code j.1).Req A) (x' : (c.code (r.near j).1).Req A) (he : HEq x x') :
    assigned g z j x = assigned g' z' (r.near j) x' := by
  simp only [assigned, hd j x x' he, hz j x x' he]

include hd hz in
def Match.supplyUnits : SupplyUnit g z s ≃ SupplyUnit g' z' v :=
  Equiv.sigmaCongr r.near fun j =>
    Equiv.sigmaCongr (Equiv.cast (congrArg (fun i : Shape N => i.Req A) (r.same j))) fun x =>
      finCongr (r.assigned_eq hd hz j x _ (cast_heq _ _).symm)

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Local dependence of supply counts and copy positions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Spectral Finset Classical

variable {K S I I' : Type} [Field K] [Fintype S] [Nonempty S] [DecidableEq S]
  [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] {N t t' : ℕ}
  {A : Finset (Tensor K S)} {b : Market I N} {c : Market I' N} {s : I} {v : I'}
  {g : b.Ports t} {g' : c.Ports t'} {z : b.Request A → ℕ} {z' : c.Request A → ℕ}

abbrev SourceSpot (A : Finset (Tensor K S)) (N : ℕ) := Σ j : Spot N, j.1.Req A

def SupplyUnit.spot (u : SupplyUnit g z s) : SourceSpot A N := ⟨Protocol.spot u.1, u.2.1⟩

variable (r : Match A b c s v) (hd : r.depots g g') (hz : r.Stocks z z')
  (d M : ℕ)

theorem Match.supply_spot (u : SupplyUnit g z s) :
    u.spot = (r.supplyUnits hd hz u).spot :=
  Sigma.ext (r.spot_eq u.1) (cast_heq _ _).symm

private def indexSpot (a : SourceSpot A N) := (Fintype.equivFin (a.1.1.Req A) a.2).val

private theorem SupplyUnit.key_eq (u : SupplyUnit g z s) :
    supplyKey A b g z u.unit = Encodable.encode (indexSpot u.spot, u.copy.val) := by
  unfold supplyKey SupplyUnit.unit
  rw [u.depot]
  rfl

theorem Match.key_supply (u : SupplyUnit g z s) :
    supplyKey A b g z u.unit = supplyKey A c g' z' (r.supplyUnits hd hz u).unit := by
  rw [SupplyUnit.key_eq, SupplyUnit.key_eq, r.supply_spot hd hz u]
  rfl

abbrev Spot.edgePins (p : Spot N) (K : Type) [Field K] := Pin (localEdge K p.1) p.2

theorem SupplyUnit.tally_at (u : SupplyUnit g z s) (x : (Protocol.spot u.1).edgePins K) :
    b.tally A d M g u.req (placeEdge K u.1 x).1 = (b.code u.1.1).route A d M u.2.1 x.1 := by
  unfold Market.tally
  rw [u.depot]
  let i := u.1.1
  let f (v : (b.shape i).edges) : b.Edge := ⟨i, v⟩
  exact Stock.collect_inj (g := f) (fun _ _ e => eq_of_heq (Sigma.mk.inj e).2)
    ((b.code i).route A d M u.2.1) x.1

theorem SupplyUnit.tally_away (u : SupplyUnit g z s) (j : Near b s)
    (hne : u.1 ≠ j) (x : (Protocol.spot j).edgePins K) :
    b.tally A d M g u.req (placeEdge K j x).1 = 0 := by
  by_contra h
  have e := tally_origin A d M b g u.req _ h
  rw [u.depot] at e
  change u.1.1 = j.1 at e
  rcases u with ⟨⟨i, p⟩, u⟩
  rcases j with ⟨j, q⟩
  change i = j at e
  subst j
  exact hne (congrArg (Sigma.mk i) (Subtype.ext ((b.name i).injective (p.property.trans q.property.symm))))

theorem Match.tally_unit (u : SupplyUnit g z s) :
    Pin.Same r.core (b.tally A d M g u.req) (c.tally A d M g' (r.supplyUnits hd hz u).req) := by
  intro p
  have hex : ∃ (j : Near b s) (x : (spot j).edgePins K), placeEdge K j x = p := by
    obtain ⟨a, l, h⟩ := placeEdge_surj p p.1.1 p.1.2 rfl
    exact ⟨⟨p.1.1, a⟩, ⟨p.1.2, l⟩, h⟩
  obtain ⟨j, x, rfl⟩ := hex
  let y := cast (congrArg (fun i : Spot N => i.edgePins K) (r.spot_eq j)) x
  rw [r.core_eq j x y (cast_heq _ _).symm]
  by_cases h : u.1 = j
  · subst j
    let w := r.supplyUnits hd hz u
    have he : (⟨u.spot, x⟩ : Σ p : SourceSpot A N, p.1.edgePins K) = ⟨w.spot, y⟩ :=
      Sigma.ext (r.supply_spot hd hz u) (cast_heq _ _).symm
    exact (u.tally_at d M x).trans ((congrArg (fun p : Σ a : SourceSpot A N, a.1.edgePins K =>
      p.1.1.1.route A d M p.1.2 p.2.1) he).trans (w.tally_at d M y).symm)
  · exact (u.tally_away d M j h x).trans ((r.supplyUnits hd hz u).tally_away d M (r.near j)
      (r.near.injective.ne h) y).symm

theorem tally_absent (u : Units A b z) (h : ∀ i, b.name (b.depot A g u.1).1 i ≠ s)
    (p : Pin (edge K b) s) : b.tally A d M g u.1 p.1 = 0 := by
  by_contra hn
  have he := tally_origin A d M b g _ _ hn
  obtain ⟨i, _, _⟩ := placeEdge_surj p p.1.1 p.1.2 rfl
  rw [he] at h
  exact h i i.property

theorem Match.count_supply (p : Pin (edge K b) s) (P : ℕ → Prop) [DecidablePred P]
    (hd : r.depots g g') (hz : r.Stocks z z') :
    (∑ i : Units A b z, if P (supplyKey A b g z i) then b.tally A d M g i.1 p.1 else 0) =
      ∑ i : Units A c z', if P (supplyKey A c g' z' i) then c.tally A d M g' i.1 (r.core p).1 else 0 := by
  rw [SupplyUnit.sum_units (g := g) (s := s) _ (by
    intro i hi; rw [tally_absent d M i hi p, ite_self]),
    SupplyUnit.sum_units (g := g') (s := v) _ (by
    intro i hi; rw [tally_absent d M i hi (r.core p), ite_self]),
    ← (r.supplyUnits hd hz).sum_comp]
  refine sum_congr rfl fun i _ => ?_
  rw [r.key_supply hd hz]
  exact congrArg (fun n => if P _ then n else 0) (r.tally_unit hd hz d M i p)

theorem Match.total_supply (hd : r.depots g g') (hz : r.Stocks z z') :
    Pin.Same r.core (fun e => ∑ i, b.tally A d M g i e * z i)
      (fun e => ∑ i, c.tally A d M g' i e * z' i) := by
  intro p
  have h := r.count_supply d M p (fun _ => True) hd hz
  simp only [ite_true, Units, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at h
  exact (sum_congr rfl (fun _ _ => mul_comm _ _)).trans
    (h.trans (sum_congr rfl (fun _ _ => mul_comm _ _)))

theorem Match.offset_supply (u : SupplyUnit g z s) (p : Pin (edge K b) s) :
    offset (fun i => b.tally A d M g i.1 p.1) (supplyKey A b g z) u.unit =
      offset (fun i => c.tally A d M g' i.1 (r.core p).1) (supplyKey A c g' z')
        (r.supplyUnits hd hz u).unit := by
  simp only [offset, sum_filter, ← r.key_supply hd hz u]
  exact r.count_supply d M p (· < supplyKey A b g z u.unit) hd hz

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Individual terminal factors and their port numbers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Spectral Finset Classical Board

variable {K S I : Type} [Field K] [Fintype S] [Nonempty S] [DecidableEq S]
  [Fintype I] [DecidableEq I] {N t : ℕ}
  {A : Finset (Tensor K S)} {b : Market I N} {s : I}
  {g : b.Ports t} {z : b.Request A → ℕ} (d M : ℕ)

abbrev totalTally (g : b.Ports t) (z : b.Request A → ℕ) (e : b.Edge) :=
  ∑ i, b.tally A d M g i e * z i

private theorem tally_sum (g : b.Ports t) (z : b.Request A → ℕ) :
    (fun e => ∑ j : Units A b z, b.tally A d M g j.1 e) = totalTally d M g z := by
  funext e
  simp [Units, totalTally, Fintype.sum_sigma, mul_comm]

def supplyPort (g : b.Ports t) (w : Units A b z) (s : I) :
    (orders (edge K b) (b.tally A d M g w.1)).localPort s →
      (orders (edge K b) (totalTally d M g z)).localPort s :=
  (orders_eq (edge K b) (tally_sum d M g z)).local s ∘
    Pin.assign (edge K b) (fun e => (pack _ _ (supplyOrdered A d M b g z e)).symm) w s

def supplyNumber (g : b.Ports t) (w : Units A b z) (e : b.Edge)
    (j : Fin (b.tally A d M g w.1 e)) : Fin (totalTally d M g z e) :=
  Fin.cast (congrFun (tally_sum d M g z) e) ((pack _ _ (supplyOrdered A d M b g z e)) ⟨w, j⟩)

theorem supplyPort_copy (g : b.Ports t) (w : Units A b z) (i : Pin (edge K b) s)
    (j : Fin (b.tally A d M g w.1 i.1)) :
    supplyPort d M g w s (Pin.atCopy i j) = Pin.atCopy i (supplyNumber d M g w i.1 j) := by
  unfold supplyPort
  rw [Function.comp_apply, Pin.assign_atCopy]
  rfl

variable (hr : b.ready A d) (hc : UniformCap N A M)

theorem supply_absent (x : b.Request A) (h : ∀ i, b.name (b.depot A g x).1 i ≠ s) :
    (supplyAt A d M b g hr hc x).kernel () s = fun _ _ _ => 1 := by
  simp only [supplyAt, supplyFrom, Expansion.rename, Expansion.absent _ _ h ()]
  rfl

def supplyFactor (g : b.Ports t) (w : Units A b z) (s : I) :
    Frame K ((orders (request b A) z).localPort s)
      ((orders (edge K b) (totalTally d M g z)).localPort s) :=
  Frame.pull ((supplyAt A d M b g hr hc w.1).kernel () s)
    (fun j => Pin.atCopy ⟨w.1, j⟩ w.2) (supplyPort d M g w s)

theorem terminal_factors (g : b.Ports t) (z : b.Request A → ℕ) (s : I) :
    (terminal A d M b g z hr hc).kernel () s =
      Frame.product (fun u : SupplyUnit g z s => supplyFactor d M hr hc g u.unit s) := by
  funext h x y
  apply SupplyUnit.prod_units (g := g) (s := s) (fun w => supplyFactor d M hr hc g w s h x y)
  intro w hw
  rw [supplyFactor, supply_absent d M hr hc _ hw]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # A terminal factor reads only the pins and ordinals of its own local route -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Spectral Finset Classical Board

variable {K S I : Type} [Field K] [Fintype S] [Nonempty S] [DecidableEq S]
  [Fintype I] [DecidableEq I] {N t : ℕ}
  {A : Finset (Tensor K S)} {b : Market I N} {s : I}
  {g : b.Ports t} {z : b.Request A → ℕ} (d M : ℕ)

abbrev Spot.reqPins (p : Spot N) (A : Finset (Tensor K S)) := Pin (localRequest p.1 A) p.2

/-- Feed a pin and copy number to a local program without any global names. -/
def SourceSpot.run (p : SourceSpot A N) (h : ℕ)
    (X : Lines h (p.1.reqPins A)) (Y : Lines h (p.1.edgePins K × ℕ)) : K :=
  if he : p.1.1.2.Direct K (p.1.1.2.tensor A (.inl p.2)) (p.1.1.priceCap A d M p.2) then
    (localSupply A d M p.1.1 p.2 he).kernel () p.1.2 h (fun i => X ⟨p.2, i⟩)
      (fun o => Y (⟨o.1.1.1, ⟨o.1.2, o.2⟩⟩, o.1.1.2.val))
  else 0

variable (hr : b.ready A d) (hc : UniformCap N A M) (u : SupplyUnit g z s)

theorem SupplyUnit.local_value (h : ℕ) (X : Lines h (Pin (request b A) s))
    (Y : Lines h (Pin (edge K b) s × ℕ)) :
    (supplyAt A d M b g hr hc u.req).kernel () s h (fun i => X ⟨u.req, i⟩)
        (fun o => Y (⟨o.1.1.1, ⟨o.1.2, o.2⟩⟩, o.1.1.2.val)) =
      u.spot.run d M h (fun l => X (placeReq A u.1 l))
        (fun p => Y (placeEdge K u.1 p.1, p.2)) := by
  let F (w : b.Source A) (hw : b.request A w.1 w.2 = u.req) :=
    (supplyFrom A d M b hr hc u.req w hw).kernel () s h (fun i => X ⟨u.req, i⟩)
      (fun o => Y (⟨o.1.1.1, ⟨o.1.2, o.2⟩⟩, o.1.1.2.val))
  change F (b.depot A g u.req) (b.depot_spec A g u.req).1 = _
  have key : F (b.depot A g u.req) (b.depot_spec A g u.req).1 = F ⟨u.1.1, u.2.1⟩ rfl := by
    simp only [u.depot]
  rw [key]
  let v := localSupply A d M (b.code u.1.1) u.2.1 (b.local_route A d M hr hc _ _)
  have he : u.spot.1.1.2.Direct K (u.spot.1.1.2.tensor A (.inl u.spot.2))
      (u.spot.1.1.priceCap A d M u.spot.2) := b.local_route A d M hr hc _ _
  rw [SourceSpot.run, dite_eq_left he]
  unfold F supplyFrom Expansion.rename
  dsimp only
  rw [v.placed (b.name u.1.1) u.1.2 ()]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Matched charts give identical terminal kernels on corresponding pins -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Spectral Finset Classical Board

namespace Pin

variable {K S S' I I' : Type} [Field K] [Fintype I] [Fintype I']
  {T : I → Board K S} {T' : I' → Board K S'} {s : S} {s' : S'}
  {z : I → ℕ} {z' : I' → ℕ} {h : ℕ}

def read (x : Lines h ((orders T z).localPort s)) (p : Pin T s) (k : ℕ) : Fin (2 ^ h) → Bool :=
  if hk : k < z p.1 then x (atCopy p ⟨k, hk⟩) else fun _ => false

theorem read_copy (x : Lines h ((orders T z).localPort s)) (p : Pin T s) (k : Fin (z p.1)) :
    read x p k = x (atCopy p k) := dite_eq_left k.isLt

theorem read_lift (e : Pin T s ≃ Pin T' s') (hz : Same e z z')
    (x : Lines h ((orders T' z').localPort s')) (p : Pin T s) (k : ℕ) :
    read (x ∘ lift e hz) p k = read x (e p) k := by
  by_cases hk : k < z p.1
  · rw [read, read, dite_eq_left hk, dite_eq_left (lt_of_lt_of_eq hk (hz p))]
    rfl
  · have hk' : ¬ k < z' (e p).1 := by rw [← hz p]; exact hk
    rw [read, read, dite_eq_right hk, dite_eq_right hk']

end Pin

variable {K S I I' : Type} [Field K] [Fintype S] [Nonempty S] [DecidableEq S]
  [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] {N t t' : ℕ}
  {A : Finset (Tensor K S)} {b : Market I N} {c : Market I' N} {s : I} {v : I'}
  {g : b.Ports t} {g' : c.Ports t'} {z : b.Request A → ℕ} {z' : c.Request A → ℕ}
  (d M : ℕ)

private def baseOffset (u : SupplyUnit g z s) (p : Pin (edge K b) s) :=
  offset (fun i => b.tally A d M g i.1 p.1) (supplyKey A b g z) u.unit

private theorem packed_factor (hr : b.ready A d) (hc : UniformCap N A M)
    (u : SupplyUnit g z s) (h : ℕ) (x : Lines h ((orders (request b A) z).localPort s))
    (y : Lines h ((orders (edge K b) (totalTally d M g z)).localPort s)) :
    supplyFactor d M hr hc g u.unit s h x y =
      u.spot.run d M h (fun p => Pin.read x (placeReq A u.1 p) u.copy.val)
        (fun q => let p := placeEdge K u.1 q.1; Pin.read y p (baseOffset d M u p + q.2)) := by
  let X := fun p => Pin.read x p u.copy.val
  let Y := fun q : Pin (edge K b) s × ℕ => Pin.read y q.1 (baseOffset d M u q.1 + q.2)
  refine Eq.trans ?_ (u.local_value d M hr hc h X Y)
  apply congrArg₂ ((supplyAt A d M b g hr hc u.req).kernel () s h)
  · exact funext fun j => (Pin.read_copy x ⟨u.req, j⟩ u.copy).symm
  · funext o
    obtain ⟨p, l, rfl⟩ := Pin.exists_atCopy o
    change y (supplyPort d M g u.unit s (Pin.atCopy p l)) = _
    rw [supplyPort_copy]
    exact (Pin.read_copy y p (supplyNumber d M g u.unit p.1 l)).symm

private theorem SourceSpot.run_eq {p q : SourceSpot A N} (he : p = q) (h : ℕ)
    {x : Lines h (p.1.reqPins A)} {x' : Lines h (q.1.reqPins A)}
    {y : Lines h (p.1.edgePins K × ℕ)} {y' : Lines h (q.1.edgePins K × ℕ)}
    (hx : ∀ i j, HEq i j → x i = x' j) (hy : ∀ i j k, HEq i j → y (i, k) = y' (j, k)) :
    p.run d M h x y = q.run d M h x' y' := by
  subst q
  exact congrArg₂ (p.run d M h) (funext fun i => hx i i .rfl)
    (funext fun i => hy i.1 i.1 i.2 .rfl)

theorem Match.terminal_rel (r : Match A b c s v) (hd : r.depots g g') (hz : r.Stocks z z')
    (d M : ℕ) (hr : b.ready A d) (hr' : c.ready A d) (hc : UniformCap N A M) :
    ∃ hw : Pin.Same r.core (totalTally d M g z) (totalTally d M g' z'),
      ∀ he : Pin.Same r.req z z', Frame.Rel (Pin.lift r.req he) (Pin.lift r.core hw)
        ((terminal A d M b g z hr hc).kernel () s) ((terminal A d M c g' z' hr' hc).kernel () v) := by
  refine ⟨r.total_supply d M hd hz, fun he => ?_⟩
  rw [terminal_factors, terminal_factors]
  apply Frame.Rel.product (r.supplyUnits hd hz)
  intro u h x y
  rw [packed_factor, packed_factor]
  apply SourceSpot.run_eq d M (r.supply_spot hd hz u)
  · intro i j hij
    rw [Pin.read_lift, r.req_eq u.1 i j hij]
    rfl
  · intro i j k hij
    dsimp only
    rw [Pin.read_lift]
    unfold baseOffset
    rw [r.offset_supply hd hz d M u (placeEdge K u.1 i), r.core_eq u.1 i j hij]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Matching local schedules
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Match
open Routing Spectral
open scoped Classical

variable {K S I I' : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  {N M : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)} {b : Market I N} {c : Market I' N}
  {s : I} {t : I'} (f : Match A b c s t) (a : Atlas N A M ρ) (μ d m : ℕ)

def Replay : (k : ℕ) → (z : b.Request A → ℕ) → (y : c.Request A → ℕ) →
    b.Path a μ d m k z → c.Path a μ d m k y → Prop
  | 0, z, y, _, _ => f.Stocks z y
  | k + 1, z, y, u, v =>
    f.Stocks z y ∧
    (∀ j : Near b s, HEq (b.record a (b.stockPrice (M := M) μ d z) m u.1 j.1)
      (c.record a (c.stockPrice (M := M) μ d y) m v.1 (f.near j).1)) ∧
    Replay k (b.after a μ d m z u.1) (c.after a μ d m y v.1) u.2 v.2

end OAI.LinearAlgebra.MatrixExponent.Protocol.Match
end
