import OAI.Computability.BorderVNP.PackedInheritedProfileLocal

/-! # Intrinsic profile observations on every finite bank

At birth the complete native site returns its empty observation list exactly
when the guessed work equals the canonical padded word and the actual sewn
factor is one. The physical wires are read from the tail of the intrinsic bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Crossing.Profile.Cell Inherited BankSite BankJoint BankCircuit BankPacket CellSparse CellAddresses
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm) (a : S)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable {ns ne np : ℕ} (siteID : (G e p bin perm positive first q).Site ↪ Fin ns)
variable (edgeID : (G e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
local notation3 "G₀" => G e p bin perm positive first q
local notation3 "j₀" => blocks p.layout bin perm m a
local notation3 "v₀" => seedSite e p bin perm positive first q a
local notation3 "work₀" => workAt e p bin perm positive first q
local notation3 "orig₀" => originSite e p bin perm positive first q a siteID edgeID portID
local notation3 "pack₀" => output e p bin perm positive first q

/-- The unique intrinsic origin staging vector determined by the physical assignment. -/
noncomputable def originWork (y : (G₀).Assignment) : Fin ((orig₀).work) → Bool :=
  fun k => paddedBank (originLayout (Fin D × Bool) j₀ e.count)
    (fun u i l => finTwoEquiv (selectors e p bin perm positive first q a y u i l)) k.val

variable (ext : Ports bits) (bank : ℕ → Bool)

/-- The physical three-block origin semantics gives the native finite-bank observation. -/
theorem origin_observe :
    let v := v₀ (.inl ())
    let y := (cellView G₀ work₀ bank).wires edgeID portID v
    (orig₀).observe bank = if (fun k : Fin ((orig₀).work) => bank k.val) =
      originWork e p bin perm positive first q a siteID edgeID portID y ∧
      (G₀).read (pack₀).table y ext v = 1 then some [] else none := by
  intro v y
  let W := cellView G₀ work₀ bank
  have hl := origin_local e p bin perm positive first q a siteID edgeID portID bank (W.read v)
    (fun _ h => (view_read G₀ v work₀ bank h).symm)
  have h := physical_origin_iff e p bin perm positive first q a id work₀ siteID edgeID portID (fun _ => 0) W [] ext rfl
  dsimp only at h
  have hv : (∀ r ∈ (orig₀).rows,r.Valid [] (W.read v)) ↔
      (fun k : Fin ((orig₀).work) => bank k.val) = originWork e p bin perm positive first q a siteID edgeID portID y ∧
        (G₀).read (pack₀).table y ext v = 1 := by
    simp only [originSite,Site.rows,List.reverse_cons,List.reverse_nil,List.nil_append,List.flatten_cons,List.flatten_nil,
      List.append_nil]
    apply h.trans
    apply and_congr_left'
    have hk := view_stage G₀ v work₀ siteID (profile_empty e p bin perm positive first q a (.inl ())) bank
    constructor
    · intro hwork
      funext k
      exact (hk k).symm.trans (hwork k)
    · intro hwork k
      exact (hk k).trans (congrFun hwork k)
  rw [hl,observe_empty_boxes _ rfl]
  by_cases hc : ∀ r ∈ (orig₀).rows,r.Valid [] (W.read v)
  · rw [ite_eq_left hc,ite_eq_left (hv.mp hc)]
  · rw [ite_eq_right hc,ite_eq_right (mt hv.mpr hc)]

variable (binName : S → ℕ)
local notation3 "term₀" => terminalSite e p bin perm positive first q a siteID edgeID portID binName

/-- The true gathered hook word and the physical bank cables determine the terminal work vector. -/
noncomputable def terminalWork (t : Fin D × Bool) (y : (G₀).Assignment) : Fin ((term₀ t).work) → Bool :=
  fun k => paddedBank (terminalLayout j₀ m (q a).val)
    (terminalData (q a).val (selectors e p bin perm positive first q a y t)
      (feederBlocks e p bin perm positive first q a y t)
      ((bundle p.layout bin perm m positive a).gather (cuts e p bin perm positive first q a y) t)) k.val

/-- The intrinsic terminal checks exactly its unique work vector and sewn physical factor. -/
theorem terminal_observe (t : Fin D × Bool) :
    let v := v₀ (.inr (.inl t))
    let y := (cellView G₀ work₀ bank).wires edgeID portID v
    (term₀ t).observe bank = if (fun k : Fin ((term₀ t).work) => bank k.val) =
      terminalWork e p bin perm positive first q a siteID edgeID portID binName t y ∧
      (G₀).read (pack₀).table y ext v = 1 then some [] else none := by
  intro v y
  let W := cellView G₀ work₀ bank
  have hl := terminal_local e p bin perm positive first q a siteID edgeID portID binName t bank (W.read v)
    (fun _ h => (view_read G₀ v work₀ bank h).symm)
  have h := physical_terminal_iff e p bin perm positive first q a id work₀ siteID edgeID portID (fun _ => 0) W []
    ext binName (fun _ => 0) t rfl
  dsimp only at h
  have hv : (∀ r ∈ (term₀ t).rows,r.Valid [] (W.read v)) ↔
      (fun k : Fin ((term₀ t).work) => bank k.val) = terminalWork e p bin perm positive first q a siteID edgeID portID binName t y ∧
        (G₀).read (pack₀).table y ext v = 1 := by
    simp only [terminalSite,Site.rows,List.reverse_cons,List.reverse_nil,List.nil_append,List.flatten_cons,List.flatten_nil,
      List.append_nil,List.forall_mem_append]
    rw [hookRows_valid_iff e p bin perm positive first q a siteID edgeID portID binName (fun _ => 0)]
    apply h.trans
    apply and_congr_left'
    have hk := view_stage G₀ v work₀ siteID (profile_empty e p bin perm positive first q a (.inr t)) bank
    constructor
    · intro hwork
      funext k
      exact (hk k).symm.trans (hwork k)
    · intro hwork k
      exact (hk k).trans (congrFun hwork k)
  rw [hl,observe_empty_boxes _ rfl]
  by_cases hc : ∀ r ∈ (term₀ t).rows,r.Valid [] (W.read v)
  · rw [ite_eq_left hc,ite_eq_left (hv.mp hc)]
  · rw [ite_eq_right hc,ite_eq_right (mt hv.mpr hc)]

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
