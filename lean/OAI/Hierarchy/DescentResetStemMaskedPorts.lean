import OAI.Hierarchy.DescentResetStemTemplatePorts

namespace OAI
/-! # Read compact physical stem metadata only on occupied actor rows -/
namespace Hierarchy.DescentResetStemMaskedPorts
open DescentResetStemTemplatePorts (Banks Room pack)
open DescentResetStemIncidence (Scene)
open DescentPackedColony (target)
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical
noncomputable section

variable {K H oldH palette w count stop : ℕ}

def guard (number : Bank) (yes : Expr) (otherwise : ℕ) : Expr :=
  .branch .lt .row (.lookup number (.lit 0)) yes (.lit otherwise)

def hereAt (B : Banks) (number : Bank) := guard number (.lookup B.here .row) 0

def ports (B : Banks) (number : Bank) (oldH : ℕ) (template : Fin K→Option (Fin palette × Fin palette)) :
    DescentResetStemIncidence.Ports K where
  here := hereAt B number
  near i := .lookup (B.neighbors i) (hereAt B number)
  src j := guard number (DescentResetStemTemplatePorts.endpoint B.parent oldH palette Prod.fst (template j)) (oldH*palette)
  dst j := guard number (DescentResetStemTemplatePorts.endpoint B.parent oldH palette Prod.snd (template j)) (oldH*palette)
  oldHub _ := guard number (.lookup B.hub (.lookup B.parent .row)) 0

def chooseRow {n : ℕ} (f : Fin count→Fin n) (nonempty : 0 < H → 0 < n) (r : Fin H) : Fin n :=
  if h : r.val < count then f ⟨r.val,h⟩ else ⟨0,nonempty (Nat.zero_lt_of_lt r.isLt)⟩

def scene (here : Fin count→Fin (oldH*palette)) (parent : Fin count→Fin oldH)
    (physical : 0 < H → 0 < oldH*palette)
    (near : Fin (oldH*palette)→Fin 3→Option (Fin (oldH*palette))) (hub : Fin oldH→Bool)
    (template : Fin K→Option (Fin palette×Fin palette)) : Scene K H (oldH*palette) where
  here := chooseRow here physical
  near := near
  ends j r := if h : r.val < count then (template j).map fun z =>
    (pack (parent ⟨r.val,h⟩) z.1,pack (parent ⟨r.val,h⟩) z.2) else none
  oldHub _ r := if h : r.val < count then hub (parent ⟨r.val,h⟩) else false

section Row

variable (here : Fin count → Fin (oldH*palette)) (parent : Fin count → Fin oldH)
    (physical : 0 < H → 0 < oldH*palette)
    (near : Fin (oldH*palette) → Fin 3 → Option (Fin (oldH*palette))) (hub : Fin oldH→Bool)
    (template : Fin K → Option (Fin palette × Fin palette))

theorem ends_ghost (j : Fin K) (r : Fin H) (past : count ≤ r.val) :
    (scene here parent physical near hub template).ends j r = none := by
  simp only [scene,dite_eq_right (Nat.not_lt.mpr past)]

theorem ends_active (j : Fin K) (r : Fin H) (active : r.val < count) :
    (scene here parent physical near hub template).ends j r =
      (template j).map (fun z => (pack (parent ⟨r.val,active⟩) z.1,pack (parent ⟨r.val,active⟩) z.2)) := by
  simp only [scene,dite_eq_left active]

theorem here_active (r : Fin H) (active : r.val < count) :
    (scene here parent physical near hub template).here r = here ⟨r.val,active⟩ := by
  simp only [scene,chooseRow,dite_eq_left active]

theorem hub_active (j : Fin K) (r : Fin H) (active : r.val < count) :
    (scene here parent physical near hub template).oldHub j r = hub (parent ⟨r.val,active⟩) := by
  simp only [scene,dite_eq_left active]

end Row

structure Stored (B : Banks) (number : Bank) (here : Fin count→Fin (oldH*palette)) (parent : Fin count→Fin oldH)
    (near : Fin (oldH*palette)→Fin 3→Option (Fin (oldH*palette))) (hub : Fin oldH→Bool) (m : Memory w) : Prop where
  count_word : m number.base = (count : Word w)
  here_word : ∀ r, m (B.here.base+r.val) = ((here r).val : Word w)
  parent_word : ∀ r, m (B.parent.base+r.val) = ((parent r).val : Word w)
  neighbor_word : ∀ i v, m ((B.neighbors i).base+v.val) = (target (near v i) : Word w)
  hub_word : ∀ r, m (B.hub.base+(parent r).val) = ((hub (parent r)).toNat : Word w)

private theorem guard_eval (number : Bank) (yes : Expr) (no : ℕ) (m : Memory w) (r : ℕ)
    (fit : number.Fits w stop) (val : m number.base=(count : Word w))
    (hr : r < 2^w) (hc : count < 2^w) :
    (guard number yes no).eval m (r : Word w) =
      if r < count then yes.eval m (r : Word w) else (no : Word w) := by
  have stored : number.read m (0 : Word w)=(count : Word w) := by
    simpa only [Nat.cast_zero,Nat.add_zero] using
      (DescentPackedZip.bank_read number m (i:=0) fit.1 fit).trans (by simpa only [Nat.add_zero] using val)
  simp [guard,Expr.eval,stored,Comparison.test,Fin.lt_def,Fin.val_cast_of_lt hr,Fin.val_cast_of_lt hc]

/-- Occupied-row correctness never constrains either compact index on padded rows. -/
theorem read (B : Banks) (number : Bank) (here : Fin count→Fin (oldH*palette)) (parent : Fin count→Fin oldH)
    (physical : 0 < H → 0 < oldH*palette)
    (near : Fin (oldH*palette)→Fin 3→Option (Fin (oldH*palette))) (hub : Fin oldH→Bool)
    (template : Fin K→Option (Fin palette×Fin palette)) (m : Memory w)
    (room : Room B count oldH palette w stop) (numberFit : number.Fits w stop) (rowWord : H ≤ 2^w)
    (data : Stored B number here parent near hub m) :
    DescentResetStemIncidence.Reads (ports B number oldH template) (scene here parent physical near hub template) m := by
  have activeWord : count < 2^w := room.here_size.trans_lt room.here.2.1
  have gate (r : Fin H) (yes : Expr) (no : ℕ) := guard_eval number yes no m r.val numberFit data.count_word
    (r.isLt.trans_le rowWord) activeWord
  have index (r : Fin H) :
      (hereAt B number).eval m (r.val : Word w) = ((chooseRow here physical r).val : Word w) := by
    rw [hereAt,gate]
    by_cases active : r.val < count
    · simp only [ite_eq_left active,chooseRow,dite_eq_left active,Expr.eval]
      exact (DescentPackedZip.bank_read B.here m (active.trans_le room.here_size) room.here).trans
        (data.here_word ⟨r.val,active⟩)
    · simp only [ite_eq_right active,chooseRow,dite_eq_right active,Nat.cast_zero]
  have prev (r : Fin H) (active : r.val < count) :
      B.parent.read m (r.val : Word w)=((parent ⟨r.val,active⟩).val : Word w) :=
    (DescentPackedZip.bank_read B.parent m (active.trans_le room.parent_size) room.parent).trans
      (data.parent_word ⟨r.val,active⟩)
  constructor
  · exact index
  · intro r i
    change (B.neighbors i).read m ((hereAt B number).eval m (r.val : Word w))=_
    rw [index]
    exact (DescentPackedZip.bank_read _ m ((chooseRow here physical r).isLt.trans_le (room.near_size i))
      (room.near i)).trans (data.neighbor_word i (chooseRow here physical r))
  · intro j r
    change (guard number _ _).eval m (r.val : Word w)=_
    rw [gate]
    by_cases h : r.val < count
    · simp only [ite_eq_left h,scene,dite_eq_left h,Option.map_map,Function.comp_def]
      exact DescentResetStemTemplatePorts.endpoint_read B.parent (parent ⟨r.val,h⟩) _ m (prev r h) Prod.fst _
    · simp only [ite_eq_right h,scene,dite_eq_right h,Option.map_none,target,Option.elim_none]
  · intro j r
    change (guard number _ _).eval m (r.val : Word w)=_
    rw [gate]
    by_cases h : r.val < count
    · simp only [ite_eq_left h,scene,dite_eq_left h,Option.map_map,Function.comp_def]
      exact DescentResetStemTemplatePorts.endpoint_read B.parent (parent ⟨r.val,h⟩) _ m (prev r h) Prod.snd _
    · simp only [ite_eq_right h,scene,dite_eq_right h,Option.map_none,target,Option.elim_none]
  · intro j r
    change (guard number _ _).eval m (r.val : Word w)=_
    rw [gate]
    by_cases h : r.val < count
    · simp only [ite_eq_left h,scene,dite_eq_left h,Expr.eval,prev r h]
      exact (DescentPackedZip.bank_read _ m ((parent ⟨r.val,h⟩).isLt.trans_le room.hub_size) room.hub).trans
        (data.hub_word ⟨r.val,h⟩)
    · simp only [ite_eq_right h,scene,dite_eq_right h,Bool.toNat_false,Nat.cast_zero]

private theorem guard_fits (number : Bank) (yes : Expr) (no : ℕ) (fit : number.Fits w stop)
    (right : yes.Fits w stop) : (guard number yes no).Fits w stop :=
  ⟨trivial,⟨fit,trivial⟩,right,trivial⟩

theorem fits (B : Banks) (number : Bank) (oldH : ℕ) (template : Fin K→Option (Fin palette×Fin palette))
    (room : Room B count oldH palette w stop) (fit : number.Fits w stop) :
    (ports B number oldH template).All (Expr.Fits w stop) := by
  have ha := guard_fits number (.lookup B.here .row) 0 fit ⟨room.here,trivial⟩
  exact ⟨ha,fun i=>⟨room.near i,ha⟩,
    fun _=>guard_fits number _ _ fit (DescentResetStemTemplatePorts.endpoint_fits _ _ _ _ _ room.parent),
    fun _=>guard_fits number _ _ fit (DescentResetStemTemplatePorts.endpoint_fits _ _ _ _ _ room.parent),
    fun _=>guard_fits number _ _ fit ⟨room.hub,room.parent,trivial⟩⟩

theorem work (B : Banks) (number : Bank) (oldH : ℕ) (template : Fin K→Option (Fin palette×Fin palette)) :
    (ports B number oldH template).All (fun e => e.work ≤ 22+8*palette) := by
  have cost := DescentResetStemTemplatePorts.work B oldH template
  have bill (e : Expr) (k : ℕ) (small : e.work ≤ 12+8*palette) :
      (guard number e k).work ≤ 22+8*palette := by
    change 2+6+e.work+1+1 ≤ 22+8*palette
    omega
  refine ⟨bill _ _ cost.here,fun i=>?_,fun j=>bill _ _ (cost.src j),fun j=>bill _ _ (cost.dst j),
    fun j=>bill _ _ (cost.hub j)⟩
  change 22 ≤ 22+8*palette
  omega

end
end Hierarchy.DescentResetStemMaskedPorts

end OAI
