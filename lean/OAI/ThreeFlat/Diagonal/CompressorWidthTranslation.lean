import OAI.ThreeFlat.Diagonal.CompressorShrinkWidthWriter
import OAI.ThreeFlat.Diagonal.CompressorDemandROM
import OAI.ThreeFlat.Diagonal.ShrinkActualSlots

namespace OAI
/-! # Lifting the elected rooted supply to the requested physical output lane -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Fin.NatCast
variable {n w : ℕ}
variable (data : Param → Word w) (mem : Memory w) (vs : Fin n → Word w)
local notation "V" => Formula.value data mem vs

theorem choose4_word (k : F n) (f : Fin 4 → F n) (i : Fin 4) (hi : V k=(i.val:Word w)) (fit : 4≤2^w) :
    V (choose4 k f) = V (f i) := by
  have eq (i j : Fin 4) : (i.val:Word w)=(j.val:Word w) ↔ i=j := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt (i.isLt.trans_le fit),Fin.val_cast_of_lt (j.isLt.trans_le fit),Fin.ext_iff]
  fin_cases i <;> simp [choose4,Formula.value,RAM.DescriptorExpr.Comparison.test,hi,Fin.ext_iff,Nat.mod_eq_of_lt (show 1<2^w by omega),Nat.mod_eq_of_lt (show 2<2^w by omega),
    Nat.mod_eq_of_lt (show 3<2^w by omega)]

theorem roles_formula (g : ArcColumns (F n)) (d : ℕ) (layout : Bool) (e : Ends (F n)) :
    (roleSites (Demand.formulaOps n) g d layout e).map V =
      roleSites (words mem) (g.map V) d layout (e.map V) := by
  cases layout <;> simp [roleSites,RoleSites.map,Ends.map,Position.select,Placement.Site.select,
    owner,toggle,thickBit,forward,Position.map,Placement.Site.map,Columns.map,ArcColumns.map,
    Demand.formulaOps,words,Formula.value,RAM.DescriptorExpr.Comparison.test,row,slot]

variable {B H : Type*} [AddCommGroup H] {d c t l : ℕ}
variable {P : PackingData B H (BitWord t) (BitWord l) d c} {E : Codec B w c t l}
variable {data mem vs}
variable {g : ArcColumns (F n)} (R : ArcReads P E (g.map (Formula.value data mem vs)) mem)
variable (count : Fin 4 → ℕ) (radix live full : ℕ)

private theorem sourceRole (layout : Bool) (u : Fin 4) (m : P.Motif) :
    Graph.siteAt (RoleSites.mk (siteCode E (P.roleA m)) (siteCode E (P.roleB m))
      (siteCode E (P.roleD layout m)) (1:Word w)) (Graph.roles layout u).1 =
      siteCode E (siteOf P layout (supplyRoles layout u).1 m) := by
  cases layout <;> fin_cases u <;> rfl

include R
set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem translate_code (layout : Bool) (k : Fin 4) (r : Rooted P) (a : Cursor (F n))
    (lane : F n) (y : BitWord l) (fit : 4≤2^w)
    (ho : a.old.map (Formula.value data mem vs)=posCode P E (sourcePosition r.val.val))
    (hp : (Formula.value data mem vs) a.oldPort=(r.val.val.1.2.val:Word w)) (hk : (Formula.value data mem vs) a.survivor=(k.val:Word w))
    (hy : (Formula.value data mem vs) lane=tagWord E.lanes y) :
    (unroot g (Graph.Stage.mk d c count radix live full) layout a lane).map (Formula.value data mem vs) = posCode P E (sourcePosition
      (moveMotif P (y-(siteOf P layout (supplyRoles layout k).1 r.val).2.2) r.val).val) := by
  let e : Ends (Formula n) := ends (Demand.formulaOps n) g d false a.old a.oldPort
  let role : RoleSites (Formula n) := roleSites (Demand.formulaOps n) g d layout e
  let u : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l) := siteOf P layout (supplyRoles layout k).1 r.val
  have he : e.map (Formula.value data mem vs)=encodeEnds P E r.val.val := Demand.ends_code g R false a.old a.oldPort (sourcePosition r.val.val) r.val.val.1.2 ho hp
  have hr : role.map (Formula.value data mem vs) = ⟨siteCode E (P.roleA r.val),siteCode E (P.roleB r.val),
      siteCode E (P.roleD layout r.val),1⟩ := by
    rw [show role.map (Formula.value data mem vs) = _ from roles_formula _ _ _ g d layout e,he,roles_code R]
  have lan : (Formula.value data mem vs) (Graph.siteAt role (Graph.roles layout k).1).lane = tagWord E.lanes u.2.2 := by
    have hr' := congrArg (fun s => (Graph.siteAt s (Graph.roles layout k).1).lane) hr
    rw [sourceRole] at hr'
    have selected (i : Fin 3) :
        (Formula.value data mem vs) (Graph.siteAt role i).lane =
          (Graph.siteAt (role.map (Formula.value data mem vs)) i).lane := by
      fin_cases i <;> rfl
    exact (selected _).trans hr'
  have atLane := choose4_word data mem vs a.survivor (fun i => (Graph.siteAt role (Graph.roles layout i).1).lane) k hk fit
  have zero : r.val.val.1.1.2.2 = 0 := r.property
  have flip (a b : Word w) : BinaryOp.bitXor.eval a b = BinaryOp.bitXor.eval b a := by simp [BinaryOp.eval,Nat.xor_comm]
  have b := congrArg (fun q => q.site.base) ho
  have t' := congrArg (fun q => q.site.tag) ho
  have bits := congrArg Placement.Position.bits ho
  have sl := congrArg Placement.Position.slot ho
  simp only [Placement.Position.map,Placement.Site.map,posCode,sourcePosition,siteCode] at b t' bits sl
  change Placement.Position.mk (Placement.Site.mk
    (Formula.value data mem vs a.old.site.base) (Formula.value data mem vs a.old.site.tag)
    (BinaryOp.bitXor.eval (Formula.value data mem vs
      (choose4 a.survivor fun i => (Graph.siteAt role (Graph.roles layout i).1).lane))
      (Formula.value data mem vs lane))) (Formula.value data mem vs a.old.bits)
    (Formula.value data mem vs a.old.slot) = _
  simp only [atLane,lan,hy,b,t',bits,sl,moveMotif,moveArc,moveSlot,moveSite,posCode,siteCode,sourcePosition,
    zero,zero_add,tagWord_sub]
  exact congrArg (fun z => Placement.Position.mk (Placement.Site.mk _ _ z) _ _) (flip _ _)


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth

end OAI
