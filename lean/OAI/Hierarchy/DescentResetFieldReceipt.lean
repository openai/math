import OAI.Hierarchy.DescentResetCandidateMeta
import OAI.Hierarchy.DescentResetSignedAll

namespace OAI
/-! # The signed lookup table consumes the original mixed fields and the three issued offsets -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "C₀" => blocks B
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
open DescentResetWindowResidentSources DescentResetFieldAssembler
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentPackedColony DescentSIMDLookup DescentPackedZip
local notation "K" => totalLocal B
local notation "FN" => fieldNames B
local notation "position_" => sumAt B FN (localRoster B)
local notation "face_" u => Roster.Face A ord C₀ u
local notation "slot_" u => Roster.addr A ord C₀ u (localRoster B u)
def rankAt (h₀ : Host) (p : Fin 3) (j : Fin K) : ℕ :=
  (localOrigin B h₀ j).elim 0 (fun x=>
    if p=2 then position_ false ((C₀).src x.val) ⟨x.val,x.property.1,.inl rfl⟩
    else position_ (decide (p=1)) h₀ x)

/-- The selected sector/slot is the caller's fixed loop coordinate. Only
the physical raw source/destination test determines whether that sign lives. -/
theorem field_read {b : ℕ} (u : Host) (a : Fin (2*K)) (f : Fin 8) :
    let part : Fin 2×Fin K:=finProdFinEquiv.symm a
    let side:=decide (part.1.val=1)
    let chip:=«meta» B u (localOrigin B u part.2)
    let picked : Cell b:=rankAt B u (atField f) part.2
    (field side f chip picked.val:Cell b)=(DescentNextSignedWindow.Native.fields (candidateRows B FN u a) f:Cell b) := by
  obtain ⟨⟨s,j⟩,rfl⟩:=finProdFinEquiv.surjective a
  simp only [Equiv.symm_apply_apply]
  let side:=decide (s.val=1)
  have sign : (if side then (1:Fin 2) else 0)=s :=by fin_cases s <;> rfl
  by_cases yes : ∃x : face_ u,(slot_ u) x=finProdFinEquiv (s,j)
  · obtain ⟨x,hx⟩:=yes
    let v:=Roster.resident A ord C₀ u x
    have coords:=finProdFinEquiv.injective hx
    have numbers : localRoster B u v=j:=congrArg Prod.snd coords
    have identity : localOrigin B u j=some v:=(local_read B u j v).2 numbers
    have sideEq : side=x.val.2:=by
      have eqn : (if x.val.2 then (1:Fin 2) else 0)=s:=congrArg Prod.fst coords
      change decide (s.val=1)=x.val.2
      exact (congrArg (fun n : Fin 2 => decide (n.val=1)) eqn).symm.trans (by cases x.val.2 <;> rfl)
    have enabled := (meta_face B u v x.val.2).2 x.property.2
    have receipt:=three_fields B FN (localRoster B) u x
    have ⟨atEnd,shared,atSource,extent⟩:=receipt
    have shownRow : candidateRows B FN u (finProdFinEquiv (s,j))=some (DescentResetWindowFields.record A ord S B.next.valid C₀ (fun e => e ∈ (B.reset.orderedReentry B.terminals (DescentOrderedReset.grains W B.count B.order)).core) u x (DescentResetWindowFields.neighbor A ord S B.next.valid FN C₀ u x)):=by
      rw [←hx]
      exact Roster.mounted ..
    change (field side f («meta» B u (localOrigin B u j)) ((rankAt B u (atField f) j:Cell b).val):Cell b)=_
    rw [identity,sideEq,shownRow,field,ite_eq_left enabled]
    have cv (n : ℕ) : (((n : Cell b).val : ℕ) : Cell b) = (n : Cell b) := Fin.cast_val_eq_self _
    have rp (p : Fin 3) : rankAt B u p j = (if p=2 then position_ false ((C₀).src v.val) ⟨v.val,v.property.1,.inl rfl⟩ else position_ (decide (p=1)) u v) := by
      simp only [rankAt,identity,Option.elim_some]
    fin_cases f
    · rfl
    · rfl
    · exact congrArg (fun n : ℕ => (n : Cell b)) ((meta_peer B u v).trans (source_neighbor B FN u x).symm)
    · exact congrArg (fun z : Bool => (z.toNat : Cell b)) (decide_eq_decide.mpr Iff.rfl)
    · change (((rankAt B u 0 j : Cell b).val : ℕ) : Cell b)=_
      rw [cv, rp]
      exact congrArg (fun n : ℕ => (n : Cell b)) atEnd
    · change (((rankAt B u 1 j : Cell b).val : ℕ) : Cell b)=_
      rw [cv, rp]
      exact congrArg (fun n : ℕ => (n : Cell b)) shared
    · change (((rankAt B u 2 j : Cell b).val : ℕ) : Cell b)=_
      rw [cv, rp]
      exact congrArg (fun n : ℕ => (n : Cell b)) atSource
    · rfl
  · have blank:=candidate_hole B FN u (finProdFinEquiv (s,j)) (fun f h=>yes ⟨f,h⟩)
    rw [blank]
    cases got:localOrigin B u j with
    | none=>simp [«meta»,field,face,Meta.blank]
    | some x=>
      have missing : face side («meta» B u (some x))=false:=by
        apply Bool.eq_false_iff.mpr
        intro active
        let ff : face_ u:=⟨(x.val,side),x.property.1,(meta_face B u x side).1 active⟩
        refine yes ⟨ff,?_⟩
        apply congrArg finProdFinEquiv
        exact Prod.ext sign ((local_read B u j x).1 got)
      change (field side f («meta» B u (some x)) _:Cell b)=_
      simp only [field,missing,Bool.false_eq_true,ite_false,Nat.cast_zero]

variable {H M b bitsW : ℕ} (rack : Fin H→Option B.next.V)
local notation "X" => 2^k
local notation "gg" => S.groupCount (i+1)
def actualMeta (x : Fin X) (j : Fin K) (v : Fin H) (g : Fin gg) :=
  (rack v).elim Meta.blank (fun r=>«meta» B ((g,r),x) (localOrigin B ((g,r),x) j))
def actualOffset (x : Fin X) (p : Fin 3) (j : Fin K) (v : Fin H) (g : Fin gg) : Cell b :=
  (rack v).elim 0 (fun r=>(rankAt B ((g,r),x) p j:Cell b))

/-- A real reported binding usable at every block and signed slot, including
vacant hosts of the fixed calendar and the wrong sign of an occupied parent. -/
theorem render_source (root : ℕ) (header : Fin X→Fin K→Expr) (rank : Fin X→Fin 3→Fin K→Expr) (m : Memory bitsW)
    (early : ∀x j,(header x j).Fits bitsW root) (prior : ∀x p j,(rank x p j).Fits bitsW root)
    (metaRead : ∀x j,Source (header x j) (fun v g=>DescentResetFieldAssembler.raw b (actualMeta B rack x j v g)) M m)
    (rankRead : ∀x p j,Source (rank x p j) (actualOffset (b:=b) B rack x p j) M m)
    (small : ∀x j v g t,DescentResetFieldAssembler.digits (actualMeta B rack x j v g) t<2^b) (space : DescentResetFieldAssembler.endAddress root b M<2^bitsW) :
    let o:=DescentResetFieldAssembler.memory root b M m
    let top:=DescentResetFieldAssembler.endAddress root b M
    (DescentResetFieldAssembler.program root b M bitsW).Exec m o (4+10*(32*2^(DescentResetFieldAssembler.width b M))) ∧
    (∀x a f,(DescentResetFieldAssembler.fields root b M header rank x a f).Fits bitsW top) ∧
    (∀x a f,Source (DescentResetFieldAssembler.fields root b M header rank x a f) (fun v g=>
      (DescentNextSignedWindow.Native.fields ((rack v).bind (fun r=>candidateRows B FN ((g,r),x) a)) f:Cell b)) M o) ∧
    (∀u,u<root ∨ top≤u → o u=m u) ∧ CheapCode (DescentResetFieldAssembler.program root b M bitsW) := by
  obtain ⟨exec,fits,mounted,stable,_,cheap⟩:=DescentResetFieldAssembler.run root header rank m
    (actualMeta B rack) (actualOffset (b:=b) B rack) early prior metaRead rankRead small space
  refine ⟨exec,fits,?_,stable,@cheap⟩
  intro x a f
  have law:=mounted x a f
  dsimp only at law
  convert law using 2
  rename_i v
  funext g₀
  cases present:rack v with
  | none=>simp [actualMeta,present,Meta.blank,field,face,DescentNextSignedWindow.Native.fields]
  | some r=>
    simp only [actualMeta,actualOffset,present,Option.bind_some,Option.elim_some]
    exact (field_read (b:=b) B ((g₀,r),x) a f).symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
