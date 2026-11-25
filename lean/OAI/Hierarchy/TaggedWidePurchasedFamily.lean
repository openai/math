import OAI.Hierarchy.TaggedWidePurchasedPins
import OAI.Hierarchy.TaggedWideProcedurePrice

namespace OAI
/-! # Cohort of actual native machines with the common purchased dyadic directory -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedPrune TaggedShorterBudget TaggedShorterPacking TaggedShorterSupergroups Tagged.WideControlJoin
open ThreeFlat Routing Spill TaggedShorterCompaction TaggedShorterNetwork Real Filter
open scoped Classical Topology BigOperators
variable {F : Type*} [Field F] {κ A : ℝ} {u : ℝ→ℝ} {δ ξ : ℝ} {k M : ℕ}

/-- Original-header and paid programs plus the true tape-to-cut input map.
These are the inputs to a two-compactor cut; their polynomial resource
charges are read from the same programs that supply the terminal receipt. -/
structure LocalPrograms (x : WideParent κ A) {menu : WideMenu κ A}
    (D S : Fin menu.types→ℕ) where
  frame : WideControlJoin.Frame F k x.h x.w M
  read : ∀i,Input (S i) (D i) (menu.height i x+menu.payload i x)→
    SitePins (OpenPins x.h x.w frame.routing.catalyst) (Fin frame.routing.selectors) frame.data frame.paid

variable {n W attempts ell : ℕ} (hW : 0<W)

namespace LocalPrograms
variable {C : ℝ} (menu : WideMenu κ A) (x : WideParent κ A) (D S count : Fin menu.types→ℕ)
variable (c : LocalPrograms (F:=F) (k:=k) (M:=M) x (menu:=menu) D S)
    (items : PurchaseList (F:=F) (C:=C) menu x D S count)
def compile : Parts F k x.h x.w M menu.types :=
  attachPurchases menu x D S count c.frame items c.read
end LocalPrograms

local notation "geom" => fun short=>typeMenu κ A W n k attempts ell hW (fun _=>short+ell)
local notation "menu" => fun short=>(geom short).menu u δ ξ
local notation "D" => fun (x:WideParent κ A) (_:Fin (n+1))=>purchaseSlots x.h W k attempts ell
local notation "count" => fun (short : ℕ) (x : WideParent κ A) i=>purchaseModules W u δ ξ (menu short) x i
local notation "S" => fun (short : ℕ) (x : WideParent κ A) i=>purchaseCandidates x.h W k attempts (D x i) ((menu short).height i x) (count short x i)
local notation "set" => fun (short : ℕ) (C:ℝ) (x : WideParent κ A)=>PurchaseList (F:=F) (C:=C) (menu short) x (D x) (S short x) (count short x)
local notation "hardware" => fun (short : ℕ) (x : WideParent κ A)=>LocalPrograms (F:=F) (k:=k) (M:=M) x («menu»:=menu short) (D x) (S short x)
local notation "mounted" => fun (short : ℕ) (C:ℝ) (x : WideParent κ A) (core:hardware short x) (items:set short C x)=>
  core.compile (C:=C) (menu short) x (D x) (S short x) (count short x) items

/-- Coherent literal programs and tapes for a single chosen pair of cutoff and
cost parameters. Only the five remaining physical resource classes are inputs. -/
def HardwareAt (short : ℕ) (C : ℝ) : Prop :=
  ∃ N:ℕ,∃ eligible:WideParent κ A→Prop,
      (∀ᶠ x in WideParent.large κ A,eligible x) ∧
      ∃ build:∀x,eligible x→hardware short x,
      ∃ progs:∀x,eligible x→Mounted x.h N × Mounted x.h N,
      (∀x (v:eligible x),(build x v).frame.first=(progs x v).1.gate ∧
        (build x v).frame.paid=(progs x v).2.gate) ∧
      (∀x (v:eligible x) (items:set short C x),Nonempty ((mounted short C x (build x v) items).Run)) ∧
      (∀j:WidePhysicalBill.Part (n+1),(∀i,j≠.cut i)→(∀i,j≠.socket i)→j≠.flag→∃K d:ℝ,0≤K ∧ 0≤d ∧
        ∀ᶠ x in WideParent.large κ A,∀(v:eligible x) (items:set short C x),
        WidePhysicalBill.Part.fee (mounted short C x (build x v) items).charges j≤
          K*(WidePhysicalBill.Part.scale x.h x.w j*(log (x.h:ℝ))^d))

/-- The cutoff and price constant are chosen by the circuit theorem before
the local RAM-to-site assembly. It is enough to give the actual two native
machines, physical input wires, their executions and the uncancelled charges. -/
theorem purchased_readout {s ε p q Q σ Λ η : ℝ} (profile : TaggedWidthProfile.Admissible s u)
    (price : Choice u A ε p q Q σ Λ δ η ξ) (hk : 0≤κ) (hM : 0<M)
    (assemble : ∀short C,0≤C→(∀ᶠ x in WideParent.large κ A,GroupRoom W k attempts u δ ξ (menu short) x)→
      HardwareAt (F:=F) (k:=k) (M:=M) (κ:=κ) (A:=A) (u:=u)
      (δ:=δ) (ξ:=ξ) (n:=n) (attempts:=attempts) (ell:=ell) hW short C) :
    Nonempty (ProtocolReadout F k u κ A δ ξ) := by
  obtain ⟨short,C,hC,purchases⟩:=choose_purchases (F:=F) profile price W n k attempts ell hW hk
  obtain ⟨N,eligible,large,build,progs,eqs,runs,fee⟩:=assemble short C hC (purchases.mono (fun _ v=>v.1))
  let valid (x:WideParent κ A):=eligible x ∧ Nonempty (set short C x)
  have eventual : ∀ᶠ x in WideParent.large κ A,valid x:=large.and (purchases.mono (fun _ v=>v.2))
  let buys (x) (v:valid x):set short C x:=Classical.choice v.2
  let a (x) (v:valid x):=mounted short C x (build x v.1) (buys x v)
  have rowFit (b:Bool) : ∀ᶠ x in WideParent.large κ A,∀v:valid x,
      (a x v).charges.rows b≤2^(2*x.h) := by
    obtain ⟨K,d,hK,hd,priceRow⟩:=fee (.rows b) (by intro i; exact fun h=>by cases h)
      (by intro i; exact fun h=>by cases h) (by intro h; cases h)
    filter_upwards [priceRow,Mounted.eventually_rows (κ:=κ) (A:=A) K d hK hd] with x priceX limit v
    exact limit _ (priceX v.1 (buys x v))
  have sizes x (v:valid x):=Mounted.sizes (progs x v.1).1 (progs x v.1).2 (a x v)
    (eqs x v.1).1 (eqs x v.1).2
  apply protocolReadout_of_native (geom short) hM valid eventual a
    (fun x v=>Classical.choice (runs x v.1 (buys x v))) (fun x v=>(sizes x v).1)
    (fun x v=>(sizes x v).2.1) (fun x v=>(sizes x v).2.2)
  · intro x v i
    exact (buys x v i).bank ((build x v.1).read i)
  · filter_upwards [rowFit false,rowFit true] with x left right v
    let p:=progs x v.1
    have e₀ : (a x v).first=p.1.gate := (eqs x v.1).1
    have e₁ : (a x v).paid=p.2.gate := (eqs x v.1).2
    have l:=(left v)
    have r:=(right v)
    change (a x v).first.S+((a x v).first.f+(a x v).first.u)≤_ at l
    change (a x v).paid.S+((a x v).paid.f+(a x v).paid.u)≤_ at r
    rw [e₀] at l
    rw [e₁] at r
    exact p.1.charges_cpu p.2 (a x v) e₀ e₁ l r
  · intro j
    by_cases cut : ∃i,j=WidePhysicalBill.Part.cut i
    · obtain ⟨i,rfl⟩:=cut
      refine ⟨C,0,hC,le_rfl,Filter.Eventually.of_forall fun x v=>?_⟩
      exact attached_work (menu short) x (D x) (S short x) (count short x)
        (build x v.1).frame (buys x v) (build x v.1).read i
    · by_cases socket : ∃i,j=WidePhysicalBill.Part.socket i
      · obtain ⟨i,rfl⟩:=socket
        obtain ⟨K,hK,pins⟩:=purchased_sockets (F:=F) (C:=C) (k:=k) (M:=M) profile price
          W n attempts ell short hW hk
        refine ⟨K,0,hK,le_rfl,?_⟩
        filter_upwards [pins] with x charged v
        exact charged (D x) (S short x) (count short x) (build x v.1).frame (buys x v) (build x v.1).read i
      · by_cases flag:j=.flag
        · subst j
          refine ⟨8,0,by norm_num,le_rfl,Filter.Eventually.of_forall fun x v=>?_⟩
          exact (progs x v.1).1.flag_bill (a x v) (eqs x v.1).1 x rfl rfl
        · obtain ⟨K,d,hK,hd,h⟩:=fee j (fun i hi=>cut ⟨i,hi⟩) (fun i hi=>socket ⟨i,hi⟩) flag
          refine ⟨K,d,hK,hd,?_⟩
          filter_upwards [h] with x ok
          exact fun v=>ok v.1 (buys x v)

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
