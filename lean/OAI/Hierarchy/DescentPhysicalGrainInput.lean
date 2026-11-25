import OAI.Hierarchy.DescentPaidResetLayout
import OAI.Hierarchy.DescentOrderedResetRows
import OAI.Hierarchy.DescentActualWholeRows
import OAI.Hierarchy.DescentHubCoverage
import OAI.Hierarchy.DescentUnitReset
import OAI.Hierarchy.DescentGrainMeasurements
import OAI.Hierarchy.DescentInstalledEpoch
import OAI.Hierarchy.DescentInstalledHops
import OAI.Hierarchy.DescentFineGoodLeaf
import OAI.Hierarchy.DescentSharedRows
import OAI.Hierarchy.DescentTrunkReadout
import OAI.Hierarchy.DescentCanonicalFallback
import OAI.Hierarchy.DescentTerminalBudget
import OAI.Hierarchy.DescentResetSourceFrame

namespace OAI
/-! # Construct the reset receipt in arbitrary integral physical cable quanta -/

namespace Hierarchy.DescentSixParty
open DescentGL DescentColonies DescentBaseVariance DescentChosenRouter DescentChosenRouter.Dyadic
open DescentResetInvoice DescentBaseProfile DescentRotor DescentFineTerminals
open Hierarchy.DescentSixParty.StarKeys
open scoped Classical BigOperators
noncomputable section
variable {F H P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (count : W.graph.Edge→ℕ) (grain : ℕ) (fits : ∀e,W.graph.width e=count e*grain)
local notation "raw" => W.countWorld count
local notation "grainW" => W.granular count grain fits
variable (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)
variable (hub : V→Bool) (atoms : W.graph.Site→List H) (wire hist : ℕ)
local notation "hb" => (hub ∘ pos)
local notation "mass" => blockMass W.graph pos ix (MarkedWorld.siteUnits W hb atoms wire 256 hist)
local notation "traffic" => (fun v w i=>(pairLoad raw pos ix (wire*grain) v w i:ℝ))
variable {Δ r f g K B n h C bitsR : ℕ} (G : NonlinearExpanders.Graph n h)
local notation "Y" => (2^n:ℕ)
local notation "D" => (32*Nat.clog 2 (2*Δ))
local notation "hops" => nonhubHops Δ Y
local notation "ht" => 2*max (terminalDepth Δ Y f g false) (terminalDepth Δ Y f g true)

set_option maxHeartbeats 12000000 in
/-- A receipt for the actual subdivided old branch. Native loads are integral;
one normalized unit costs q and one original physical bit costs q*wire.
The two sources of additive loss are the measured stored atoms and the small
base allocation. The same epsilon pays each inequality in the receipt. -/
theorem physical_grain_budgets_for_ordered_rosters (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (vertex : V↪ℕ)
    (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
    (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (quota : Δ*2^decayExponent Δ≤K)
    (ports : 4*K≤Y) (hK : 0<K) (_fr : f≤r) (rk : r≤k) (fg : f≤g) (gk : g≤k)
    (positive : 0<wire) (grainPos : 0<grain) (allowed : wire*grain≤B) (positiveRotor : 0<bitsR)
    (power : Y^2*bitsR≤2^f) (menu : ∀p : Equiv.Perm (Fin Y),Configures F G.arcs C bitsR p)
    (room : ∀v i,mass v i≤B) (saturated : ∀v,hub v=true→∀i,mass v i=B)
    (edge : ∀e,pos (W.graph.dst e)∈near (pos (W.graph.src e)))
    (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
    (inside : ∀e∈W.core,hb (W.graph.src e)=false ∧ hb (W.graph.dst e)=false)
    (outside : ∀e∉W.core,hb (W.graph.src e)≠hb (W.graph.dst e))
    (q ε : ℝ) (hq : 0<q)
    (_initial : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε)
    (history : (hist:ℝ)*(∑v,((atoms v).length:ℝ))≤ε)
    (_small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ))
    (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k)
    (paid : PaidResetLayout near Δ r f B K hops ε
      (blockMass (raw).graph pos ix ((raw).siteUnits hb atoms (wire*grain) 256 hist)) traffic b hk L) :
    ∃(Z : ResetInput grainW (q*wire) (q*ε) h C ht) (T : ResetInput.Terminals Z),
      Z.ActorBudget T atoms wire hist f g B ∧ Z.k=k ∧ T.commonDepth=k-max r g ∧ Z.n=n ∧ Fintype.card Z.V=Fintype.card V ∧
      Z.unit=grain ∧ Z.width=bitsR ∧ HEq Z.graph G ∧ ∃ frame : Z.SourceFrame T pos ix hub g,frame.basis=L ∧ (∀v,Z.placement.b (frame.host v)=b v) ∧ ResetInput.SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K traffic Δ (blockMass (raw).graph pos ix ((raw).siteUnits hb atoms (wire*grain) 256 hist)) ∧ Z.placement.OrderedTickets (DescentOrderedReset.grains W count order) := by
  have branch' : 0<Δ := by omega
  have money := Nat.mul_pos positive grainPos
  have hB : 0<B := lt_of_lt_of_le money allowed
  have unitB : wire≤B := (Nat.le_mul_of_pos_right _ grainPos).trans allowed
  let measured := blockMass (raw).graph pos ix ((raw).siteUnits hb atoms (wire*grain) 256 hist)
  have measured_eq (v i) : measured v i=mass v i := W.mass_of_counts count grain fits pos ix hb atoms wire 256 hist v i
  have rawRoom (v i) : measured v i≤B := (measured_eq v i).le.trans (room v i)
  have hopsPos : 0<hops := by unfold nonhubHops;omega
  obtain ⟨fit,smooth,span,budget,hubs,marked⟩ := paid
  let a : Dyadic V (BitsOf raw) k :=
    ⟨b,hk,L,resetKeys near Δ f B K measured traffic b hk L,fun v=>hub v=true,physicalOld raw pos ix,_,DescentOrderedReset.grains W count order,vertex⟩
  have actual (s i) : a.old s i=physicalOld raw pos ix s i := rfl
  have core (p : a.Paid) : p.val.1∈W.core := by
    apply paid_core raw pos ix a actual _ p
    intro e notCore
    exact (by decide : ∀ x y : Bool, x ≠ y → x = true ∨ y = true)
      (hb (W.graph.src e)) (hb (W.graph.dst e)) (outside e notCore)
  let loads := physical_loads raw pos ix hb atoms (wire*grain) 256 hist a actual near sym hB (by decide)
    rawRoom rfl core (fun e _=>edge e) (fun e _=>same e) smooth degree quota ports
    (fun v j => by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using budget v j)
  have pu : (0:ℝ)<wire := by exact_mod_cast positive
  have ub : (wire:ℝ)≤B := by exact_mod_cast unitB
  have fitGrain : (grain:ℝ)≤B/wire := (le_div_iff₀ pu).mpr (by exact_mod_cast (Nat.mul_comm grain wire).le.trans allowed)
  have grainR : (0:ℝ)<grain := by exact_mod_cast grainPos
  have avail : (Y:ℝ)^2*bitsR≤(2:ℝ)^f := by exact_mod_cast power
  have enough : Y≤2^f := by
    have hy : 1≤Y := Nat.one_le_pow _ _ (by decide)
    have sq : Y≤Y^2 := by nlinarith
    exact sq.trans ((Nat.le_mul_of_pos_right _ positiveRotor).trans power)
  let remixed := rearrangedLoad measured L
  have lim : ∀v i,remixed v i≤B := fun v i=>rawRoom v _
  have posS := unit_pos pu ub (show 0<(2:ℝ)^f by positivity)
  have rows := unit_rows (n:=n) positiveRotor pu ub avail
  let goodRow := a.row (loads.per_grain positive) posS grainR fitGrain rows
  let row := sharedRow («D»:=D) near remixed lim b hk L a.keys a.hub enough goodRow
  let fall := terminal («D»:=D) (f:=f) (g:=g) near remixed lim b hub L row
  have terminalFields (s : Bool) (o : V×Block k) :
      DescentPlainTerminal.fields (fall s o).val.2=DescentPlainTerminal.endpoint near b L measured
        f D B g Y rawRoom (fun v j=>(v,j)∈a.keys) hub o.1 o.2 := by
    by_cases tagged : hub o.1=true
    · simp [fall,terminal,name,DescentPlainTerminal.fields,DescentPlainTerminal.endpoint,tagged]
    have untagged : hub o.1=false := by cases eq : hub o.1 <;> simp_all
    have good : DescentFineTerminals.paid b hk L a.keys a.hub o ↔
        (o.1,group (b o.1) (rearrange L o.2))∉a.keys := by
      rw [DescentFineTerminals.paid,and_iff_left (show ¬a.hub o.1 from tagged)]
      have keyEq : label b (baseOf b hk L o) =
          (o.1,group (b o.1) (rearrange L o.2)) :=
        Prod.ext rfl (layout_id (hk o.1) L o.2)
      have member : baseOf b hk L o ∈ validBases b a.keys ↔
          label b (baseOf b hk L o) ∈ a.keys := by
        unfold validBases
        exact ⟨fun h => (Finset.mem_filter.mp h).2,
          fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
      rw [keyEq] at member
      exact not_congr member
    by_cases active : DescentFineTerminals.paid b hk L a.keys a.hub o
    · have atRow := a.row_numeral (loads.per_grain positive) posS grainR fitGrain rows pu ((2:ℕ)^f*B)
          (by push_cast;ring) measured (fun _ _=>rfl) s o active
      simp only [fall,terminal,name,untagged,Bool.false_eq_true,ite_false,
        DescentPlainTerminal.fields,Option.map_some,DescentPlainTerminal.endpoint,ite_eq_right (good.mp active),
        row,sharedRow,ite_eq_left active,DescentPlainTerminal.baseSum,leafKey,goodRow,atRow,
        DescentChosenRouter.Dyadic.baseSum]; rfl
    · have bad : (o.1,group (b o.1) (rearrange L o.2))∈a.keys := by
        by_contra absent
        exact active (good.mpr absent)
      have atRow:=DescentFineTerminals.leaf_numeral («D»:=D) near remixed lim b enough o.1 (rearrange L o.2)
      simp only [fall,terminal,name,untagged,Bool.false_eq_true,ite_false,
        DescentPlainTerminal.fields,Option.map_some,DescentPlainTerminal.endpoint,ite_eq_left bad,
        row,sharedRow,ite_eq_right active,DescentFineTerminals.oldRow,atRow,DescentFineTerminals.leafSum,
        DescentPlainTerminal.leafSum,leafKey,remixed]
  have fallHost (s : Bool) (o : V×Block k) : (fall s o).val.1=o.1 := by
    cases tagged : hub o.1 <;> simp [fall,terminal,name,tagged]
  have directoryFields (v : V) (z : (ℕ×ℕ)×Option ℕ) :
      (∃ t : ↥(Directory («D»:=D) (f:=f) (g:=g) near remixed lim b hub L row),
        t.val.1=v ∧ DescentPlainTerminal.fields t.val.2=z) ↔
        ∃x,DescentPlainTerminal.endpoint near b L measured f D B g Y rawRoom
          (fun v j=>(v,j)∈a.keys) hub v x=z := by
    constructor
    · rintro ⟨t,same,read⟩
      obtain ⟨⟨s,o⟩,_,eqn⟩:=Finset.mem_image.mp t.property
      have actual : fall s o=t := Subtype.ext eqn
      have host : o.1=v := (fallHost s o).symm.trans ((congrArg (fun t=>t.val.1) actual).trans same)
      refine ⟨o.2,?_⟩
      rw [←host,←terminalFields s o,actual,read]
    · rintro ⟨x,read⟩
      exact ⟨fall false (v,x),fallHost ..,(terminalFields false (v,x)).trans read⟩
  let pay := (2:ℝ)^f*(B/wire)
  let R₀ := a.install (loads.per_grain positive) posS grainR fitGrain rows fall
  let scale := (2:ℕ)^f*B
  let mean (v w : V) := blockMean k (traffic v w)
  let cap (v w : V) := pairCapacity k (b v) (b w) (mean v w) scale K/wire
  have physicalSize (v w : V) :
      DescentBaseProfile.rowCount Y pay (cap v w) =
        DescentBaseProfile.rowCount Y ((2:ℝ)^f*(B/wire))
          (pairCapacity k (b v) (b w) (blockMean k (traffic v w)) ((2:ℕ)^f*B) K/wire) := by
    simp only [cap,mean,scale,pay,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have meanSym (v w : V) : mean v w=mean w v := by
    apply congrArg (blockMean k)
    funext i
    exact congrArg (fun n : ℕ => (n : ℝ)) (pairLoad_symm raw pos ix (wire*grain) (fun e _=>same e) v w i)
  have capEq (t : a.Pairs) (s : Bool) :
      (loads.per_grain positive).cap t=cap (a.endAt s t).val.1 (a.endAt (!s) t).val.1 := by
    let v := (a.endAt false t).val.1
    let w := (a.endAt true t).val.1
    have forward : (loads.per_grain positive).cap t=cap v w := by
      change pairCapacity k (b v) (b w) (mean v w) ((2:ℝ)^f * (B:ℝ)) K/wire =
        pairCapacity k (b v) (b w) (mean v w) (scale:ℝ) K/wire
      simp only [scale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    cases s
    · exact forward
    · change (loads.per_grain positive).cap t=cap w v
      calc
        _ = cap v w := forward
        _ = cap w v := by simp only [cap,pairCapacity,max_comm (b v) (b w),meanSym v w]
  have capPos (v w : V) : 0≤cap v w := by dsimp [cap,mean,blockMean,pairCapacity];positivity
  have capBill (v : V) (id : ℕ) : (∑w∈near v,∑_j∈touching (b v) (b w) id,cap v w)≤2*pay := by
    simp only [cap,←Finset.sum_div]
    have h := div_le_div_of_nonneg_right (budget v id) pu.le
    simpa only [scale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_div_assoc,pay,mean] using h
  have baseEdge (i : a.Paid) : (a.old true i.val).1∈near (a.old false i.val).1 := edge i.val.1
  have baseSame (i : a.Paid) : (a.old true i.val).2=(a.old false i.val).2 := (same i.val.1).symm
  let m := k-max r g
  have low (v : V) : m≤b v := (Nat.sub_le_sub_left (le_max_left r g) k).trans (fit v).1
  obtain ⟨σ,coherent,columnRead⟩ := a.install_columns (loads.per_grain positive) posS grainR fitGrain rows fall
    near sym baseEdge baseSame low cap capEq capPos capBill smooth degree quota ports
  let bare := relabel R₀ σ
  have sameMatrix {A : Type} (a₁ a₂ : Fintype A) (src dst : A → Fin Y) (i j : Fin Y) :
      @matrixOfBundles A a₁ Y src dst i j = @matrixOfBundles A a₂ Y src dst i j := by
    cases Subsingleton.elim a₁ a₂
    rfl
  have matrixRead (s : Bool) (t : a.G) (i j : Fin Y)
      (cells : Fintype (Cells R₀ s t)) (entries : Fintype (a.AtBase s t)) :
      @matrixOfBundles _ cells _ (source R₀ s t) (target R₀ s t) i j =
        @matrixOfBundles _ entries _ ((a.assignment (loads.per_grain positive) posS grainR fitGrain rows s t).choose ∘
          a.whole s t) (a.lastRow (loads.per_grain positive) posS grainR s t) i j :=
    (sameMatrix cells _ _ _ i j).trans
      ((a.observed_matrix (loads.per_grain positive) posS grainPos fitGrain rows fall s t i j).trans
        (sameMatrix _ entries _ _ i j))
  obtain ⟨rotors⟩ := relabel_hardware R₀ G positiveRotor grainPos menu fitGrain avail σ
    (fun s t i=>by
      simp only [Nat.cast_mul,mul_assoc]
      refine Eq.trans_le ?_ ((a.assignment (loads.per_grain positive) posS grainR fitGrain rows s t).choose_spec.2.1 i)
      exact Finset.sum_congr rfl fun j _ => congrArg (fun q : ℕ => (q : ℝ)) (matrixRead s t i j _ _))
    (fun s t j=>by
      simp only [Nat.cast_mul,mul_assoc]
      refine Eq.trans_le ?_ ((a.assignment (loads.per_grain positive) posS grainR fitGrain rows s t).choose_spec.2.2 j)
      exact Finset.sum_congr rfl fun i _ => congrArg (fun q : ℕ => (q : ℝ)) (matrixRead s t i j _ _))
  have old (s : Bool) (i : BitsOf raw) : bare.old s i=physicalOld raw pos ix s i := rfl
  have incident (s : Bool) (i : BitsOf raw) : (bare.old (!s) i).1∈near (bare.old s i).1 := by
    cases s
    · exact edge i.1
    · exact (sym _ _).mp (edge i.1)
  have common (s : Bool) (i : BitsOf raw) : (bare.old (!s) i).2=(bare.old s i).2 := by
    cases s
    · exact (same i.1).symm
    · exact same i.1
  have clean (s : Bool) (i : BitsOf raw) : ¬(hub (bare.old s i).1=true ∧ hub (bare.old (!s) i).1=true) := by
    have ends : ¬(hb (W.graph.src i.1)=true ∧ hb (W.graph.dst i.1)=true) := by
      intro both
      by_cases he : i.1∈W.core
      · exact Bool.noConfusion ((inside i.1 he).1.symm.trans both.1)
      · exact outside i.1 he (both.1.trans both.2.symm)
    cases s
    · exact ends
    · exact fun both => ends ⟨both.2,both.1⟩
  have grainCore (i : BitsOf raw) : i∈(grainW).core ↔ i.1∈W.core := by
    exact (raw).fine_mark i
  have ordinary (i : BitsOf raw) (hi : i∈(grainW).core) (s : Bool) : hub (bare.old s i).1=false := by
    obtain ⟨x,y⟩ := inside i.1 ((grainCore i).mp hi)
    cases s
    · exact x
    · exact y
  let range := max r g
  have rangeFit : range≤k := max_le rk gk
  have upper (v : V) : b v≤k-f := (fit v).2
  have smooth' := smooth_for_terminals near b branch' sym smooth
  have full' (v : V) (hv : hub v=true) : b v=k-f :=
    hubs v (fun i=>(measured_eq v i).trans (saturated v hv i))
  let code := Function.Embedding.subtype (fun z=>z∈Directory («D»:=D) (f:=f) (g:=g) near remixed lim b hub L row)
  let roster := DescentRelativeContacts.rosterIndex bare near remixed lim hub row code
    (fun _ _=>rfl) rangeFit low upper smooth' full' fg (le_max_right r g) incident common clean
  let R := {bare with fallbackBook:=fun s t=>
    DescentRelativeContacts.bookAt (Δ:=Δ) (k:=k) (r:=range) (f:=f) (g:=g) near hub code vertex t (roster s t)}
  have hardware : Hardware (K:=F) (C₀:=C) (u:=grain) R G positiveRotor pay := rotors
  have routes := installed_hops_book R near remixed lim hub row code G positiveRotor pay hardware
    (fun _ _=>rfl) (fun s t=>DescentRelativeContacts.book_depth (Δ:=Δ) (f:=f) (g:=g) near hub code
      vertex branch' degree t (roster s t)) (grainW).core ordinary
  refine ⟨{
    V:=V,Fallback:=_,Contact:=_,k:=k,n:=n,width:=bitsR,unit:=grain,allWidths:=W.granular_width count grain fits,
    hub:=hb,inside:=fun i h=>inside i.1 ((grainCore i).mp h),
    outside:=fun i h=>outside i.1 (fun m=>h ((grainCore i).mpr m)),
    placement:=R,graph:=G,positive:=positiveRotor,pay:=pay,scale:=q*((2:ℝ)^f*B),
    hn:=posS.le,rate:=?_,circuit:=hardware,«hops»:=hops,weight:=fun v i=>q*measured v i,
    ordinary:=fun i hi s h=>by
      change hub (bare.old s i).1 = true at h
      exact Bool.noConfusion ((ordinary i hi s).symm.trans h),
    incidences:=?_,fallback:=routes.1,exterior:=routes.2,
    loadBill:=?_,span:=?_,marked:=?_},?_⟩
  · rw [mul_assoc]
    exact congrArg (q*·) (restored_price pu)
  · intro p
    have integers := bit_incidences raw pos ix hb atoms (wire*grain) hist q hq.le p
    have sameCharge (p₁ p₂ : Prop) (d₁ : Decidable p₁) (d₂ : Decidable p₂) (hh : p₁ ↔ p₂) :
        @ite ℝ p₁ d₁ (q*(wire:ℝ)*grain) 0 =
        @ite ℝ p₂ d₂ (q*((wire*grain:ℕ):ℝ)*1) 0 := by
      cases d₁ with
      | isTrue yes =>
        cases d₂ with
        | isTrue _ =>
          change q*(wire:ℝ)*grain = q*((wire*grain:ℕ):ℝ)*1
          rw [Nat.cast_mul,mul_one,mul_assoc]
        | isFalse no => exact (no (hh.mp yes)).elim
      | isFalse no =>
        cases d₂ with
        | isFalse _ => rfl
        | isTrue yes => exact (no (hh.mpr yes)).elim
    refine Eq.trans_le ?_ integers
    apply congrArg₂ (· + ·)
    · apply congrArg (fun f => load (R.old false) f p)
      funext i
      exact sameCharge _ _ _ _ ((grainCore i).trans ((raw).fine_mark i).symm)
    · apply congrArg (fun f => load (R.old true) f p)
      funext i
      exact sameCharge _ _ _ _ ((grainCore i).trans ((raw).fine_mark i).symm)
  · have amount := all_bits_bill raw pos ix hb atoms (wire*grain) hist q ε hq.le inside outside history
    change (∑v,∑i,q*(measured v i:ℝ)) ≤
      2*(q*((wire*grain:ℕ):ℝ)*(raw).fine.liveWidth) +
        257*(q*((wire*grain:ℕ):ℝ)*(raw).fine.tetherWidth) + q*ε at amount
    have a : ((raw).fine.liveWidth:ℝ)*grain=(grainW).liveWidth := by exact_mod_cast W.count_core_amount count grain fits
    have b : ((raw).fine.tetherWidth:ℝ)*grain=(grainW).tetherWidth := by exact_mod_cast W.count_tether_amount count grain fits
    rw [←a,←b]
    simpa only [Nat.cast_mul,mul_assoc,mul_left_comm,mul_comm] using amount
  · simp_rw [←Finset.mul_sum]
    have scaled := mul_le_mul_of_nonneg_left span hq.le
    push_cast at scaled
    change q*((2:ℝ)^f*B*∑v,(2:ℝ)^(b v)) ≤
      q*(4*(ε+∑v,∑i,(measured v i:ℝ))) at scaled
    change q*((2:ℝ)^f*B)*(∑v,(2:ℝ)^(b v)) ≤
      4*(q*ε+q*∑v,∑i,(measured v i:ℝ))
    nlinarith only [scaled]
  · exact scaled_marked raw pos ix hb atoms (wire*grain) hist b hk L _ q ε hq.le hops marked

  · have commonRow (o : V×Block k) : goodRow true o=goodRow false o :=
      a.row_side (loads.per_grain positive) posS grainR fitGrain rows (fun _=>rfl) o
    have sameFall := actual_side (Δ:=Δ) (K:=K) (f:=f) (g:=g) near measured rawRoom traffic b hk L hub enough goodRow commonRow
    have commonBooks (s : Bool) (t : ↥(Directory («D»:=D) (f:=f) (g:=g) near remixed lim b hub L row)) :
        (R.fallbackBook s t).height≤ht := by
      have bill := DescentRelativeContacts.book_depth (Δ:=Δ) (f:=f) (g:=g) near hub code vertex
        branch' degree t (roster s t)
      change (DescentRelativeContacts.bookAt (Δ:=Δ) (k:=k) (r:=range) (f:=f) (g:=g) near hub code vertex t (roster s t)).height≤ht
      apply bill.trans
      cases (code t).2.2.isSome <;> omega
    have coarseLinks : R.CommonGroups m code :=
      common_groups_of_records R m code low (fun i=>(common false i).symm) (fun a0=>a.group_origins a0)
        (fun s i=>DescentRelativeContacts.coarse_name near remixed lim b hub L row
          low upper (le_max_right r g) s (R.old s i))
    have hubName (u : W.graph.Site) (tagged : hub (pos u)=true) :
        code (fall false (pos u,ix u)) = (pos u,((k-g,group (k-g) (rearrange L (ix u))),none)) := by
      change name («D»:=D) (f:=f) (g:=g) near remixed lim b hub L row false (pos u,ix u) = _
      simp only [name,tagged,ite_true]
    refine ⟨{
      home:=fun v=>fall false (pos v,ix v),hub:=fun z=>hub z.val.1,commonDepth:=m,joined:=coherent,columns:=⟨vertex,near,fun v w=>DescentBaseProfile.rowCount Y pay (cap v w),columnRead,fun s t=>congrArg (DescentBaseProfile.rowCount Y pay) (capEq t s)⟩,tag:=?_,
      attach:=?_,code:=code,commonLow:=low,
      hubShape:=hub_shape near remixed lim b hub L row,
      hubCover:=hub_cover near remixed lim b hub L row (le_max_right r g) rangeFit,
      codeLegal:=DescentResetHostSize.fallback_valid near remixed lim b hub L row low upper (le_max_right r g),
      bookHeight:=commonBooks,coarseLinks:=coarseLinks,fallbackCoherent:=DescentRelativeContacts.common_book_install (Δ:=Δ) (g:=g) (f:=f)
        bare near hub code vertex roster (fun _ _ _=>rfl),leaves:=DescentRelativeContacts.issued_leaf_roster (Δ:=Δ) (g:=g) (f:=f) bare near hub code vertex roster (fun _ _ _=>rfl),source:=?_},?_,rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,⟨{
        host:=Equiv.refl _,basis:=L,used:=HEq.rfl,extent:=rfl,actor:=fun s i=>by cases s <;> rfl,oldBlock:=fun s i=>by cases s <;> rfl,homeHigh:=fun u=>DescentRelativeContacts.coarse_name near remixed lim b hub L row low upper (le_max_right r g) false (pos u,ix u),homeHost:=fun u=>fallHost false (pos u,ix u),rotorHub:=fun _=>Iff.rfl,originalHub:=fun _=>rfl,fits:=gk,
        enough:=Nat.sub_le_sub_left (le_max_right r g) k,atHub:=hubName},rfl,(fun _=>rfl),⟨fun _=>rfl,fun _ _=>Iff.rfl,physicalSize,fun _ _=>Iff.rfl,(fun z=>by change _=window (k:=k-m) (f:=f) (g:=g) («D»:=D) near hub z;rw [show k-m=range by dsimp [m];omega];rfl),rawRoom,(fun u=>terminalFields false (pos u,ix u)),directoryFields⟩,⟨fun p=>a.ticket_endpoint_read (loads.per_grain positive) posS grainR p,
        a.ticket_pair_surjective (loads.per_grain positive) posS grainR⟩⟩⟩
    · intro v
      exact congrArg hub (fallHost false (pos v, ix v))
    · intro s i
      cases s
      · rfl
      · exact (sameFall (pos (W.graph.dst i.1),ix (W.graph.dst i.1))).symm
    · intro s i hi
      exact actual_good_name (Δ:=Δ) (K:=K) (g:=g) near measured rawRoom traffic b hk L hub enough goodRow
        s (a.old s i) (hi s)

    · let cost := (grainW).siteUnits hb atoms wire 256 hist
      let loc (v : W.graph.Site) := (pos v,ix v)
      have total v x : DescentResetTrunks.bin loc cost (v,x)=measured v x := by
        have units : cost = W.siteUnits hb atoms wire 256 hist := funext fun u =>
          W.granular_units count grain fits hb atoms wire 256 hist u
        exact (block_bin W.graph pos ix cost v x).trans
          ((congrArg (fun c : W.graph.Site → ℕ => blockMass W.graph pos ix c v x) units).trans
            (measured_eq v x).symm)
      have rowsPaid s (p : BaseId b) (outside : p∉validBases b a.keys) (nonhub : ¬a.hub p.1) j :
          inputLoad Finset.univ (fun z : OldBase b hk L p=>(measured z.val.1 z.val.2:ℝ))
            (fun z=>goodRow s z.val) j≤3*((2^f*B:ℕ):ℝ)/Y := by
        have h := a.whole_input_bound (loads.per_grain positive) posS grainR fitGrain rows s ⟨p,outside,nonhub⟩ j
        change inputLoad Finset.univ (fun z : OldBase b hk L p=>(measured z.val.1 z.val.2:ℝ)/wire)
          (fun z=>goodRow s z.val) j≤3*pay/Y at h
        rw [input_div] at h
        have eqPay : 3*pay/(Y:ℝ)*(wire:ℝ)=3*((2^f*B:ℕ):ℝ)/Y := by
          unfold pay
          push_cast
          field_simp
        exact ((div_le_iff₀ pu).mp h).trans_eq eqPay
      have exactPrice : (wire:ℝ)*pay=((2^f*B:ℕ):ℝ) := by
        unfold pay
        push_cast
        field_simp [ne_of_gt pu]
      constructor
      · exact exactPrice.le
      · rintro ⟨⟨v,p,j⟩,included⟩ nonhub
        obtain ⟨⟨s,⟨w,x⟩⟩,_,found⟩ := Finset.mem_image.mp included
        have vw : w=v := (fallHost s (w,x)).symm.trans (congrArg Prod.fst found)
        subst w
        change hub v=false at nonhub
        cases j with
        | none => simp [name,nonhub] at found
        | some j =>
          rw [terminal_bin cost code (fun v=>fall false (loc v))]
          change ((DescentResetTrunks.bin (name («D»:=D) (f:=f) (g:=g) near remixed lim b hub L row false ∘ loc)
            cost (v,p,some j)):ℝ)≤_
          rw [terminal_read near remixed lim b hub L row loc cost false v p j nonhub]
          simp_rw [total]
          exact shared_bound («D»:=D) near remixed lim b hk L a.keys a.hub enough goodRow
            (fun _ o=>(measured o.1 o.2:ℝ)) (fun _ _=>by positivity) (fun _ _ _=>le_rfl) rowsPaid false v p j
      · rintro ⟨⟨v,p,j⟩,included⟩ tagged
        obtain ⟨⟨s,⟨w,x⟩⟩,_,found⟩ := Finset.mem_image.mp included
        have vw : w=v := (fallHost s (w,x)).symm.trans (congrArg Prod.fst found)
        subst w
        change hub v=true at tagged
        simp only [name,tagged,ite_true,Prod.mk.injEq,true_and] at found
        rcases found with ⟨rfl,rfl⟩
        rw [terminal_bin cost code (fun t=>fall false (loc t))]
        exact hub_read near remixed lim b hub L row loc cost false v tagged (rearrange L x) gk
          (fun i=>(total v i).trans ((measured_eq v i).trans (saturated v tagged i)))
      · intro s base
        have inp := a.good_items grain (loads.per_grain positive) posS grainPos fitGrain rows fall s base
        have eqPay : (wire:ℝ)*(2*pay)=2*((2^f*B:ℕ):ℝ) := by unfold pay;push_cast;field_simp
        exact (mul_le_mul_of_nonneg_left inp pu.le).trans_eq eqPay
      · exact exactPrice

theorem physical_grain_budgets_for_ordered (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (vertex : V↪ℕ)
    (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
    (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (quota : Δ*2^decayExponent Δ≤K)
    (ports : 4*K≤Y) (hK : 0<K) (fr : f≤r) (rk : r≤k) (fg : f≤g) (gk : g≤k)
    (positive : 0<wire) (grainPos : 0<grain) (allowed : wire*grain≤B) (positiveRotor : 0<bitsR)
    (power : Y^2*bitsR≤2^f) (menu : ∀p : Equiv.Perm (Fin Y),Configures F G.arcs C bitsR p)
    (room : ∀v i,mass v i≤B) (saturated : ∀v,hub v=true→∀i,mass v i=B)
    (edge : ∀e,pos (W.graph.dst e)∈near (pos (W.graph.src e)))
    (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
    (inside : ∀e∈W.core,hb (W.graph.src e)=false ∧ hb (W.graph.dst e)=false)
    (outside : ∀e∉W.core,hb (W.graph.src e)≠hb (W.graph.dst e))
    (q ε : ℝ) (hq : 0<q)
    (initial : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε)
    (history : (hist:ℝ)*(∑v,((atoms v).length:ℝ))≤ε)
    (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ))
    (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k)
    (paid : PaidResetLayout near Δ r f B K hops ε
      (blockMass (raw).graph pos ix ((raw).siteUnits hb atoms (wire*grain) 256 hist)) traffic b hk L) :
    ∃(Z : ResetInput grainW (q*wire) (q*ε) h C ht) (T : ResetInput.Terminals Z),
      Z.ActorBudget T atoms wire hist f g B ∧ Z.k=k ∧ T.commonDepth=k-max r g ∧ Z.n=n ∧ Fintype.card Z.V=Fintype.card V ∧
      Z.unit=grain ∧ ∃ frame : Z.SourceFrame T pos ix hub g,frame.basis=L ∧ Z.placement.OrderedTickets (DescentOrderedReset.grains W count order) := by
  obtain ⟨Z,T,cost,zk,dep,zn,sz,unit,_,_,frame,exactBasis,_,_,tickets⟩:=physical_grain_budgets_for_ordered_rosters
    W count grain fits pos ix hub atoms wire hist G order vertex near sym branch degree quota ports hK fr rk fg gk
    positive grainPos allowed positiveRotor power menu room saturated edge same inside outside q ε hq initial history small b hk L paid
  exact ⟨Z,T,cost,zk,dep,zn,sz,unit,frame,exactBasis,tickets⟩

theorem physical_grain_budgets_for_chosen (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
    (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (quota : Δ*2^decayExponent Δ≤K)
    (ports : 4*K≤Y) (hK : 0<K) (fr : f≤r) (rk : r≤k) (fg : f≤g) (gk : g≤k)
    (positive : 0<wire) (grainPos : 0<grain) (allowed : wire*grain≤B) (positiveRotor : 0<bitsR)
    (power : Y^2*bitsR≤2^f) (menu : ∀p : Equiv.Perm (Fin Y),Configures F G.arcs C bitsR p)
    (room : ∀v i,mass v i≤B) (saturated : ∀v,hub v=true→∀i,mass v i=B)
    (edge : ∀e,pos (W.graph.dst e)∈near (pos (W.graph.src e)))
    (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
    (inside : ∀e∈W.core,hb (W.graph.src e)=false ∧ hb (W.graph.dst e)=false)
    (outside : ∀e∉W.core,hb (W.graph.src e)≠hb (W.graph.dst e))
    (q ε : ℝ) (hq : 0<q)
    (initial : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε)
    (history : (hist:ℝ)*(∑v,((atoms v).length:ℝ))≤ε)
    (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ))
    (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k)
    (paid : PaidResetLayout near Δ r f B K hops ε
      (blockMass (raw).graph pos ix ((raw).siteUnits hb atoms (wire*grain) 256 hist)) traffic b hk L) :
    ∃(Z : ResetInput grainW (q*wire) (q*ε) h C ht) (T : ResetInput.Terminals Z),
      Z.ActorBudget T atoms wire hist f g B ∧ Z.k=k ∧ T.commonDepth=k-max r g ∧ Z.n=n ∧ Fintype.card Z.V=Fintype.card V ∧
      Z.unit=grain ∧ ∃ frame : Z.SourceFrame T pos ix hub g,frame.basis=L := by
  obtain ⟨Z,T,cost,zk,group,zn,card,unit,frame,exactL,_⟩ :=
    physical_grain_budgets_for_ordered W count grain fits pos ix hub atoms wire hist G (Fintype.equivFin _).toEmbedding ((Fintype.equivFin V).toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩)
      near sym branch degree quota ports hK fr rk fg gk positive grainPos allowed positiveRotor power menu room
      saturated edge same inside outside q ε hq initial history small b hk L paid
  exact ⟨Z,T,cost,zk,group,zn,card,unit,frame,exactL⟩

theorem physical_grain_budgets_with_order_rosters (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (vertex : V↪ℕ)
    (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
    (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (quota : Δ*2^decayExponent Δ≤K)
    (ports : 4*K≤Y) (hK : 0<K) (fr : f≤r) (rk : r≤k) (fg : f≤g) (gk : g≤k)
    (positive : 0<wire) (grainPos : 0<grain) (allowed : wire*grain≤B) (positiveRotor : 0<bitsR)
    (power : Y^2*bitsR≤2^f) (menu : ∀p : Equiv.Perm (Fin Y),Configures F G.arcs C bitsR p)
    (room : ∀v i,mass v i≤B) (saturated : ∀v,hub v=true→∀i,mass v i=B)
    (edge : ∀e,pos (W.graph.dst e)∈near (pos (W.graph.src e)))
    (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
    (inside : ∀e∈W.core,hb (W.graph.src e)=false ∧ hb (W.graph.dst e)=false)
    (outside : ∀e∉W.core,hb (W.graph.src e)≠hb (W.graph.dst e))
    (q ε : ℝ) (hq : 0<q)
    (initial : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε)
    (history : (hist:ℝ)*(∑v,((atoms v).length:ℝ))≤ε)
    (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ)) :
    ∃(Z : ResetInput grainW (q*wire) (q*ε) h C ht) (T : ResetInput.Terminals Z),
      Z.ActorBudget T atoms wire hist f g B ∧ Z.k=k ∧ T.commonDepth=k-max r g ∧ Z.n=n ∧ Fintype.card Z.V=Fintype.card V ∧
      Z.unit=grain ∧ Z.width=bitsR ∧ HEq Z.graph G ∧ (∃frame : Z.SourceFrame T pos ix hub g,ResetInput.SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K traffic Δ (blockMass (raw).graph pos ix ((raw).siteUnits hb atoms (wire*grain) 256 hist))) ∧
      Z.placement.OrderedTickets (DescentOrderedReset.grains W count order) := by
  have branch' : 0<Δ := by omega
  have money := Nat.mul_pos positive grainPos
  have hB : 0<B := lt_of_lt_of_le money allowed
  have unitB : wire≤B := (Nat.le_mul_of_pos_right _ grainPos).trans allowed
  let measured := blockMass (raw).graph pos ix ((raw).siteUnits hb atoms (wire*grain) 256 hist)
  have measured_eq (v i) : measured v i=mass v i := W.mass_of_counts count grain fits pos ix hb atoms wire 256 hist v i
  have rawRoom (v i) : measured v i≤B := (measured_eq v i).le.trans (room v i)
  have hopsPos : 0<hops := by unfold nonhubHops;omega
  obtain ⟨b,hk,L,fit,smooth,span,budget,hubs,marked,_⟩ :=
    physical_reset_placement raw pos ix hb atoms (wire*grain) 256 hist (by decide) near sym branch degree hB
      quota hK fr rk rawRoom initial hopsPos small

  obtain ⟨Z,T,cost,zk,group,zn,card,unit,width,board,frame,_,_,roster,tickets⟩ := physical_grain_budgets_for_ordered_rosters
    W count grain fits pos ix hub atoms wire hist G order vertex near sym branch degree quota ports hK fr rk fg gk positive grainPos allowed positiveRotor power menu room saturated edge same inside outside q ε hq initial history small b hk L ⟨fit,smooth,span,budget,hubs,marked⟩
  exact ⟨Z,T,cost,zk,group,zn,card,unit,width,board,⟨frame,roster⟩,tickets⟩

theorem physical_grain_budgets_with_order (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (vertex : V↪ℕ)
    (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
    (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (quota : Δ*2^decayExponent Δ≤K)
    (ports : 4*K≤Y) (hK : 0<K) (fr : f≤r) (rk : r≤k) (fg : f≤g) (gk : g≤k)
    (positive : 0<wire) (grainPos : 0<grain) (allowed : wire*grain≤B) (positiveRotor : 0<bitsR)
    (power : Y^2*bitsR≤2^f) (menu : ∀p : Equiv.Perm (Fin Y),Configures F G.arcs C bitsR p)
    (room : ∀v i,mass v i≤B) (saturated : ∀v,hub v=true→∀i,mass v i=B)
    (edge : ∀e,pos (W.graph.dst e)∈near (pos (W.graph.src e)))
    (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
    (inside : ∀e∈W.core,hb (W.graph.src e)=false ∧ hb (W.graph.dst e)=false)
    (outside : ∀e∉W.core,hb (W.graph.src e)≠hb (W.graph.dst e))
    (q ε : ℝ) (hq : 0<q)
    (initial : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε)
    (history : (hist:ℝ)*(∑v,((atoms v).length:ℝ))≤ε)
    (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ)) :
    ∃(Z : ResetInput grainW (q*wire) (q*ε) h C ht) (T : ResetInput.Terminals Z),
      Z.ActorBudget T atoms wire hist f g B ∧ Z.k=k ∧ T.commonDepth=k-max r g ∧ Z.n=n ∧ Fintype.card Z.V=Fintype.card V ∧
      Z.unit=grain ∧ Nonempty (Z.SourceFrame T pos ix hub g) ∧
      Z.placement.OrderedTickets (DescentOrderedReset.grains W count order) := by
  obtain ⟨Z,T,cost,zk,group,zn,sz,unit,_,_,⟨frame,_⟩,tickets⟩:=physical_grain_budgets_with_order_rosters
    W count grain fits pos ix hub atoms wire hist G order vertex near sym branch degree quota ports hK fr rk fg gk
    positive grainPos allowed positiveRotor power menu room saturated edge same inside outside q ε hq initial history small
  exact ⟨Z,T,cost,zk,group,zn,sz,unit,⟨frame⟩,tickets⟩

theorem physical_grain_budgets_with_units (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
    (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (quota : Δ*2^decayExponent Δ≤K)
    (ports : 4*K≤Y) (hK : 0<K) (fr : f≤r) (rk : r≤k) (fg : f≤g) (gk : g≤k)
    (positive : 0<wire) (grainPos : 0<grain) (allowed : wire*grain≤B) (positiveRotor : 0<bitsR)
    (power : Y^2*bitsR≤2^f) (menu : ∀p : Equiv.Perm (Fin Y),Configures F G.arcs C bitsR p)
    (room : ∀v i,mass v i≤B) (saturated : ∀v,hub v=true→∀i,mass v i=B)
    (edge : ∀e,pos (W.graph.dst e)∈near (pos (W.graph.src e)))
    (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
    (inside : ∀e∈W.core,hb (W.graph.src e)=false ∧ hb (W.graph.dst e)=false)
    (outside : ∀e∉W.core,hb (W.graph.src e)≠hb (W.graph.dst e))
    (q ε : ℝ) (hq : 0<q)
    (initial : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε)
    (history : (hist:ℝ)*(∑v,((atoms v).length:ℝ))≤ε)
    (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ)) :
    ∃(Z : ResetInput grainW (q*wire) (q*ε) h C ht) (T : ResetInput.Terminals Z),
      Z.ActorBudget T atoms wire hist f g B ∧ Z.k=k ∧ T.commonDepth=k-max r g ∧ Z.n=n ∧ Fintype.card Z.V=Fintype.card V ∧
      Z.unit=grain ∧ Nonempty (Z.SourceFrame T pos ix hub g) := by
  obtain ⟨Z,T,cost,zk,group,zn,card,unit,frame,_⟩ := physical_grain_budgets_with_order
    W count grain fits pos ix hub atoms wire hist G (Fintype.equivFin _).toEmbedding ((Fintype.equivFin V).toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩) near sym branch degree quota
    ports hK fr rk fg gk positive grainPos allowed positiveRotor power menu room saturated edge same inside
    outside q ε hq initial history small
  exact ⟨Z,T,cost,zk,group,zn,card,unit,frame⟩

theorem physical_grain_budgets (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
    (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (quota : Δ*2^decayExponent Δ≤K)
    (ports : 4*K≤Y) (hK : 0<K) (fr : f≤r) (rk : r≤k) (fg : f≤g) (gk : g≤k)
    (positive : 0<wire) (grainPos : 0<grain) (allowed : wire*grain≤B) (positiveRotor : 0<bitsR)
    (power : Y^2*bitsR≤2^f) (menu : ∀p : Equiv.Perm (Fin Y),Configures F G.arcs C bitsR p)
    (room : ∀v i,mass v i≤B) (saturated : ∀v,hub v=true→∀i,mass v i=B)
    (edge : ∀e,pos (W.graph.dst e)∈near (pos (W.graph.src e)))
    (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
    (inside : ∀e∈W.core,hb (W.graph.src e)=false ∧ hb (W.graph.dst e)=false)
    (outside : ∀e∉W.core,hb (W.graph.src e)≠hb (W.graph.dst e))
    (q ε : ℝ) (hq : 0<q)
    (initial : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε)
    (history : (hist:ℝ)*(∑v,((atoms v).length:ℝ))≤ε)
    (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ)) :
    ∃(Z : ResetInput grainW (q*wire) (q*ε) h C ht) (T : ResetInput.Terminals Z),
      Z.ActorBudget T atoms wire hist f g B ∧ Z.k=k ∧ T.commonDepth=k-max r g ∧ Z.n=n ∧ Fintype.card Z.V=Fintype.card V ∧
      Nonempty (Z.SourceFrame T pos ix hub g) := by
  obtain ⟨Z,T,cost,zk,group,zn,card,_,frame⟩ := physical_grain_budgets_with_units
    W count grain fits pos ix hub atoms wire hist G near sym branch degree quota ports hK fr rk fg gk positive grainPos allowed positiveRotor power menu room saturated edge same inside outside q ε hq initial history small
  exact ⟨Z,T,cost,zk,group,zn,card,frame⟩

theorem physical_grain_control (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
    (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (quota : Δ*2^decayExponent Δ≤K)
    (ports : 4*K≤Y) (hK : 0<K) (fr : f≤r) (rk : r≤k) (fg : f≤g) (gk : g≤k)
    (positive : 0<wire) (grainPos : 0<grain) (allowed : wire*grain≤B) (positiveRotor : 0<bitsR)
    (power : Y^2*bitsR≤2^f) (menu : ∀p : Equiv.Perm (Fin Y),Configures F G.arcs C bitsR p)
    (room : ∀v i,mass v i≤B) (saturated : ∀v,hub v=true→∀i,mass v i=B)
    (edge : ∀e,pos (W.graph.dst e)∈near (pos (W.graph.src e)))
    (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
    (inside : ∀e∈W.core,hb (W.graph.src e)=false ∧ hb (W.graph.dst e)=false)
    (outside : ∀e∉W.core,hb (W.graph.src e)≠hb (W.graph.dst e))
    (q ε : ℝ) (hq : 0<q)
    (initial : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε)
    (history : (hist:ℝ)*(∑v,((atoms v).length:ℝ))≤ε)
    (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ)) :
    ∃Z : ResetInput grainW (q*wire) (q*ε) h C ht,Nonempty (ResetInput.Terminals Z) := by
  obtain ⟨Z,T,_⟩ := physical_grain_budgets W count grain fits pos ix hub atoms wire hist G near sym branch degree quota
    ports hK fr rk fg gk positive grainPos allowed positiveRotor power menu room saturated edge same
    inside outside q ε hq initial history small
  exact ⟨Z,⟨T⟩⟩

theorem physical_grain_input (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
    (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (quota : Δ*2^decayExponent Δ≤K)
    (ports : 4*K≤Y) (hK : 0<K) (fr : f≤r) (rk : r≤k) (fg : f≤g) (gk : g≤k)
    (positive : 0<wire) (grainPos : 0<grain) (allowed : wire*grain≤B) (positiveRotor : 0<bitsR)
    (power : Y^2*bitsR≤2^f) (menu : ∀p : Equiv.Perm (Fin Y),Configures F G.arcs C bitsR p)
    (room : ∀v i,mass v i≤B) (saturated : ∀v,hub v=true→∀i,mass v i=B)
    (edge : ∀e,pos (W.graph.dst e)∈near (pos (W.graph.src e)))
    (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
    (inside : ∀e∈W.core,hb (W.graph.src e)=false ∧ hb (W.graph.dst e)=false)
    (outside : ∀e∉W.core,hb (W.graph.src e)≠hb (W.graph.dst e))
    (q ε : ℝ) (hq : 0<q)
    (initial : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε)
    (history : (hist:ℝ)*(∑v,((atoms v).length:ℝ))≤ε)
    (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ)) :
    Nonempty (ResetInput grainW (q*wire) (q*ε) h C ht) :=
  (physical_grain_control W count grain fits pos ix hub atoms wire hist G near sym branch degree quota
    ports hK fr rk fg gk positive grainPos allowed positiveRotor power menu room saturated edge same
    inside outside q ε hq initial history small).elim (fun Z _=>⟨Z⟩)

end
end Hierarchy.DescentSixParty

end OAI
