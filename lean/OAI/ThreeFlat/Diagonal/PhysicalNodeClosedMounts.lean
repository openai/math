import OAI.ThreeFlat.Diagonal.PhysicalNodeTapeBounds
import OAI.ThreeFlat.Diagonal.NavigationRootPublication

namespace OAI
/-! # The original packed parameter words survive both native archive passes -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication


open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.NavigationNodeRows RAM.TickPhysicalABI PhysicalStage NavigationDirectory
open scoped Fin.CommRing Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u rem low stride cells off tariff : ℕ} (shape : PhysicalPinsExpr.Shape)
local notation "pa" => Parameters.cursor B u rem low stride cells shape off tariff
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "d" => (2^B.exponent 0)
local notation "P" => B.repeat n
variable (X : PhysicalStage.State (2^B.exponent 0) ((B.repeat (u^8)).charge+rem))
local notation "vv" => Fintype.card X.Base
local notation "ss" => (P).directory rem vv
local notation "edges" => (P).finalEdges rem vv
local notation "A" => (pa).archive d W
local notation "N" => (pa).nodeArchive A ss W
local notation "R" => (pa).rootArchive A N ss W
local notation "rs" => nodeLayers (A).K ss (A).cursor (A).seedLayer
local notation "lib" => Parameters.gridWords B u
local notation "tailWords" => List.ofFn (fun j : Fin 22=>(R).word j)++stageTape rs
local notation "suffix" => nodeTape (N).banks (N).headerBase rs++tailWords
local notation "words" => lib++(pa).staticWords B n rem W
local notation "cur" => ((A).control:Word W)

private theorem low_stable (x : ℕ) (hx : x<(A).seed) : stable N rs x := by
  have below (j : ℕ) (hj : 20 < j) : x < TickWorkspace.base (pa).age j := by
    calc
      x < TickWorkspace.base (pa).age 20 := hx
      _ ≤ TickWorkspace.base (pa).age 20 + TickWorkspace.stride (pa).age :=
        Nat.le_add_right _ _
      _ ≤ TickWorkspace.base (pa).age j := TickWorkspace.apart hj
  have current : x < (N).banks.current := below 40 (by decide)
  have counter : x < (N).counter := lt_of_lt_of_le current (Nat.le_add_right _ 3)
  have header : x < (N).headerBase := below 41 (by decide)
  have charges : x < (N).banks.charges := below 43 (by decide)
  have nodes : x < (N).banks.nodes := below 44 (by decide)
  refine ⟨ne_of_lt counter, ne_of_lt current, Or.inl header, ?_⟩
  intro i
  exact ⟨ne_of_lt counter, ne_of_lt current,
    Or.inl (lt_of_lt_of_le charges (Nat.le_add_right _ _)),
    Or.inl (lt_of_lt_of_le nodes (Nat.le_add_right _ _))⟩

/-- All protected tick pin words, including every bit of the original parameter
image, survive the actual starts, accepted journal and selected node archive. -/
theorem cursor_closed_low
    (card : vv=(pa).axes) (hu : 40≤u) (degree : d≤u) (half : low=u^10/2)
    (depth : (P).charge+rem+low≤u^10+2*u^6) (alphabet : B.alphabetCap≤u)
    (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    {budget : ℕ} (room : RunBounds W N rs budget) (limits : (A).Limits u cur ss edges (A).pairCapacity)
    (bits : ℕ→Bool) (input out : Memory W) (src : (A).SeedSources ss edges lib suffix bits input)
    (E : ((P).run rem X).Records)
    (closed : (A).Closed B n rem X bits E ((A).startedMemory ss edges lib bits input n) out) :
    (∀ x,x<(A).seed→ out x=input x) ∧
    ∀ Q : Program rs,∀ x,x<(A).seed→state N Q out (rs).length x=input x := by
  have axesBound : (pa).axes ≤ u^10+2*u^6 := (Nat.le_add_right ((P).charge+rem) low).trans depth
  have space : (A).SeedSpace W := (pa).seed_space d hu degree axesBound
  have old : (A).MountedRange ss edges W := by
    rw [show ss=(P).directory rem (pa).axes by rw [card]]
    exact (pa).block_seed_mounted d B rem low edges hu alphabet levels score rfl half depth
  have counter : (A).control+3<2^W:=room.counterSize
  have before (x : ℕ) (hx : x<(A).seed) : out x=input x :=
    Archive.Closed.before_seed lib suffix closed space old src limits counter x hx
  exact ⟨before,fun Q x hx=>(final_input N Q out room x (low_stable B shape X x hx)).trans (before x hx)⟩

open private mount_framed_words from OAI.ThreeFlat.Diagonal.PhysicalNodeTapeBounds

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
/-- The S41 mounted image before node publication and the two root input mounts
afterwards use the exact grid, directory, node, root and stage words on the input tape. -/
theorem cursor_closed_mounts
    (card : vv=(pa).axes) (hu : 40≤u) (degree : d≤u) (half : low=u^10/2)
    (depth : (P).charge+rem+low≤u^10+2*u^6) (alphabet : B.alphabetCap≤u)
    (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    {budget : ℕ} (room : RunBounds W N rs budget) (root : RootArchive.PublishRoom R W)
    (limits : (A).Limits u cur ss edges (A).pairCapacity)
    (bits : ℕ→Bool) (input out : Memory W) (src : (A).SeedSources ss edges lib suffix bits input)
    (E : ((P).run rem X).Records)
    (closed : (A).Closed B n rem X bits E ((A).startedMemory ss edges lib bits input n) out)
    (fit : off+W*(words).length ≤ shape.parameterBits)
    (rawLow : 2+shape.advice+shape.teamBits+shape.timeBits+shape.parameterBits≤TickWorkspace.stride u) :
    Mount (image N (rs).length) (tapeWord N rs) out ∧
      ∀ Q : Program rs, Mount (R).headerImage (R).headerData (state N Q out (rs).length) ∧
        Mount (R).stageImage ((R).stageData rs) (state N Q out (rs).length) := by
  have original := cursor_closed_low B shape X card hu degree half depth alphabet levels score room limits
    bits input out src E closed
  let dir:=(A).directory ss edges W
  let before:=lib++dir
  have static : (pa).staticWords B n rem W=dir++suffix := by
    simpa only [card,dir] using (pa).staticWords_directory B n rem W (show (P).charge+rem=(pa).axes from rfl)
  have parts : words=before++(nodeTape (N).banks (N).headerBase rs++tailWords) := by
    rw [static];exact (List.append_assoc ..).symm
  have srcBits (i : ℕ) (hi : i<(words).length) (j : ℕ) (hj : j<W) :
      input ((pa).rawTables+W*i+j)=((((words[i]?.getD 0:ℕ):Word W).val.testBit (W-1-j)).toNat:Word W) := by
    rw [static] at hi ⊢
    exact src.publicBits i hi j hj
  have rawEnd : (pa).rawTables+W*(words).length≤TickWorkspace.stride u := by
    change 2+shape.advice+shape.teamBits+shape.timeBits+off+W*(words).length≤_
    omega
  have bounded (i : ℕ) (hi : i<(words).length) (j : ℕ) (hj : j<W) : (pa).rawTables+W*i+j<TickWorkspace.stride u := by
    have more:=Nat.mul_le_mul_left W (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at more;omega
  have atRaw : (N).rawHeader=(pa).rawTables+W*before.length := by
    have b : (pa).codebookWords=(lib).length:=src.book
    change (pa).rawTables+W*(pa).codebookWords+W*(64*((ss).length+2))=(pa).rawTables+W*(lib++dir).length
    have dl : dir.length=64*((ss).length+2) := Archive.directory_length ..
    rw [List.length_append,b,dl]
    exact (Nat.add_assoc _ _ _).trans
      (congrArg (fun size => (pa).rawTables+size) (Nat.mul_add W (lib).length (64*((ss).length+2))).symm)
  have size : before.length+16*(rs).length≤(words).length := by
    have total : (words).length = before.length+(16*(rs).length+(tailWords).length) := by
      calc
        _ = (before++(nodeTape (N).banks (N).headerBase rs++tailWords)).length := congrArg List.length parts
        _ = _ := by simp only [List.length_append,nodeTape_length]
    omega
  have partSize:=Nat.mul_le_mul_left W size
  rw [Nat.mul_add] at partSize
  have sourceEnd : (N).rawHeader+W*(16*(rs).length)≤(N).headerBase := by
    have t : TickWorkspace.stride u≤(N).headerBase:=TickWorkspace.lower u 41
    rw [atRaw];omega
  have nonempty : 0<(rs).length := by rw [nodeLayers_length];omega
  let zero : Fin (rs).length := ⟨0,nonempty⟩
  have charge := (room.layer zero).chargeEnd
  have last := (room.layer zero).nodeEnd
  have chargeFit : (N).banks.charges<2^W := by omega
  have seedLow : TickWorkspace.stride u≤(A).seed:=TickWorkspace.lower u 20
  have phase : (N).phase<2^W := by
    have strideWide : 2≤TickWorkspace.stride u := by
      have agePos : 0 < u^10 := Nat.pow_pos (show 0 < u by omega)
      have pow : 2≤2^(u^10) := Nat.le_self_pow (Nat.ne_of_gt agePos) 2
      exact pow.trans (Nat.le_self_pow (by decide : 4≠0) _)
    have g : TickWorkspace.base u 0+TickWorkspace.stride u≤(N).banks.current := TickWorkspace.apart (by decide : 0<40)
    have ctr:=room.pointerSize
    change TickWorkspace.base u 0+2<2^W
    omega
  have headerEnd : (N).headerBase+16*(rs).length≤(N).banks.charges := by
    let j : Fin (rs).length:=⟨(rs).length-1,by omega⟩
    have r := (room.layer j).header
    change (N).headerBase+16*j.val+16≤(N).banks.charges at r
    dsimp only [j] at r;omega
  constructor
  · refine mount_framed_words N rs out (pa).rawTables before tailWords words parts atRaw phase
      sourceEnd (headerEnd.trans_lt chargeFit) ?_
    intro i hi j hj
    exact (original.1 _ ((bounded i hi j hj).trans_le seedLow)).trans (srcBits i hi j hj)
  · intro Q
    let m : Memory W := state N Q out (rs).length
    have actual (i : ℕ) (hi : i < (words).length) (j : ℕ) (hj : j < W) :
        m ((pa).rawTables+W*i+j) =
          ((((words[i]?.getD 0 : ℕ) : Word W).val.testBit (W-1-j)).toNat : Word W) :=
      (original.2 Q _ ((bounded i hi j hj).trans_le seedLow)).trans (srcBits i hi j hj)
    have same : (R).stageRaw+W*(4*(R).stageCount) = (pa).rawTables+W*(words).length := by
      change (RootArchive.parameterArchive pa d ss W).stageRaw +
          W*(4*(RootArchive.parameterArchive pa d ss W).stageCount) =
          2+shape.advice+shape.teamBits+shape.timeBits+off+W*(words).length
      rw [card]
      exact RootArchive.cursor_raw_end B u rem low stride cells shape off tariff d
    have toRoot : TickWorkspace.stride u ≤ (R).header := TickWorkspace.lower u 42
    have toStage : TickWorkspace.stride u ≤ directory (R).age 2 := by
      change TickWorkspace.stride u ≤ TickWorkspace.base u 11+_
      exact (TickWorkspace.lower u 11).trans (Nat.le_add_right ..)
    have separated : (R).stageRaw+W*(4*(R).stageCount) ≤ min (R).header (directory (R).age 2) := by
      rw [same]
      exact le_min (rawEnd.trans toRoot) (rawEnd.trans toStage)
    have rootHead : (R).header+22 < 2^W := root.chargeAfter.trans_lt chargeFit
    have stageHead : directory (R).age 2+4*(R).stageCount < 2^W :=
      root.staticHeader.trans_lt (lt_of_le_of_lt (Nat.le_add_right _ 22) rootHead)
    have mountAt (sites : ℕ) (numbered : sites = (pa).axes) :
        let ops := (P).directory rem sites
        let bank := (pa).nodeArchive A ops W
        let archive := (pa).rootArchive A bank ops W
        let rows := nodeLayers (A).K ops (A).cursor (A).seedLayer
        archive.phase < 2^W →
        archive.stageRaw+W*(4*archive.stageCount) ≤ min archive.header (directory archive.age 2) →
        archive.header+22 < 2^W → directory archive.age 2+4*archive.stageCount < 2^W →
        Mount archive.headerImage archive.headerData m ∧ Mount archive.stageImage (archive.stageData rows) m := by
      subst sites
      intro ops bank archive rows phaseFit apart headFit stagesFit
      exact RootArchive.parameter_mounts (pa) B n rem W lib m src.book.symm
        phaseFit apart headFit stagesFit actual
    exact mountAt vv card phase separated rootHead stageHead

end

end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
