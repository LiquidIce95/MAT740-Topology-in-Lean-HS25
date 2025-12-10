import Mathlib.Tactic

open Set

universe u v

/- A topology on a type `X` -/
class Topology (X : Type u) : Type u where
  /- A predicate witnessing that a set `s : Set X` is open. -/
  Open : Set X → Prop
  /- The universal set {x : X | True} is open. -/
  Open_univ : Open Set.univ
  /- Binary intersections of opens are open. -/
  Open_inter : ∀ s t, Open s → Open t → Open (s ∩ t)
  /- Unions of families of open sets are open. -/
  Open_sUnion : ∀ s, (∀ t ∈ s, Open t) → Open (⋃₀ s)

/- # Open and Closed sets -/

variable {X : Type u} {Y : Type v} [Topology X] [Topology Y] {s t : Set X}

/- Predicate on subsets of ambient topology on X. -/
def Open (s : Set X) : Prop := Topology.Open s

/- A set is closed if its complement is open. -/
@[simp]
def Closed (s : Set X) : Prop := Open sᶜ

@[simp]
/- A neighborhood of `x : X` is an open set containing `x`. -/
def Nbhd (s : Set X) (x : X) := Open s ∧ x ∈ s

/- We state the defining properties as theorems so we can apply them easily in proofs. -/
@[simp]
theorem Open_univ : Open (univ : Set X) := Topology.Open_univ

@[simp]
theorem Open_inter (hs : Open s) (ht : Open t) : Open (s ∩ t) := Topology.Open_inter s t hs ht

@[simp]
theorem Open_sUnion {s : Set (Set X)} (h : ∀ t ∈ s, Open t) : Open (⋃₀ s) :=
  Topology.Open_sUnion s h

@[simp]
theorem Open_iUnion
  {I : Type*} {A : I → Set X} (h : ∀ i, Open (A i)) :
  Open (⋃ i, A i) := by
    rw [← sUnion_range]
    apply Open_sUnion
    intro U hU
    rw [mem_range] at hU
    obtain ⟨i, hi⟩ := hU
    specialize h i
    rw [hi] at h
    exact h

@[simp]
theorem Open_biUnion {A : Set (Set X)} (h : ∀ a ∈ A, Open (a))
  : Open (⋃ a ∈ A, a) := by
  rw [← sUnion_eq_biUnion]
  apply Open_sUnion
  exact h

@[simp]
theorem Open_preimageUnion
   {Z : Type u} {A : Set (Set Z)} {f : X → Z} (h : ∀ a ∈ A, Open (f ⁻¹' a))
  : Open (⋃ a ∈ A, f ⁻¹' a) := by
  rw [← @sUnion_image]
  apply Open_sUnion
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact h

@[simp]
theorem Open_empty : Open (∅ : Set X) := by
  have w : ∀ t ∈ (∅ : Set (Set X)), Open t := by
    intro t ht
    contradiction
  apply Open_sUnion at w
  rw [sUnion_empty] at w
  exact w

/- # Instances of topologies -/

/- For every type `X`, there is a topology on `X` where every set is open. -/
def discreteTopology (X : Type u) : Topology X where
  Open := fun s => True
  Open_univ := by trivial
  Open_inter := by intros ; trivial
  Open_sUnion := by intros ; trivial

/- For every type `X`, there is a topology on `X` where only `∅` and `univ` are open. -/
def indiscreteTopology (X : Type u) : Topology X where
  Open := fun s => s = ∅ ∨ s = univ
  Open_univ := by right ; rfl
  Open_inter := by
    intro a b ha hb
    obtain ha1 | ha2 := ha
    case inl =>
      left ; rw [ha1] ; simp
    case inr =>
      obtain hb1 | hb2 := hb
      case inl =>
        left ; rw [hb1] ; simp
      case inr =>
        right ; rw [ha2, hb2]; simp
  Open_sUnion := by
    intro s hs
    by_cases c : univ ∈ s
    case pos =>
      right
      rw [sUnion_eq_univ_iff]
      intro x
      use univ
      exact ⟨c, trivial⟩
    case neg =>
      left
      rw [sUnion_eq_empty]
      intro t ht
      specialize hs t ht
      obtain hs1 | hs2 := hs
      case inl => exact hs1
      case inr => rw [hs2] at ht; contradiction

/- Topology restricted to an open subset of space X. -/
def restrictionTopology [Topology X] (U : Set X) (open_U : Open U) : Topology ↥U where
  Open := fun s => Open (U ∩ s)
  Open_univ := by
    rw [Subtype.coe_image_univ, inter_eq_self_of_subset_left fun {a} a => a]
    exact open_U
  Open_inter := by
    intro V W open_V open_W
    rw [image_val_inter_self_right_eq_coe] at open_W
    rw [image_val_inter_self_right_eq_coe] at open_V
    rw [image_val_inter_self_right_eq_coe, image_val_inter]
    apply @Open_inter X
    case hs => exact open_V
    case ht => exact open_W
  Open_sUnion := by
    intro C hC
    simp only [image_val_inter_self_right_eq_coe] at hC
    rw [image_val_inter_self_right_eq_coe, image_sUnion]
    apply @Open_sUnion X
    intro V hV
    obtain ⟨V',⟨hV'1, hV'2⟩⟩ := hV
    specialize hC V' hV'1
    rw [hV'2] at hC
    exact hC



----------------------------------------------------------------
-- Closure and its basic properties
----------------------------------------------------------------

section Closure

variable {X : Type u} [Topology X]


/-- The closure of `A` as intersection of all closed supersets. -/
@[simp]
def Closure (A : Set X) : Set X :=
  ⋂ C : {C : Set X | Closed C ∧ A ⊆ C}, C

/--Is very easy to prove via induction but somehow here ... its not  -/
@[simp]
theorem finite_sInter_open
  (S : Set (Set X))
  (hfin : S.Finite)
  (hopen : ∀ U ∈ S, Open U) :
  Open (⋂s∈ S, s) := by
    sorry

/--The lemma 'without proof' that ironically needs a lot of proving-/
@[simp]
theorem finite_union_of_closed_is_closed
  (S : Set (Set X))
  (hfin : S.Finite)
  (hclosed : ∀ C ∈ S, Closed C) :
  (Closed (⋃ s ∈ S, s)) := by
    have hDeMorgan : (⋃ s∈S,s)ᶜ = ⋂s∈S, sᶜ := by
      simp
    have h : (⋃s∈ S,s)= ((⋃s∈S,s)ᶜ)ᶜ := by ext; simp
    rw [h]
    rw [hDeMorgan]
    rw [Closed]
    have h2 : (⋂s∈ S, sᶜ )ᶜᶜ = (⋂s∈ S,sᶜ) := by
      simp
    rw [h2]
    have h3 : ∀ s ∈ S, Open (sᶜ) := by
      intro s hs
      have hsClosed : Closed s := hclosed s hs
      simpa [Closed] using hsClosed
    let S' : Set (Set X) := {sᶜ | s∈ S}
    have h4 : ⋂ s∈S, sᶜ = ⋂ s'∈ S',s':= by
      ext x
      simp [S']
    rw [h4]
    have h5 : ∀s'∈ S', Open s' := by
      intro s' hs'
      rcases hs' with ⟨s, hsS, rfl⟩
      exact h3 s hsS
    have h6 : S'.Finite := by
      have hEq : S' = compl '' S := by
        ext U
        simp [S']
      rw [hEq]
      apply hfin.image
    apply finite_sInter_open at h5
    case hfin => assumption
    assumption

@[simp]
theorem inter_of_closed_is_closed
  (S : Set (Set X))
  (hclosed : ∀ C ∈ S, Closed C) :
  Closed (⋂ s ∈ S, s) := by
    rw [Closed]
    let S' : Set (Set X) := {sᶜ | s ∈ S}
    have hDeMorgan : (⋂ s ∈ S, s)ᶜ = ⋃ s ∈ S, sᶜ := by
      ext x
      simp
    have h1 : (⋂ s∈ S, s)ᶜ = ⋃ s'∈ S', s' := by
      ext x
      simp [S']
    rw [h1]
    have h2 : ∀ s' ∈ S', Open s' := by
      intro s' hs'
      rcases hs' with ⟨s, hsS, rfl⟩
      have hsClosed : Closed s := hclosed s hsS
      simpa [Closed] using hsClosed
    apply Open_sUnion at h2
    have h6: (⋃₀S'=⋃s∈S',s) := by
      simp [sUnion_eq_biUnion]
    rw [h6] at h2
    assumption

@[simp]
theorem closure_is_closed (A : Set X) : Closed (Closure A) := by
  have hclosed : ∀ C ∈ {C : Set X | Closed C ∧ A ⊆ C}, Closed C := by
    intro C hC; exact (And.left hC)
  have hEq : Closure A = ⋂ s ∈ {C : Set X | Closed C ∧ A ⊆ C}, s := by
    ext x; simp [Closure]
  have hInter : Closed (⋂ s ∈ {C : Set X | Closed C ∧ A ⊆ C}, s) :=
    inter_of_closed_is_closed _ hclosed
  rw [hEq]
  trivial


/-- Theorem 1 -/
@[simp]
theorem chara_closed
  (A : Set X) :
  Closed A ↔ A= Closure A := by
    constructor
    case mp =>
      intro a_closed
      have a_closure_set : Closed A ∧ A⊆ A := by
        trivial
      have closure_is_subset: Closure A ⊆ A := by
        intro x
        intro x_in_closure
        have x_is_in_all_sets : ∀C ∈  {C : Set X| Closed C ∧ A⊆ C}, x∈ C := by
           simpa [Closure] using x_in_closure
        apply x_is_in_all_sets at a_closure_set
        assumption
      have a_is_subset : A ⊆ Closure A := by
        intro x
        intro x_in_a
        have x_in_all : ∀C ∈ {C:Set X| Closed C ∧ A⊆ C},x∈ C := by
          intro c
          intro some_c
          have a_subset_c : A⊆c :=
             And.right some_c
          exact a_subset_c x_in_a
        have x_in_inter : x∈ (⋂ C ∈ {C: Set X| Closed C ∧ A⊆C},C):= by
            simpa [Set.mem_iInter] using x_in_all
        have being_same : Closure A = ⋂ c ∈ {C:Set X| Closed C ∧ A⊆ C},c := by
          ext y
          simp [Closure, Set.mem_iInter, Set.mem_setOf_eq]
        simpa [being_same] using x_in_inter
      apply Set.Subset.antisymm
      trivial
      trivial
    case mpr =>
      intro being_same
      rw [being_same]
      apply closure_is_closed


@[simp]
def neighbourhood
  (x : X) : Set (Set X) :=
  {U : Set X| Open U ∧ x∈U}

/-- Theorem 2 -/
@[simp]
theorem consistency_alt_def
  (A : Set X) :
  (Closed A ↔ ∀x∈ Aᶜ,∃U ∈ (neighbourhood x), U⊆Aᶜ) := by
    constructor
    case mp =>
      intro a_closed
      have a_is_closure : A=Closure A := by
        apply (chara_closed A).1 a_closed
      let closure_sets :Set (Set X):= {C: Set X| Closed C ∧ A⊆ C}
      have a_closure_correct : A=⋂c∈ closure_sets,c := by
        rw [Closure] at a_is_closure
        rw [a_is_closure]
        ext x
        simp [closure_sets,mem_iInter,Subtype.forall]
      have a_subset : ∀ Z∈ closure_sets,A⊆ Z := by
         intro Z hZ
         exact hZ.right
      have z_comp_subset_a_comp : ∀Z∈ closure_sets, Zᶜ ⊆ Aᶜ := by
        intro Z hZ
        intro y hy
        simp at hy
        intro hyA
        exact hy (hZ.right hyA)
      intro x
      intro x_in_a
      let nei_x : Set (Set X) := neighbourhood x
      have x_in_closure_comp : x∈ ⋃z∈ closure_sets ,zᶜ := by
        rw [a_closure_correct] at x_in_a
        simp [mem_iUnion, mem_compl_iff] at x_in_a ⊢
        exact x_in_a
      have exists_z_compl : ∃z∈ closure_sets, x∈ zᶜ  := by
        rw [Set.mem_iUnion] at x_in_closure_comp
        rcases x_in_closure_comp with ⟨z, hz⟩
        rw [Set.mem_iUnion] at hz
        rcases hz with ⟨hz_mem, hx⟩
        exact ⟨z, hz_mem, hx⟩
      have z_comp_open_nei : ∃z∈ closure_sets, zᶜ∈ nei_x:= by
        rcases exists_z_compl with ⟨Z, hZ, hxZ⟩
        exact ⟨Z, hZ, ⟨hZ.1, hxZ⟩⟩
      rcases z_comp_open_nei with ⟨Z, hZ, hZnei⟩
      refine ⟨Zᶜ, ?_, ?_⟩
      · have : Zᶜ ∈ neighbourhood x := by
          simpa [nei_x] using hZnei
        exact this
      · intro y hy
        exact z_comp_subset_a_comp Z hZ hy
    case mpr =>
    intro h
    have hA_compl_open : Open Aᶜ := by
      -- For each x in Aᶜ, we have a neighborhood U_x contained in Aᶜ
      -- We'll express Aᶜ as the union of all these U_x
      let S : Set (Set X) := {U | ∃ (x : X) (hx : x ∈ Aᶜ), U ∈ neighbourhood x ∧ U ⊆ Aᶜ}
      have hS_open : ∀ U ∈ S, Open U := by
        intro U hU
        rcases hU with ⟨x, hx, hU_nei, hU_sub⟩
        exact hU_nei.1  -- Since U ∈ neighbourhood x, it's open

      have hA_compl_eq : Aᶜ = ⋃₀ S := by
        ext x
        constructor
        · intro hx
          rcases h x hx with ⟨U, hU_nei, hU_sub⟩
          refine ⟨U, ⟨x, hx, hU_nei, hU_sub⟩, hU_nei.2⟩
        · intro hx
          rcases hx with ⟨U, hU_S, hxU⟩
          rcases hU_S with ⟨y, hy, hU_nei, hU_sub⟩
          exact hU_sub hxU

      rw [hA_compl_eq]
      have better_union : ⋃ s∈ S, s = ⋃₀S := by
          simp [sUnion_eq_biUnion]
      rw [← better_union]
      exact Open_biUnion hS_open
    exact hA_compl_open

















































































end Closure
