import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter

open scoped BigOperators

-- [TABLET NODE: ThreeUniformThreeSimpleLocalSetup]
structure ThreeUniformThreeSimpleLocalSetup (D : ℕ)
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (F : MultiHypergraph V E) (f : E) where
-- BODY
  D_large : 100 ≤ D
  class_mem : F ∈ HypergraphClass (V := V) (E := E) 3 3 D
  b : ℝ
  b_eq :
    b =
      @LocalBParameter E _ _ (LineGraphOfHypergraph F)
        (Classical.decRel (LineGraphOfHypergraph F).Adj) (3 * D) f
  maximizes_b :
    ∀ {V' E' : Type*} [Fintype E'] [DecidableEq E'] [DecidableEq V'],
      ∀ F' : MultiHypergraph V' E',
        F' ∈ HypergraphClass (V := V') (E := E') 3 3 D →
        ∀ e' : E',
          @LocalBParameter E' _ _ (LineGraphOfHypergraph F')
              (Classical.decRel (LineGraphOfHypergraph F').Adj) (3 * D) e'
            ≤ b
  saturated_neighbors :
    ((Finset.univ : Finset E).filter
      (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)).card = 3 * (D - 1)
  saturated_vertex_degrees :
    ∀ v : V, v ∈ F.edge f → HypergraphDegree F v = D
  X : Finset V
  Xs : Finset V
  Xb : Finset V
  X_eq :
    X =
      (Finset.univ : Finset V).filter
        (fun x =>
          x ∉ F.edge f ∧
            ∃ g : E, g ≠ f ∧ x ∈ F.edge g ∧ (F.edge g ∩ F.edge f).Nonempty)
  X_partition : Xs ∪ Xb = X
  Xs_disjoint_Xb : Disjoint Xs Xb
  Xb_eq : Xb = X \ Xs
  V1 : Finset E
  V2 : Finset E
  V1_eq :
    V1 =
      ((Finset.univ : Finset E).filter
        (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)).filter
          (fun g => (F.edge g ∩ Xs).Nonempty)
  V2_eq :
    V2 =
      ((Finset.univ : Finset E).filter
        (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)) \ V1
  V_partition :
    V1 ∪ V2 =
      (Finset.univ : Finset E).filter
        (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)
  V1_disjoint_V2 : Disjoint V1 V2
  P : ℝ
  T : ℝ
  W : ℝ
  WXs : ℝ
  WXb : ℝ
  Y : ℝ
  T1 : ℝ
  T2 : ℝ
  totalX : ℝ
  totalXs : ℝ
  totalXb : ℝ
  vertexDegreeIntoF : V → ℝ
  rowDegreeOverX : V → ℝ
  crossDegree : E → ℝ
  vertexDegreeIntoF_eq :
    ∀ x : V,
      vertexDegreeIntoF x =
        ∑ v ∈ F.edge f,
          (((Finset.univ : Finset E).filter
            (fun g => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ)
  rowDegreeOverX_eq :
    ∀ v : V,
      rowDegreeOverX v =
        ∑ x ∈ X,
          (((Finset.univ : Finset E).filter
            (fun g => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ)
  crossDegree_eq :
    ∀ g : E,
      crossDegree g =
        ∑ x ∈ F.edge g \ F.edge f,
          ∑ v ∈ F.edge f \ F.edge g,
            (((Finset.univ : Finset E).filter
              (fun h => v ∈ F.edge h ∧ x ∈ F.edge h)).card : ℝ)
  P_is_independent_pair_count :
    P =
      (@IndependentPairCount E _ _ (LineGraphOfHypergraph F)
        (Classical.decRel (LineGraphOfHypergraph F).Adj) f : ℝ)
  T_is_independent_triple_count :
    T =
      (@IndependentTripleCount E _ _ (LineGraphOfHypergraph F)
        (Classical.decRel (LineGraphOfHypergraph F).Adj) f : ℝ)
  pair_identity : P = 3 * (D : ℝ) ^ (2 : ℕ) - 6 * (D : ℝ) + 3 - W + Y
  Y_nonnegative : 0 ≤ Y
  W_split : W = WXs + WXb
  T_split : T = T1 + T2
  T1_is_triangle_count_meeting_V1 :
    T1 =
      (((Finset.univ : Finset (Finset E)).filter (fun S =>
        S.card = 3 ∧
          S ⊆ ((Finset.univ : Finset E).filter
            (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)) ∧
          (∀ ⦃g⦄, g ∈ S → ∀ ⦃h⦄, h ∈ S → g ≠ h →
            ¬ (g ≠ h ∧ (F.edge g ∩ F.edge h).Nonempty)) ∧
          ∃ g ∈ S, g ∈ V1)).card : ℝ)
  T2_is_triangle_count_inside_V2 :
    T2 =
      (((Finset.univ : Finset (Finset E)).filter (fun S =>
        S.card = 3 ∧
          S ⊆ ((Finset.univ : Finset E).filter
            (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)) ∧
          (∀ ⦃g⦄, g ∈ S → ∀ ⦃h⦄, h ∈ S → g ≠ h →
            ¬ (g ≠ h ∧ (F.edge g ∩ F.edge h).Nonempty)) ∧
          S ⊆ V2)).card : ℝ)
  totalX_eq_sum : totalX = ∑ x ∈ X, vertexDegreeIntoF x
  totalXs_eq_sum : totalXs = ∑ x ∈ Xs, vertexDegreeIntoF x
  totalXb_eq_sum : totalXb = ∑ x ∈ Xb, vertexDegreeIntoF x
  totalX_value : totalX = 6 * ((D : ℝ) - 1)
  Xs_total_cutoff : totalXs ≤ (D : ℝ) / 2
  Xs_maximal_under_cutoff :
    ∀ x : V, x ∈ Xb → (D : ℝ) / 2 < totalXs + vertexDegreeIntoF x
  Xb_total_eq : totalXb = totalX - totalXs
  column_bound : ∀ x : V, x ∈ X → vertexDegreeIntoF x ≤ (D : ℝ)
  row_sum : ∀ v : V, v ∈ F.edge f → rowDegreeOverX v = 2 * ((D : ℝ) - 1)
  Xs_low_degree_maximal :
    ∀ x ∈ Xs, ∀ y ∈ Xb, vertexDegreeIntoF x ≤ vertexDegreeIntoF y
  V2_edge_shape :
    ∀ g : E, g ∈ V2 → (F.edge g ∩ F.edge f).card = 1 ∧ (F.edge g ∩ Xb).card = 2
  WXs_is_weight_of_Xs :
    WXs =
      ∑ x ∈ Xs,
        ∑ p ∈ ((Finset.univ : Finset (Finset V)).filter
          (fun p => p.card = 2 ∧ p ⊆ F.edge f)),
          ∏ v ∈ p,
            (((Finset.univ : Finset E).filter
              (fun g => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ)
  WXb_is_weight_of_Xb :
    WXb =
      ∑ x ∈ Xb,
        ∑ p ∈ ((Finset.univ : Finset (Finset V)).filter
          (fun p => p.card = 2 ∧ p ⊆ F.edge f)),
          ∏ v ∈ p,
            (((Finset.univ : Finset E).filter
              (fun g => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ)
  T1_nonnegative : 0 ≤ T1
  T2_nonnegative : 0 ≤ T2
