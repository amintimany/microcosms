From microcosms Require Import prelude positive_pairs.
From stdpp Require Import countable gmap finite.
From iris.algebra Require Import functions gmap proofmode_classes.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export iprop own.
Import uPred.

(* Taken from gmap cmra construction;
  this is needed for the stronger allocation of mcown compared to own *)
Section freshness.
  Local Set Default Proof Using "Type*".
  Context `{!EqDecision K, !Countable K, !Infinite K} {A : cmra}.
  Lemma alloc_updateP_strong_dep {N} (g : K → option K) (h : N → K → K) (S : list N)
    (Q : gmap K A → Prop) (I : K → Prop) m (f : N → K → A) :
    NoDup S →
    pred_infinite I →
    (∀ n1 n2 k, h n1 k = h n2 k → n1 = n2) →
    (∀ n k, g (h n k) = Some k) →
    (∀ i n, m !! (h n i) = None → I i → n ∈ S → ✓ (f n i)) →
    (∀ i, (∀ n, n ∈ S → m !! (h n i) = None) → I i → Q (foldr (λ n m, <[h n i := f n i]>m) m S)) →
    m ~~>: Q.
  Proof.
    move=> HND /(pred_infinite_set I (C:=gset K)) HP Hhinj Hgh ? HQ.
    apply cmra_total_updateP. intros n mf Hm.
    destruct (HP (set_omap g (dom (m ⋅ mf)))) as [i [Hi1 Hi2]].
    assert (∀ n, n ∈ S → m !! (h n i) = None).
    { intros n' Hn'. rewrite -not_elem_of_dom.
      rewrite dom_op set_omap_union not_elem_of_union in Hi2.
      destruct Hi2 as [Hi2 _]. intros ?; eapply Hi2, elem_of_set_omap_2; eauto. }
    eexists; split; first by apply HQ.
    match goal with
      |- ✓{n} ?A => cut (dom A = list_to_set ((λ n, h n i) <$> S) ∪ dom (m ⋅ mf) ∧ ✓{n} A)
    end; first tauto.
    clear HQ.
    induction S as [|n' S IHS]; simpl.
    { split; last done. set_solver. }
    destruct IHS as [IHS1 IHS2].
    { by inversion HND. }
    { set_solver. }
    { set_solver. }
    assert ((foldr (λ n' m', <[h n' i:=f n' i]> m') m S ⋅ mf) !! h n' i = None) as Hnin.
    { apply not_elem_of_dom; rewrite IHS1.
      apply not_elem_of_union; split.
      - inversion HND; simplify_eq; set_solver.
      - intros ?; apply Hi2. eapply elem_of_set_omap_2; first eassumption.
        rewrite Hgh //. }
    assert (foldr (λ n' m', <[h n' i:=f n' i]> m') m S !! h n' i = None).
    { rewrite lookup_op in Hnin.
      match type of Hnin with ?A ⋅ ?B = _ => destruct A; destruct B; done end. }
    split.
    - clear -IHS1; rewrite !dom_op dom_insert_L; rewrite !dom_op in IHS1; set_solver.
    - rewrite insert_singleton_op //.
      rewrite -assoc -insert_singleton_op; last done.
      apply insert_validN; [apply cmra_valid_validN|]; [set_solver|auto].
  Qed.
End freshness.

Definition mcname := positive.

Definition push_mcname (μ : mcname) (γ : gname) : gname := inject_positive_pair μ γ.

Lemma push_mcname_inj μ γ μ' γ' : push_mcname μ γ = push_mcname μ' γ' → μ = μ' ∧ γ =γ'.
Proof. apply inject_positive_pair_inj. Qed.

Definition pop_mcname (γ : gname) : option gname :=
  option_map (λ mi, mi.2) (project_positive_pair γ).

Definition mcname_of (γ : gname) : option mcname :=
  option_map (λ mi, mi.1) (project_positive_pair γ).

Lemma mcname_of_is_Some_pop γ μ : mcname_of γ = Some μ → is_Some (pop_mcname γ).
Proof.
  rewrite /is_Some /mcname_of /pop_mcname.
  destruct project_positive_pair; simpl; firstorder eauto.
Qed.

Lemma pop_mcname_is_Some_mcname_of γ γ' : pop_mcname γ = Some γ' → is_Some (mcname_of γ).
Proof.
  rewrite /is_Some /mcname_of /pop_mcname.
  destruct project_positive_pair; simpl; firstorder eauto.
Qed.

Lemma mcname_of_push_mcname μ γ : mcname_of (push_mcname μ γ) = Some μ.
Proof. rewrite /mcname_of /push_mcname project_inject_positive_pair //. Qed.
  
Lemma pop_push_mcname γ μ : pop_mcname (push_mcname μ γ) = Some γ.
Proof. rewrite /push_mcname /pop_mcname project_inject_positive_pair //. Qed.

Lemma push_pop_mcname γ γ' μ : pop_mcname γ = Some γ' → mcname_of γ = Some μ → push_mcname μ γ' = γ.
Proof.
  rewrite /push_mcname /pop_mcname /mcname_of.
  destruct project_positive_pair as [[μ' γ'']|] eqn:Hdec; last done.
  intros; simplify_eq/=.
  pose proof (project_inject_positive_pair μ γ') as Hpi.
  eapply project_positive_pair_inj; eauto.
Qed.

Lemma push_pop_mcname_ext γ γ' δ μ :
  pop_mcname γ = Some δ → mcname_of γ = Some μ →
  pop_mcname γ' = Some δ → mcname_of γ' = Some μ →
  γ = γ'.
Proof.
  intros.
  erewrite <- (push_pop_mcname γ), <- (push_pop_mcname γ'); eauto.
Qed.

Definition mcrename (μ μ' : mcname) (γ : gname) : option gname :=
  mcname_of γ ≫=
    (λ γμ, if bool_decide (γμ = μ) then
      option_map (λ δ, push_mcname μ' δ) (pop_mcname γ)
      else None).

Lemma mcrename_spec μ μ' γ δ :
  mcrename μ μ' γ = Some δ ↔
  mcname_of γ = Some μ ∧ ∃ ξ, pop_mcname γ = Some ξ ∧ δ = push_mcname μ' ξ.
Proof.
  rewrite /mcrename.
  destruct (mcname_of γ) as [ξ|] eqn:Hξ; simpl; last first.
  { split; first done. intros []; done. }
  pose proof (mcname_of_is_Some_pop _ _ Hξ) as [w Hw].
  rewrite Hw.
  rewrite -decide_bool_decide.
  destruct decide; simplify_eq/=.
  - split.
    + intros; simplify_eq; eauto.
    + intros [_ (?&?&?)]; simplify_eq; done.
  - split; first done.
    intros []; simplify_eq.
Qed.

Lemma mcrename_inj μ μ' γ γ' δ : mcrename μ μ' γ = Some δ → mcrename μ μ' γ' = Some δ → γ = γ'.
Proof.
  intros [? (?&?&?)]%mcrename_spec [? (?&?&?)]%mcrename_spec; simplify_eq.
  match goal with
  | H : _ |- _ => apply push_mcname_inj in H as []; subst
  end.
  erewrite <- (push_pop_mcname γ); [|eauto|eauto].
  erewrite <- (push_pop_mcname γ'); [|eauto|eauto].
  done.
Qed.

Lemma mcrename_inv μ μ' γ δ : mcrename μ μ' γ = Some δ → mcrename μ' μ δ = Some γ.
Proof.
  intros [? (?&?&?)]%mcrename_spec; simplify_eq.
  apply mcrename_spec.
  split; first apply mcname_of_push_mcname.
  rewrite pop_push_mcname.
  eexists; split; first done.
  erewrite push_pop_mcname; eauto.
Qed.

Lemma mcrename_inv' μ μ' γ : mcrename μ μ' γ = None → ∀ δ, mcrename μ' μ δ ≠ Some γ.
Proof. intros ???%mcrename_inv; simplify_eq. Qed.

Lemma mcrename_to_push μ μ' δ γ : mcrename μ μ' δ = Some (push_mcname μ' γ) → δ = push_mcname μ γ.
Proof.
  intros (?&?&?&[]%push_mcname_inj)%mcrename_spec; simplify_eq.
  symmetry; apply push_pop_mcname; done.
Qed.

Lemma mcrename_of_push μ μ' γ : mcrename μ μ' (push_mcname μ γ) = Some (push_mcname μ' γ).
Proof.
  apply mcrename_spec.
  split; first by apply mcname_of_push_mcname.
  eexists _; split; first by apply pop_push_mcname. done.
Qed.

Lemma mcrename_same μ γ δ : mcrename μ μ δ = Some γ → γ = δ.
Proof.
  intros (?&?&?&?)%mcrename_spec; simplify_eq.
  eapply push_pop_mcname_ext; eauto using pop_push_mcname, mcname_of_push_mcname.
Qed.

Lemma mcrename_None μ μ' γ : mcrename μ μ' γ = None → mcname_of γ ≠ Some μ.
Proof.
  intros Hmcr Hmco.
  pose proof Hmco as [δ ?]%mcname_of_is_Some_pop.
  erewrite <- (push_pop_mcname γ) in Hmcr; eauto.
  rewrite mcrename_of_push in Hmcr; done.
Qed.

Lemma mcrename_has_mcname μ ν γ δ :
  mcrename μ ν γ = Some δ → mcname_of γ = Some μ.
Proof.
  intros (?&?&?&?)%mcrename_spec; simplify_eq; done.
Qed.

Lemma mcrename_has_mcname' μ ν γ δ :
  mcrename μ ν γ = Some δ → mcname_of δ = Some ν.
Proof.
  intros (?&?&?&?)%mcrename_spec; simplify_eq.
  rewrite mcname_of_push_mcname //.
Qed.

Lemma mcrename_id μ γ : mcname_of γ = Some μ → mcrename μ μ γ = Some γ.
Proof.
  intros Hγ; apply mcrename_spec; split; first done.
  pose proof Hγ as [? ?]%mcname_of_is_Some_pop.
  eexists _; split; first done.
  erewrite push_pop_mcname; eauto.
Qed.

Lemma mcrename_trans μ ν ρ γ δ ξ :
  mcrename μ ν γ = Some δ → mcrename ν ρ δ = Some ξ → mcrename μ ρ γ = Some ξ.
Proof.
  intros (?&?&?&?)%mcrename_spec (?&?&Hpp&?)%mcrename_spec; simplify_eq.
  rewrite pop_push_mcname in Hpp; simplify_eq.
  apply mcrename_spec; eauto.
Qed.

Lemma mcrename_retract μ ν ρ γ δ :
  mcrename μ ν γ = Some δ → ∃ ξ, mcrename ρ ν ξ = Some δ.
Proof.
  intros (?&ξ&?&?)%mcrename_spec; simplify_eq.
  exists (push_mcname ρ ξ); apply mcrename_spec.
  split; first by apply mcname_of_push_mcname.
  eexists; split; last done.
  by rewrite pop_push_mcname.
Qed.

Lemma mcrename_breadth μ ν ρ γ δ :
  mcrename μ ν γ = Some δ → ∃ ξ, mcrename μ ρ γ = Some ξ.
Proof.
  intros (?&?&?&?)%mcrename_spec; simplify_eq.
  eexists _; apply mcrename_spec; eauto.
Qed.

Lemma mcrename_breadth' μ ν ρ γ :
  mcrename μ ν γ = None → mcrename μ ρ γ = None.
Proof.
  destruct (mcrename μ ρ γ) eqn:Hγ; last done.
  apply mcrename_spec in Hγ as (?&δ&?&?); simplify_eq.
  assert (mcrename μ ν γ = Some (push_mcname ν δ)) by by apply mcrename_spec; eauto.
  intros; simplify_eq.
Qed.

Definition mcname_of_set (γ : gname) : gset mcname :=
  match mcname_of γ with Some μ => {[μ]} | None => ∅ end.

Lemma elem_of_mcname_of_set μ γ :
  μ ∈ mcname_of_set γ ↔ mcname_of γ = Some μ.
Proof. rewrite /mcname_of_set; destruct mcname_of; set_solver. Qed.

Definition mcnames_of (γs : gset gname) : gset mcname :=
  set_fold (λ γ μs, mcname_of_set γ ∪ μs) ∅ γs.

Lemma mcnames_of_empty : mcnames_of ∅ = ∅.
Proof. by rewrite /mcnames_of set_fold_empty. Qed.

Lemma mcnames_of_singleton γ : mcnames_of {[γ]} = mcname_of_set γ.
Proof. rewrite /mcnames_of set_fold_singleton; set_solver. Qed.

Lemma mcnames_of_union P Q :
  mcnames_of (P ∪ Q) = mcnames_of P ∪ mcnames_of Q.
Proof.
  rewrite /mcnames_of (set_fold_union_strong (=));
    [|set_solver|set_solver].
  generalize (set_fold (λ p mis, mcname_of_set p ∪ mis) ∅ P); intros R.
  replace R with (R ∪ ∅) by set_solver.
  rewrite (set_fold_comm_acc _ (λ Q, R ∪ Q)); set_solver.
Qed.

Lemma elem_of_mcnames_of γs μ :
  μ ∈ mcnames_of γs ↔ ∃ γ, mcname_of γ = Some μ ∧ γ ∈ γs.
Proof.
  revert μ; induction γs as [|γ γs Hγ IHγs] using set_ind_L; intros μ.
  { rewrite /mcnames_of set_fold_empty; set_solver. }
  rewrite mcnames_of_union mcnames_of_singleton
    elem_of_union elem_of_mcname_of_set; set_solver.
Qed.

Lemma mcnames_of_mono γs γs' : γs ⊆ γs' → mcnames_of γs ⊆ mcnames_of γs'.
Proof. intros Hsb μ; rewrite !elem_of_mcnames_of; set_solver. Qed.

Lemma elem_of_push_mcname μ γ (γs : gset gname) :
  push_mcname μ γ ∈ γs → ∃ γ', mcname_of γ' = Some μ ∧ γ' ∈ γs.
Proof. intros ?; exists (push_mcname μ γ); rewrite mcname_of_push_mcname; done. Qed.

Definition mcnames_of_iResUR `(x : !iResUR Σ) : gset mcname :=
  mcnames_of (foldr (∪) ∅ ((λ i, dom (x i)) <$> enum (fin (gFunctors_len Σ)))).

Lemma mcnames_of_iResUR_include_dom `(x : !iResUR Σ) i :
  mcnames_of (dom (x i)) ⊆ mcnames_of_iResUR x.
Proof.
  apply mcnames_of_mono.
  rewrite /mcnames_of_iResUR.
  pose proof (elem_of_enum i) as
    (l&l'&->)%(list_elem_of_fmap_2 (λ i, dom (x i)))%list_elem_of_split.
  replace (foldr union ∅ (l ++ dom (x i) :: l')) with
    (foldr union ∅ (dom (x i) :: l ++ l')); first set_solver.
  apply (foldr_permutation (=) union).
  - repeat intros ?; set_solver.
  - repeat intros ?; set_solver.
  - apply Permutation_middle.
Qed.

Definition fresh_mcname `(x : !iResUR Σ) (M : gset mcname) : mcname :=
  fresh (mcnames_of_iResUR x ∪ M).

Lemma fresh_mcname_is_fresh `(x : !iResUR Σ) M :
  fresh_mcname x M ∉ (mcnames_of_iResUR x ∪ M).
Proof. apply is_fresh. Qed.

Definition mcrename_keys {A} (μ μ' : mcname) (g : gmap gname A) : gmap gname A :=
  list_to_map (omap (λ γa, option_map (λ δ, (δ, γa.2)) (mcrename μ μ' γa.1)) (map_to_list g)).

Lemma in_mcrename_keys {A} μ μ' (g : gmap gname A) δ a :
  mcrename_keys μ μ' g !! δ = Some a ↔ ∃ γ, mcrename μ μ' γ = Some δ ∧ g !! γ = Some a.
Proof.
  rewrite /mcrename_keys.
  rewrite -elem_of_list_to_map; last first.
  { apply NoDup_fmap_fst.
    - intros ???.
      rewrite !list_elem_of_omap.
      intros ([γ b]& Hγ &?) ([γ' b']& Hγ' &?); simpl in *.
      destruct (mcrename μ μ' γ) as [ξ|] eqn:Heqξ; last done.
      apply mcrename_spec in Heqξ as [? (?&?&?)]; simplify_eq.
      destruct (mcrename μ μ' γ') as [ξ'|] eqn:Heqξ'; last done.
      apply mcrename_spec in Heqξ' as [? (?&?&?)]; simplify_eq.
      simplify_eq/=.
      match goal with
      | H : _ |- _ => apply push_mcname_inj in H as []; subst
      end.
      assert (γ = γ'); subst.
      { eapply push_pop_mcname_ext; eauto. }
      apply elem_of_map_to_list in Hγ.
      apply elem_of_map_to_list in Hγ'.
      simplify_eq; done.
    - apply NoDup_omap; last first.
      { apply NoDup_map_to_list. }
      intros [γ b] [γ' b'] ???; simpl in *.
      destruct (mcrename μ μ' γ) as [ξ|] eqn:Heqξ; last done.
      apply mcrename_spec in Heqξ as [? (?&?&?)]; simplify_eq.
      destruct (mcrename μ μ' γ') as [ξ'|] eqn:Heqξ'; last done.
      apply mcrename_spec in Heqξ' as [? (?&?&?)]; simplify_eq.
      simplify_eq/=.
      match goal with
      | H : _ |- _ => apply push_mcname_inj in H as []; subst
      end.
      assert (γ = γ'); subst.
      { eapply push_pop_mcname_ext; eauto. }
      done. }
  rewrite list_elem_of_omap.
  split.
  - intros ([γ b]& Hγ &?); simpl in *.
    destruct (mcrename μ μ' γ) as [ξ|] eqn:Heqξ; last done.
    apply elem_of_map_to_list in Hγ.
    simplify_eq/=; eauto.
  - intros (γ & Hγ &?); simpl in *.
    exists (γ, a); split; first by apply elem_of_map_to_list.
    rewrite Hγ //=.
Qed.

Lemma not_in_mcrename_keys {A} μ μ' (g : gmap gname A) δ :
  mcrename_keys μ μ' g !! δ = None ↔
  (∀ γ, mcrename μ μ' γ ≠ Some δ ∨ g !! γ = None).
Proof.
  rewrite /mcrename_keys; split.
  - intros Hδ%not_elem_of_list_to_map_2 γ.
    rewrite list_fmap_omap list_elem_of_omap in Hδ.
    destruct (decide (mcrename μ μ' γ = Some δ)) as [Hγδ|]; last by left.
    destruct (g !! γ) eqn:Hgγ; last by right.
    exfalso; apply Hδ.
    exists (γ, a).
    split; first by apply elem_of_map_to_list.
    rewrite /= Hγδ //=.
  - intros Hn.
    match goal with
    |- ?A = _ => destruct A as [a|] eqn:Ha; last done
    end.
    apply elem_of_list_to_map_2 in Ha.
    rewrite list_elem_of_omap in Ha.
    destruct Ha as ([γ a'] & Hγa'%elem_of_map_to_list & Hδa'); simpl in *.
    specialize (Hn γ).
    destruct (mcrename μ μ' γ); last done.
    destruct Hn; simplify_eq/=.
Qed.

Lemma not_in_mcrename_keys' {A} μ μ' (g : gmap gname A) δ γ :
  mcrename_keys μ μ' g !! δ = None → mcrename μ μ' γ = Some δ → g !! γ = None.
Proof. intros Hδ ?; eapply not_in_mcrename_keys in Hδ as []; done. Qed.

Definition remove_keys_in_mc {A} (μ : mcname) (g : gmap gname A) : gmap gname A :=
  list_to_map (omap (λ γa, if bool_decide (mcname_of γa.1 = Some μ) then None else Some γa) (map_to_list g)).

Lemma in_remove_keys_in_mc {A} μ (g : gmap gname A) γ a :
  remove_keys_in_mc μ g !! γ = Some a ↔
  mcname_of γ ≠ Some μ ∧ g !! γ = Some a.
Proof.
  rewrite /remove_keys_in_mc.
  rewrite -elem_of_list_to_map; last first.
  { apply NoDup_fmap_fst.
    - intros ???.
      rewrite !list_elem_of_omap.
      intros ([δ b]& Hδ & Hδlu) ([δ' b']& Hδ' & Hδ'lu); simpl in *.
      rewrite -decide_bool_decide in Hδlu; destruct decide; first done.
      simplify_eq.
      rewrite -decide_bool_decide in Hδ'lu; destruct decide; first done.
      simplify_eq.
      apply elem_of_map_to_list in Hδ.
      apply elem_of_map_to_list in Hδ'.
      simplify_eq; done.
    - apply NoDup_omap; last first.
      { apply NoDup_map_to_list. }
      intros [δ b] [δ' b'] ? Hlu Hlu'; simpl in *.
      rewrite -decide_bool_decide in Hlu; destruct decide; first done.
      simplify_eq.
      rewrite -decide_bool_decide in Hlu'; destruct decide; first done.
      simplify_eq; done. }
  rewrite list_elem_of_omap.
  split.
  - intros ([δ b]& Hδ & Hlu); simpl in *.
    rewrite -decide_bool_decide in Hlu; destruct decide; first done.
    simplify_eq.
    apply elem_of_map_to_list in Hδ; done.
  - intros []; simpl in *.
    exists (γ, a); split; first by apply elem_of_map_to_list.
    rewrite -decide_bool_decide; destruct decide; done.
Qed.

Lemma not_in_remove_keys_in_mc {A} μ (g : gmap gname A) γ :
  remove_keys_in_mc μ g !! γ = None ↔
  mcname_of γ = Some μ ∨ g !! γ = None.
Proof.
  rewrite /remove_keys_in_mc; split.
  - intros Hδ%not_elem_of_list_to_map_2.
    rewrite list_fmap_omap list_elem_of_omap in Hδ.
    destruct (decide (mcname_of γ = Some μ)) as [Hγμ|]; first by left.
    destruct (g !! γ) eqn:Hgγ; last by right.
    exfalso; apply Hδ.
    exists (γ, a).
    split; first by apply elem_of_map_to_list.
    rewrite /= bool_decide_eq_false_2; done.
  - intros Hn.
    match goal with
    |- ?A = _ => destruct A as [a|] eqn:Ha; last done
    end.
    apply elem_of_list_to_map_2 in Ha.
    rewrite list_elem_of_omap in Ha.
    destruct Ha as ([δ a'] & Hδa'%elem_of_map_to_list & Hδγ'); simpl in *.
    rewrite -decide_bool_decide in Hδγ'; destruct decide; first done.
    simplify_eq.
    destruct Hn; simplify_eq.
Qed.

Lemma mcrename_keys_comp {A} μ ν ρ (g : gmap gname A) :
  mcrename_keys ν ρ (mcrename_keys μ ν g) = mcrename_keys μ ρ g.
Proof.
  apply map_eq; intros γ.
  destruct (mcrename_keys ν ρ (mcrename_keys μ ν g) !! γ) as [a|] eqn:Hlu; last first.
  - symmetry; apply not_in_mcrename_keys; intros δ.
    destruct (mcrename μ ρ δ) as [ξ|] eqn:Hξ; last by left.
    destruct (decide (ξ = γ)) as [->|Hneq];
     last by left; intros ?; apply Hneq; simplify_eq.
    right.
    rewrite not_in_mcrename_keys in Hlu.
    pose proof Hξ as [k Hk]%(mcrename_retract _ _ ν).
    specialize (Hlu k) as [|Hlu]; first by simplify_eq.
    apply mcrename_inv in Hk.
    pose proof (mcrename_trans _ _ _ _ _ _ Hξ Hk).
    rewrite not_in_mcrename_keys in Hlu.
    specialize (Hlu δ) as [|]; last done;
    by simplify_eq.
  - apply in_mcrename_keys in Hlu as (δ & Hδ & Hlu).
    apply in_mcrename_keys in Hlu as (ξ & Hξ & Hlu).
    pose proof (mcrename_trans _ _ _ _ _ _ Hξ Hδ).
    symmetry; apply in_mcrename_keys; eauto.
Qed.

Lemma remove_keys_in_mc_idemp {A} μ (g : gmap gname A) :
remove_keys_in_mc μ (remove_keys_in_mc μ g) = remove_keys_in_mc μ g.
Proof.
  apply map_eq; intros γ.
  destruct (remove_keys_in_mc μ (remove_keys_in_mc μ g) !! γ) as [a|] eqn:Hlu; last first.
  - apply not_in_remove_keys_in_mc in Hlu as [|Hlu].
    { symmetry; apply not_in_remove_keys_in_mc; by left. }
    apply not_in_remove_keys_in_mc in Hlu as [|Hlu].
    { symmetry; apply not_in_remove_keys_in_mc; by left. }
    symmetry; apply not_in_remove_keys_in_mc; by right.
  - apply in_remove_keys_in_mc in Hlu as (? & <-); done.
Qed.

Lemma remove_keys_in_mc_mcrename_keys_empty {A} μ ν (g : gmap gname A) :
  remove_keys_in_mc ν (mcrename_keys μ ν g) = ∅.
Proof.
  apply map_eq; intros γ; rewrite lookup_empty.
  apply not_in_remove_keys_in_mc.
  destruct (decide (mcname_of γ = Some ν)); first by left.
  right.
  apply not_in_mcrename_keys; intros δ.
  left; intros ?%mcrename_has_mcname'; done.
Qed.

Lemma remove_keys_in_mc_mcrename_keys_id {A} μ ν ρ (g : gmap gname A) :
  ρ ≠ ν → remove_keys_in_mc ρ (mcrename_keys μ ν g) = (mcrename_keys μ ν g).
Proof.
  intros Hneq; apply map_eq; intros γ.
  destruct (mcrename_keys μ ν g !! γ) eqn:Heqm.
  - apply in_mcrename_keys in Heqm as (?& Hmcr &?).
    pose proof Hmcr as ?%mcrename_has_mcname'.
    apply in_remove_keys_in_mc; split; first by intros ?; simplify_eq.
    apply in_mcrename_keys; eauto.
  - apply not_in_remove_keys_in_mc.
    destruct (decide (mcname_of γ = Some ρ)); [by left|by right].
Qed.

Lemma mcrename_keys_remove_keys_in_mc_empty {A} μ ν (g : gmap gname A) :
  mcrename_keys μ ν (remove_keys_in_mc μ g) = ∅.
Proof.
  apply map_eq; intros γ; rewrite lookup_empty.
  apply not_in_mcrename_keys; intros δ.
  destruct (decide (mcrename μ ν δ = Some γ)) as [?%mcrename_has_mcname|];
    last by left.
  right.
  apply not_in_remove_keys_in_mc; by left.
Qed.

Lemma mcrename_keys_remove_keys_in_mc_id {A} μ ν ρ (g : gmap gname A) :
  ρ ≠ μ → mcrename_keys μ ν (remove_keys_in_mc ρ g) = mcrename_keys μ ν g.
Proof.
  intros Hneq; apply map_eq; intros γ.
  destruct (mcrename_keys μ ν g !! γ) eqn:Heqm.
  - apply in_mcrename_keys in Heqm as (δ & Hmcr &?).
    pose proof Hmcr as ?%mcrename_has_mcname.
    apply in_mcrename_keys.
    eexists; split; first done.
    apply in_remove_keys_in_mc; split; last done.
    by intros ?; simplify_eq.
  - apply not_in_mcrename_keys; intros δ.
    destruct (decide (mcrename μ ν δ = Some γ)); last by left.
    right.
    rewrite not_in_mcrename_keys in Heqm; destruct (Heqm δ); first done.
    apply not_in_remove_keys_in_mc; auto.
Qed.

Definition rename_mc_iResUR {Σ} μ μ' (x : iResUR Σ) : iResUR Σ :=
  λ i, mcrename_keys μ μ' (x i).

Definition remove_mc_iResUR {Σ} μ (x : iResUR Σ) : iResUR Σ :=
  λ i, remove_keys_in_mc μ (x i).

Lemma rename_mc_iResUR_comp {Σ} μ ν ρ (x : iResUR Σ) :
  rename_mc_iResUR ν ρ (rename_mc_iResUR μ ν x) ≡ rename_mc_iResUR μ ρ x.
Proof. intros i; rewrite /rename_mc_iResUR mcrename_keys_comp //. Qed.

Lemma remove_mc_iResUR_idemp {Σ} μ (x : iResUR Σ) :
  remove_mc_iResUR μ (remove_mc_iResUR μ x) ≡ remove_mc_iResUR μ x.
Proof. intros i; rewrite /remove_mc_iResUR remove_keys_in_mc_idemp //. Qed.

Lemma remove_mc_rename_mc_iResUR_emp {Σ} μ ν (x : iResUR Σ) :
  remove_mc_iResUR ν (rename_mc_iResUR μ ν x) ≡ ε.
Proof.
  intros i; rewrite /remove_mc_iResUR /rename_mc_iResUR
    remove_keys_in_mc_mcrename_keys_empty //.
Qed.

Lemma remove_mc_rename_mc_iResUR_id {Σ} μ ν ρ (x : iResUR Σ) :
  ρ ≠ ν → remove_mc_iResUR ρ (rename_mc_iResUR μ ν x) ≡ (rename_mc_iResUR μ ν x).
Proof.
  intros ? i; rewrite /remove_mc_iResUR /rename_mc_iResUR
    remove_keys_in_mc_mcrename_keys_id //.
Qed.

Lemma rename_mc_remove_mc_iResUR_empty {Σ} μ ν (x : iResUR Σ) :
  rename_mc_iResUR μ ν (remove_mc_iResUR μ x) ≡ ε.
Proof.
  intros i; rewrite /remove_mc_iResUR /rename_mc_iResUR
    mcrename_keys_remove_keys_in_mc_empty //.
Qed.

Lemma rename_mc_remove_mc_iResUR_id {Σ} μ ν ρ (x : iResUR Σ) :
  ρ ≠ μ → rename_mc_iResUR μ ν (remove_mc_iResUR ρ x) ≡ rename_mc_iResUR μ ν x.
Proof.
  intros ? i; rewrite /remove_mc_iResUR /rename_mc_iResUR
    mcrename_keys_remove_keys_in_mc_id //.
Qed.

Lemma rename_mc_remove_mc_iResUR {Σ} μ (x : iResUR Σ) :
  x ≡ rename_mc_iResUR μ μ x ⋅ remove_mc_iResUR μ x.
Proof.
  rewrite /rename_mc_iResUR /remove_mc_iResUR.
  intros i γ.
  rewrite !discrete_fun_lookup_op !lookup_op.
  destruct (decide (mcname_of γ = Some μ)) as [Heq|Hneq].
  - assert (remove_keys_in_mc μ (x i) !! γ = None) as Hrm.
    { apply not_in_remove_keys_in_mc; by left. }
    rewrite Hrm right_id.
    destruct (x i !! γ) as [a|] eqn:Hlu.
    + rewrite Hlu.
      assert (mcrename_keys μ μ (x i) !! γ = Some a) as Hren;
        last by rewrite Hren.
      apply in_mcrename_keys; eauto.
      eexists; split; first by apply mcrename_id. done.
    + rewrite Hlu.
      assert (mcrename_keys μ μ (x i) !! γ = None) as Hren;
        last by rewrite Hren.
      apply not_in_mcrename_keys.
      intros δ.
      destruct (decide (mcrename μ μ δ = Some γ)) as [Hren|]; last by left.
      pose proof Hren as ?%mcrename_has_mcname.
      rewrite mcrename_id in Hren; last done; simplify_eq.
      by right.
  - assert (mcrename_keys μ μ (x i) !! γ = None) as Hren.
    { apply not_in_mcrename_keys.
      intros δ; left; intros ?%mcrename_has_mcname'; done. }
    rewrite Hren left_id.
    destruct (x i !! γ) as [a|] eqn:Hlu; rewrite Hlu.
    + assert (remove_keys_in_mc μ (x i) !! γ = Some a) as Hrm.
      { apply in_remove_keys_in_mc; done. }
      rewrite Hrm; done.
    + assert (remove_keys_in_mc μ (x i) !! γ = None) as Hrm.
      { apply not_in_remove_keys_in_mc; by right. }
      rewrite Hrm; done.
Qed.

Lemma rename_mc_iResUR_included {Σ} μ (x : iResUR Σ) : rename_mc_iResUR μ μ x ≼ x.
Proof. eexists; apply rename_mc_remove_mc_iResUR. Qed.
Lemma rename_mc_iResUR_includedN {Σ} μ (x : iResUR Σ) n : rename_mc_iResUR μ μ x ≼{n} x.
Proof. apply cmra_included_includedN, rename_mc_iResUR_included. Qed.

Lemma remove_mc_iResUR_included {Σ} μ (x : iResUR Σ) : remove_mc_iResUR μ x ≼ x.
Proof. eexists; rewrite comm; apply rename_mc_remove_mc_iResUR. Qed.
Lemma remove_mc_iResUR_includedN {Σ} μ (x : iResUR Σ) n : remove_mc_iResUR μ x ≼{n} x.
Proof. apply cmra_included_includedN, remove_mc_iResUR_included. Qed.

Lemma rename_mc_iResUR_core {Σ} μ ν (x : iResUR Σ) :
  core (rename_mc_iResUR μ ν x) ≡ rename_mc_iResUR μ ν (core x).
Proof.
  intros i γ; rewrite /rename_mc_iResUR !discrete_fun_lookup_core lookup_core.
  destruct (mcrename_keys μ ν (core (x i)) !! γ) eqn:Heqm; rewrite Heqm.
  - apply in_mcrename_keys in Heqm as (δ & Hδr & Hδlu).
    destruct (mcrename_keys μ ν (x i) !! γ) eqn:Heqm'.
    + apply in_mcrename_keys in Heqm' as (ξ & Hξr & Hξlu).
      assert (δ = ξ); subst.
      { eapply mcrename_inj; eauto. }
      rewrite lookup_core Hξlu in Hδlu.
      rewrite Hδlu //.
    + rewrite not_in_mcrename_keys in Heqm'.
      specialize (Heqm' δ) as [|Heqm']; first done.
      rewrite lookup_core Heqm' in Hδlu; done.
  - destruct (mcrename_keys μ ν (x i) !! γ) eqn:Heqm'; last done.
    apply in_mcrename_keys in Heqm' as (ξ & Hξr & Hξlu).
    rewrite not_in_mcrename_keys in Heqm.
    specialize (Heqm ξ) as [|Heqm]; first done.
    rewrite lookup_core Hξlu in Heqm; rewrite Heqm //.
Qed.

Lemma remove_mc_iResUR_core {Σ} μ (x : iResUR Σ) :
  core (remove_mc_iResUR μ x) ≡ remove_mc_iResUR μ (core x).
Proof.
  intros i γ; rewrite /remove_mc_iResUR !discrete_fun_lookup_core lookup_core.
  destruct (remove_keys_in_mc μ (core (x i)) !! γ) eqn:Heqm; rewrite Heqm.
  - apply in_remove_keys_in_mc in Heqm as [? Hlu].
    destruct (remove_keys_in_mc μ (x i) !! γ) eqn:Heqm'.
    + apply in_remove_keys_in_mc in Heqm' as [? Hlu'].
      rewrite lookup_core Hlu' in Hlu.
      rewrite Hlu //.
    + rewrite lookup_core in Hlu.
      rewrite not_in_remove_keys_in_mc in Heqm'.
      destruct Heqm' as [|Heqm]; first done.
      rewrite Heqm in Hlu; rewrite Hlu //.
  - destruct (remove_keys_in_mc μ (x i) !! γ) eqn:Heqm'; last done.
    apply in_remove_keys_in_mc in Heqm' as [? Heqm'].
    rewrite not_in_remove_keys_in_mc in Heqm.
    destruct Heqm as [|Heqm]; first done.
    rewrite lookup_core Heqm' in Heqm; rewrite Heqm //.
Qed.
    
Global Instance rename_mc_iResUR_ne {Σ} μ μ' : NonExpansive (@rename_mc_iResUR Σ μ μ').
Proof.
  intros n x y Heq i γ.
  destruct (mcrename_keys μ μ' (x i) !! γ) as [m|] eqn:Heqm;
    destruct (mcrename_keys μ μ' (y i) !! γ) as [m'|] eqn:Heqm';
    rewrite Heqm Heqm' /=; last done.
  - apply in_mcrename_keys in Heqm as (δ & ? & Hδ).
    apply in_mcrename_keys in Heqm' as (δ' & ? & Hδ').
    assert (δ = δ'); subst.
    { eapply mcrename_inj; eauto. }
    specialize (Heq i δ').
    rewrite Hδ Hδ' in Heq; done.
  - apply in_mcrename_keys in Heqm as (δ & ? & Hδ).
    eapply not_in_mcrename_keys' in Heqm'; last by eauto.
    specialize (Heq i δ).
    rewrite Hδ Heqm' in Heq; done.
  - apply in_mcrename_keys in Heqm' as (δ' & ? & Hδ').
    eapply not_in_mcrename_keys' in Heqm; last by eauto.
    specialize (Heq i δ').
    rewrite Heqm Hδ' in Heq; done.
Qed.

Global Instance rename_mc_iResUR_proper {Σ} μ μ' : Proper ((≡) ==> (≡)) (@rename_mc_iResUR Σ μ μ').
Proof. apply ne_proper; apply _. Qed.

Global Instance remove_mc_iResUR_ne {Σ} μ : NonExpansive (@remove_mc_iResUR Σ μ).
Proof.
  intros n x y Heq i γ.
  destruct (remove_keys_in_mc μ (x i) !! γ) as [m|] eqn:Heqm;
    destruct (remove_keys_in_mc μ (y i) !! γ) as [m'|] eqn:Heqm';
    rewrite Heqm Heqm' /=; last done.
  - apply in_remove_keys_in_mc in Heqm as (? & <-).
    apply in_remove_keys_in_mc in Heqm' as (? & <-).
    apply Heq.
  - apply in_remove_keys_in_mc in Heqm as (? & <-).
    apply not_in_remove_keys_in_mc in Heqm' as [| <-]; first done.
    apply Heq.
  - apply in_remove_keys_in_mc in Heqm' as (? & <-).
    apply not_in_remove_keys_in_mc in Heqm as [| <-]; first done.
    apply Heq.
Qed.

Global Instance remove_mc_iResUR_proper {Σ} μ : Proper ((≡) ==> (≡)) (@remove_mc_iResUR Σ μ).
Proof. apply ne_proper; apply _. Qed.

Lemma rename_mc_iResUR_op {Σ} μ μ' (x x' : iResUR Σ) :
  rename_mc_iResUR μ μ' (x ⋅ x') ≡ rename_mc_iResUR μ μ' x ⋅ rename_mc_iResUR μ μ' x'.
Proof.
  intros i γ; rewrite /rename_mc_iResUR.
  rewrite !discrete_fun_lookup_op !lookup_op.
  destruct (mcrename_keys μ μ' (x i) !! γ) as [m|] eqn:Heqm;
    destruct (mcrename_keys μ μ' (x' i) !! γ) as [m'|] eqn:Heqm'.
  - apply in_mcrename_keys in Heqm as (δ & ? & Hδ).
    apply in_mcrename_keys in Heqm' as (δ' & ? & Hδ').
    assert (δ = δ'); subst.
    { eapply mcrename_inj; eauto. }
    destruct (mcrename_keys μ μ' (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw; last first.
    { eapply not_in_mcrename_keys' in Heqw; last by eauto.
      rewrite lookup_op Hδ Hδ' in Heqw; done. }
    rewrite Heqw.
    apply in_mcrename_keys in Heqw as (ξ & ? & Hξ).
    assert (ξ = δ'); subst.
    { eapply mcrename_inj; eauto. }
    rewrite lookup_op Hδ Hδ' -Some_op in Hξ; simplify_eq/=.
    rewrite Some_op //.
  - apply in_mcrename_keys in Heqm as (δ & ? & Hδ).
    eapply not_in_mcrename_keys' in Heqm'; last by eauto.
    destruct (mcrename_keys μ μ' (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw; last first.
    { eapply not_in_mcrename_keys' in Heqw; last by eauto.
      rewrite lookup_op Hδ Heqm' in Heqw; done. }
    rewrite Heqw.
    apply in_mcrename_keys in Heqw as (ξ & ? & Hξ).
    assert (ξ = δ); subst.
    { eapply mcrename_inj; eauto. }
    rewrite lookup_op Hδ Heqm' right_id in Hξ; simplify_eq/=.
    rewrite right_id //.
  - apply in_mcrename_keys in Heqm' as (δ' & ? & Hδ').
    eapply not_in_mcrename_keys' in Heqm; last by eauto.
    destruct (mcrename_keys μ μ' (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw; last first.
    { eapply not_in_mcrename_keys' in Heqw; last by eauto.
      rewrite lookup_op Hδ' Heqm in Heqw; done. }
    rewrite Heqw.
    apply in_mcrename_keys in Heqw as (ξ & ? & Hξ).
    assert (ξ = δ'); subst.
    { eapply mcrename_inj; eauto. }
    rewrite lookup_op Hδ' Heqm left_id in Hξ; simplify_eq/=.
    rewrite left_id //.
  - rewrite left_id.
    destruct (mcrename_keys μ μ' (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw;
      rewrite Heqw; last done.
    apply in_mcrename_keys in Heqw as (ξ & ? & Hξ).
    eapply not_in_mcrename_keys' in Heqm; last done.
    eapply not_in_mcrename_keys' in Heqm'; last done.
    rewrite lookup_op Heqm Heqm' in Hξ; done.
Qed.

Lemma rename_mc_iResUR_op_inv {Σ} μ μ' n (z x y : iResUR Σ) :
  rename_mc_iResUR μ μ' z ≡{n}≡ x ⋅ y →
  ∃ x' y' : iResUR Σ,
    z ≡{n}≡ x' ⋅ y' ∧
    x ≡{n}≡ rename_mc_iResUR μ μ' x' ∧ y ≡{n}≡ rename_mc_iResUR μ μ' y'.
Proof.
  intros Heq; rewrite /rename_mc_iResUR.
  exists (rename_mc_iResUR μ' μ x ⋅ remove_mc_iResUR μ z),
    (rename_mc_iResUR μ' μ y); split_and!.
  - rewrite {1}(rename_mc_remove_mc_iResUR μ z).
    rewrite -(rename_mc_iResUR_comp μ μ' μ z) Heq.
    rewrite rename_mc_iResUR_op.
    rewrite -assoc -(comm (⋅) _ (rename_mc_iResUR μ' μ y)) assoc //.
  - intros i γ; rewrite discrete_fun_lookup_op /rename_mc_iResUR.
    destruct (mcrename_keys μ μ'
      (mcrename_keys μ' μ (x i) ⋅ remove_mc_iResUR μ z i) !! γ) eqn:Heqm;
      rewrite Heqm.
    + apply in_mcrename_keys in Heqm as (δ & Hδr & Heqm).
      pose proof Hδr as ?%mcrename_has_mcname.
      rewrite lookup_op in Heqm. 
      destruct (remove_mc_iResUR μ z i !! δ) eqn:Heqm'.
      { apply in_remove_keys_in_mc in Heqm' as []; done. }
      rewrite Heqm' right_id in Heqm.
      apply in_mcrename_keys in Heqm as (ξ &?& Hlu).
      assert (ξ = γ); subst; last by rewrite Hlu.
      eapply mcrename_inj; first eassumption.
      by apply mcrename_inv.
    + destruct (mcrename μ' μ γ) as [δ|] eqn:Hδ.
      * rewrite not_in_mcrename_keys in Heqm.
        specialize (Heqm δ) as [Heqm|Heqm].
        { exfalso; apply Heqm. by apply mcrename_inv. }
        pose proof Hδ as ?%mcrename_has_mcname'.
        rewrite lookup_op in Heqm.
        destruct (remove_mc_iResUR μ z i !! δ) eqn:Heqm'.
        { apply in_remove_keys_in_mc in Heqm' as []; done. }
        rewrite Heqm' right_id in Heqm.
        rewrite not_in_mcrename_keys in Heqm.
        specialize (Heqm γ) as [| <-]; done.
      * clear Heqm.
        specialize (Heq i γ).
        destruct (rename_mc_iResUR μ μ' z i !! γ) eqn:Heqm.
        { apply in_mcrename_keys in Heqm as (ξ & ?%mcrename_inv &?);
            simplify_eq. }
        rewrite Heqm lookup_op in Heq.
        destruct (x i !! γ) eqn:Heqx; destruct (y i !! γ) eqn:Heqy;
          rewrite ?Heqx ?Heqy ?left_id ?right_id in Heq;
          rewrite ?Heqx; by inversion Heq.
  - intros i γ.
    specialize (Heq i γ).
    destruct (rename_mc_iResUR μ μ' z i !! γ) eqn:Heqm; last first.
    + rewrite Heqm lookup_op in Heq.
      destruct (x i !! γ) eqn:Heqx; destruct (y i !! γ) eqn:Heqy;
        rewrite ?Heqx ?Heqy ?left_id ?right_id in Heq;
        rewrite ?Heqy; try (by inversion Heq); [].
      destruct (mcrename_keys μ μ' (rename_mc_iResUR μ' μ y i) !! γ) eqn:Heqm';
        rewrite Heqm'; last done.
      apply in_mcrename_keys in Heqm' as (δ &?& Hlu).
      rewrite not_in_mcrename_keys in Heqm.
      specialize (Heqm δ) as [|]; first done.
      apply in_mcrename_keys in Hlu as (ξ & Hξ & Hlu).
      pose proof Hξ as ?%mcrename_inv; simplify_eq/=.
      rewrite Heqy in Hlu; done.
    + rewrite Heqm in Heq.
      apply in_mcrename_keys in Heqm as (δ &?& Hlu).
      destruct (mcrename_keys μ μ' (rename_mc_iResUR μ' μ y i) !! γ) eqn:Heqm';
        rewrite Heqm'.
      * apply in_mcrename_keys in Heqm' as (ξ &?& Hlu').
        apply in_mcrename_keys in Hlu' as (ξ' & Hξ' & Hlu'').
        assert (δ = ξ); subst.
        { eapply mcrename_inj; eauto. }
        pose proof Hξ' as ?%mcrename_inv; simplify_eq/=.
        rewrite Hlu''; done.
      * rewrite not_in_mcrename_keys in Heqm'.
        specialize (Heqm' δ) as [?|Heqm']; first done.
        rewrite not_in_mcrename_keys in Heqm'.
        specialize (Heqm' γ) as [Heqm'|Heqm'].
        { by exfalso; apply Heqm', mcrename_inv. }
        rewrite Heqm'; done.
Qed.

Lemma remove_mc_iResUR_op {Σ} μ (x x' : iResUR Σ) :
  remove_mc_iResUR μ (x ⋅ x') ≡ remove_mc_iResUR μ x ⋅ remove_mc_iResUR μ x'.
Proof.
  intros i γ; rewrite /remove_mc_iResUR.
  rewrite !discrete_fun_lookup_op !lookup_op.
  destruct (remove_keys_in_mc μ (x i) !! γ) as [m|] eqn:Heqm;
    destruct (remove_keys_in_mc μ (x' i) !! γ) as [m'|] eqn:Heqm'.
  - apply in_remove_keys_in_mc in Heqm as (? & <-).
    apply in_remove_keys_in_mc in Heqm' as (? & <-).
    destruct (remove_keys_in_mc μ (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw; last first.
    { rewrite Heqw.
      eapply not_in_remove_keys_in_mc in Heqw as [|Hnin]; first done.
      rewrite lookup_op in Hnin; rewrite Hnin; done. }
    rewrite Heqw.
    apply in_remove_keys_in_mc in Heqw as (? & <-).
    rewrite lookup_op //.
  - apply in_remove_keys_in_mc in Heqm as (? & <-).
    apply not_in_remove_keys_in_mc in Heqm' as [| <-]; first done.
    destruct (remove_keys_in_mc μ (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw;
      rewrite Heqw; last first.
    { eapply not_in_remove_keys_in_mc in Heqw as [| <-]; first done.
      rewrite lookup_op //. }
    apply in_remove_keys_in_mc in Heqw as (? & <-).
    rewrite lookup_op //.
  - apply in_remove_keys_in_mc in Heqm' as (? & <-).
    apply not_in_remove_keys_in_mc in Heqm as [| <-]; first done.
    destruct (remove_keys_in_mc μ (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw;
      rewrite Heqw; last first.
    { eapply not_in_remove_keys_in_mc in Heqw as [| <-]; first done.
      rewrite lookup_op //. }
    apply in_remove_keys_in_mc in Heqw as (? & <-).
    rewrite lookup_op //.
  - apply not_in_remove_keys_in_mc in Heqm as [|Heqm].
    { destruct (remove_keys_in_mc μ (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw;
        rewrite Heqw; last done.
      apply in_remove_keys_in_mc in Heqw as (? & <-); done. }
    apply not_in_remove_keys_in_mc in Heqm' as [|Heqm'].
    { destruct (remove_keys_in_mc μ (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw;
        rewrite Heqw; last done.
      apply in_remove_keys_in_mc in Heqw as (? & <-); done. }
    destruct (remove_keys_in_mc μ (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw;
      rewrite Heqw; last done.
    apply in_remove_keys_in_mc in Heqw as (? & <-).
    rewrite left_id lookup_op Heqm Heqm' //.
Qed.

Lemma remove_mc_iResUR_op_inv {Σ} μ n (z x y : iResUR Σ) :
  remove_mc_iResUR μ z ≡{n}≡ x ⋅ y →
  ∃ x' y' : iResUR Σ,
    z ≡{n}≡ x' ⋅ y' ∧
    x ≡{n}≡ remove_mc_iResUR μ x' ∧ y ≡{n}≡ remove_mc_iResUR μ y'.
Proof.
  intros Heq.
  exists (x ⋅ rename_mc_iResUR μ μ z), y; split_and!.
  - rewrite {1}(rename_mc_remove_mc_iResUR μ z) Heq.
    rewrite assoc -(comm (⋅) x) //.
  - rewrite remove_mc_iResUR_op.
    rewrite remove_mc_rename_mc_iResUR_emp right_id.
    intros i γ.
    specialize (Heq i γ).
    destruct (remove_mc_iResUR μ z i !! γ) eqn:Heqm;
      rewrite Heqm in Heq.
    + apply in_remove_keys_in_mc in Heqm as [].
      rewrite discrete_fun_lookup_op lookup_op in Heq.
      destruct (remove_mc_iResUR μ x i !! γ) eqn:Heqm'; rewrite Heqm'.
      * apply in_remove_keys_in_mc in Heqm' as [? Heqm'].
        rewrite Heqm'; done.
      * apply not_in_remove_keys_in_mc in Heqm' as [|Heqm']; first done.
        by rewrite Heqm'.
    + apply not_in_remove_keys_in_mc in Heqm as [Heqm|Heqm].
      * destruct (remove_mc_iResUR μ x i !! γ) eqn:Heqm'; rewrite Heqm'.
        -- apply in_remove_keys_in_mc in Heqm' as [? Heqm'].
          rewrite Heqm'; done.
        -- rewrite discrete_fun_lookup_op lookup_op in Heq.
           destruct (x i !! γ) eqn:Heqx; destruct (y i !! γ) eqn:Heqy;
            rewrite ?Heqx ?Heqy in Heq; rewrite Heqx; by inversion Heq.
      * rewrite discrete_fun_lookup_op lookup_op in Heq.
        destruct (remove_mc_iResUR μ x i !! γ) eqn:Heqm'; rewrite Heqm'.
        -- apply in_remove_keys_in_mc in Heqm' as [? Heqm'].
           rewrite Heqm'; done.
        -- destruct (x i !! γ) eqn:Heqx; destruct (y i !! γ) eqn:Heqy;
            rewrite ?Heqx ?Heqy in Heq; rewrite Heqx; by inversion Heq.
  - intros i γ.
    specialize (Heq i γ).
    destruct (remove_mc_iResUR μ z i !! γ) eqn:Heqm;
      rewrite Heqm in Heq.
    + apply in_remove_keys_in_mc in Heqm as [].
      rewrite discrete_fun_lookup_op lookup_op in Heq.
      destruct (remove_mc_iResUR μ y i !! γ) eqn:Heqm'; rewrite Heqm'.
      * apply in_remove_keys_in_mc in Heqm' as [? Heqm'].
        rewrite Heqm'; done.
      * apply not_in_remove_keys_in_mc in Heqm' as [|Heqm']; first done.
        by rewrite Heqm'.
    + apply not_in_remove_keys_in_mc in Heqm as [Heqm|Heqm].
      * destruct (remove_mc_iResUR μ y i !! γ) eqn:Heqm'; rewrite Heqm'.
        -- apply in_remove_keys_in_mc in Heqm' as [? Heqm'].
          rewrite Heqm'; done.
        -- rewrite discrete_fun_lookup_op lookup_op in Heq.
          destruct (x i !! γ) eqn:Heqx; destruct (y i !! γ) eqn:Heqy;
            rewrite ?Heqx ?Heqy in Heq; rewrite Heqy; by inversion Heq.
      * rewrite discrete_fun_lookup_op lookup_op in Heq.
        destruct (remove_mc_iResUR μ y i !! γ) eqn:Heqm'; rewrite Heqm'.
        -- apply in_remove_keys_in_mc in Heqm' as [? Heqm'].
          rewrite Heqm'; done.
        -- destruct (x i !! γ) eqn:Heqx; destruct (y i !! γ) eqn:Heqy;
            rewrite ?Heqx ?Heqy in Heq; rewrite Heqy; by inversion Heq.
Qed.

Lemma rename_mc_iResUR_mono {Σ} μ μ' (x x' : iResUR Σ) :
  x ≼ x' → rename_mc_iResUR μ μ' x ≼ rename_mc_iResUR μ μ' x'.
Proof.
  intros [z Hincl]; exists (rename_mc_iResUR μ μ' z).
  rewrite -rename_mc_iResUR_op Hincl //.
Qed.

Lemma rename_mc_iResUR_monoN {Σ} μ μ' n (x x' : iResUR Σ) :
  x ≼{n} x' → rename_mc_iResUR μ μ' x ≼{n} rename_mc_iResUR μ μ' x'.
Proof. 
  intros [z Hincl]; exists (rename_mc_iResUR μ μ' z).
  rewrite -rename_mc_iResUR_op Hincl //.
Qed.

Lemma remove_mc_iResUR_mono {Σ} μ (x x' : iResUR Σ) :
  x ≼ x' → remove_mc_iResUR μ x ≼ remove_mc_iResUR μ x'.
Proof.
  intros [z Hincl]; exists (remove_mc_iResUR μ z).
  rewrite -remove_mc_iResUR_op Hincl //.
Qed.

Lemma remove_mc_iResUR_monoN {Σ} μ n (x x' : iResUR Σ) :
  x ≼{n} x' → remove_mc_iResUR μ x ≼{n} remove_mc_iResUR μ x'.
Proof.
  intros [z Hincl]; exists (remove_mc_iResUR μ z).
  rewrite -remove_mc_iResUR_op Hincl //.
Qed.

Lemma rename_mc_iResUR_validN {Σ} μ ν n (x : iResUR Σ) :
  ✓{n} x → ✓{n} rename_mc_iResUR μ ν x.
Proof.
  intros Hvl i γ.
  destruct (mcrename_keys μ ν (x i) !! γ) as [m|] eqn:Heqm;
    rewrite Heqm; last done.
  apply in_mcrename_keys in Heqm as (δ & ? & Hδ).
  specialize (Hvl i δ); rewrite Hδ in Hvl; done.
Qed.

Lemma remove_mc_iResUR_validN {Σ} μ n (x : iResUR Σ) :
  ✓{n} x → ✓{n} remove_mc_iResUR μ x.
Proof.
  intros Hvl i γ.
  destruct (remove_keys_in_mc μ (x i) !! γ) as [m|] eqn:Heqm;
    rewrite Heqm; last done.
  apply in_remove_keys_in_mc in Heqm as [? Heqm].
  specialize (Hvl i γ); rewrite Heqm in Hvl; done.
Qed.

(* the modality rename_mc *)

Program Definition rename_mc {Σ} μ μ' (P : iProp Σ) : iProp Σ :=
  UPred _ (λ n x, uPred_holds P n (rename_mc_iResUR μ μ' x)) _.
Next Obligation.
Proof.
  intros Σ μ μ' P n1 n2 x1 x2 HP Hxs Hns; simpl in *.
  eapply uPred_mono; [eassumption| |done].
  apply rename_mc_iResUR_monoN; done.
Qed.
Fail Next Obligation.

(* the modality remove_mc *)

Program Definition remove_mc {Σ} μ (P : iProp Σ) : iProp Σ :=
  UPred _ (λ n x, uPred_holds P n (remove_mc_iResUR μ x)) _.
Next Obligation.
Proof.
  intros Σ μ P n1 n2 x1 x2 HP Hxs Hns; simpl in *.
  eapply uPred_mono; [eassumption| |done].
  apply remove_mc_iResUR_monoN; done.
Qed.
Fail Next Obligation.

(* rules for the two modalities and their interaction *)
Section modalities.
  Context {Σ : gFunctors}.
  Implicit Types P Q : iProp Σ.
  Local Arguments uPred_holds {_} !_.

  Global Instance rename_mc_ne μ ν : NonExpansive (@rename_mc Σ μ ν).
  Proof.
    intros; split; intros; simpl;
    eapply uPred_in_dist; eauto using rename_mc_iResUR_validN.
  Qed.
  Global Instance rename_mc_proper μ ν : Proper ((≡) ==> (≡)) (@rename_mc Σ μ ν).
  Proof. apply ne_proper, _. Qed.
    
  Global Instance remove_mc_ne μ : NonExpansive (@remove_mc Σ μ).
  Proof.
    intros; split; intros; simpl;
    eapply uPred_in_dist; eauto using remove_mc_iResUR_validN.
  Qed.
  Global Instance remove_mc_proper μ : Proper ((≡) ==> (≡)) (@remove_mc Σ μ).
  Proof. apply ne_proper, _. Qed.

  Lemma rename_mc_compose μ ν ρ P : rename_mc μ ν (rename_mc ν ρ P) ⊣⊢ rename_mc μ ρ P.
  Proof. split; intros; rewrite /rename_mc /= rename_mc_iResUR_comp //. Qed.
  
  Lemma rename_mc_intro μ P : rename_mc μ μ P ⊢ P.
  Proof.
    split; rewrite /rename_mc /=; intros.
    eapply uPred_mono; eauto using rename_mc_iResUR_includedN.
  Qed.
  
  Lemma remove_mc_idemp μ P : remove_mc μ (remove_mc μ P) ⊣⊢ remove_mc μ P.
  Proof.
    split; rewrite /remove_mc /=; intros; rewrite remove_mc_iResUR_idemp //.
  Qed.

  Lemma remove_mc_intro μ P : remove_mc μ P ⊢ P.
  Proof.
    split; rewrite /remove_mc /=; intros.
    eapply uPred_mono; eauto using remove_mc_iResUR_includedN.
  Qed.

  Lemma remove_mc_rename_mc_plainly μ ν P : remove_mc μ (rename_mc μ ν P) ⊣⊢ ■ P.
  Proof.
    split; unseal; intros; rewrite /remove_mc /rename_mc /=
      rename_mc_remove_mc_iResUR_empty //.
  Qed.

  Lemma remove_mc_rename_mc_just_rename μ ν ρ P :
    ρ ≠ μ → remove_mc ρ (rename_mc μ ν P) ⊣⊢ (rename_mc μ ν P).
  Proof.
    split; intros; rewrite /remove_mc /rename_mc /=
      rename_mc_remove_mc_iResUR_id //.
  Qed.

  Lemma rename_mc_remove_mc_plainly μ ν P :
    rename_mc ν μ (remove_mc μ P) ⊣⊢ ■ P.
  Proof.
    split; unseal; intros; rewrite /remove_mc /rename_mc /=
      remove_mc_rename_mc_iResUR_emp //.
  Qed.

  Lemma rename_mc_remove_mc_just_rename μ ν ρ P :
    ρ ≠ ν → rename_mc μ ν (remove_mc ρ P) ≡ rename_mc μ ν P.
  Proof.
    split; intros; rewrite /remove_mc /rename_mc /=
      remove_mc_rename_mc_iResUR_id //.
  Qed.

  Lemma rename_mc_pure μ ν φ : rename_mc μ ν ⌜φ⌝ ⊣⊢@{iPropI Σ} ⌜φ⌝.
  Proof. split; unseal; done. Qed.

  Lemma rename_mc_emp μ ν P : rename_mc μ ν emp ⊣⊢@{iPropI Σ} emp.
  Proof. split; unseal; done. Qed.

  Lemma rename_mc_plainly μ ν P : rename_mc μ ν (■ P) ⊣⊢ ■ P.
  Proof. split; unseal; done. Qed.
  
  Lemma plainly_rename_mc μ ν P : ■ (rename_mc μ ν P) ⊣⊢ ■ P.
  Proof. split; unseal; done. Qed.

  Lemma rename_mc_persistently μ ν P :
    rename_mc μ ν (<pers> P) ⊣⊢ <pers> (rename_mc μ ν P).
  Proof. split; unseal; intros; rewrite rename_mc_iResUR_core //. Qed.

  Lemma rename_mc_later μ ν P :
    rename_mc μ ν (▷ P) ⊣⊢ ▷ (rename_mc μ ν P).
  Proof. split; unseal; done. Qed.

  Lemma rename_mc_forall {A} μ ν (Φ : A → iProp Σ) :
    rename_mc μ ν (∀ x, Φ x) ⊣⊢ ∀ x, rename_mc μ ν (Φ x).
  Proof. split; unseal; done. Qed.

  Lemma rename_mc_exist {A} μ ν (Φ : A → iProp Σ) :
    rename_mc μ ν (∃ x, Φ x) ⊣⊢ ∃ x, rename_mc μ ν (Φ x).
  Proof. split; unseal; done. Qed.

  Lemma rename_mc_or μ ν P Q :
    rename_mc μ ν (P ∨ Q) ⊣⊢ rename_mc μ ν P ∨ rename_mc μ ν Q.
  Proof. split; unseal; done. Qed.

  Lemma rename_mc_and μ ν P Q :
    rename_mc μ ν (P ∧ Q) ⊣⊢ rename_mc μ ν P ∧ rename_mc μ ν Q.
  Proof. split; unseal; done. Qed.

  Lemma rename_mc_impl μ ν P Q :
    rename_mc μ ν (P → Q) ⊢ (rename_mc μ ν P → rename_mc μ ν Q).
  Proof.
    split; unseal; simpl; intros ??? Hant; intros.
    apply Hant; [|done| |done].
    - by apply rename_mc_iResUR_mono.
    - by apply rename_mc_iResUR_validN.
  Qed.

  Lemma rename_mc_sep μ ν P Q :
    rename_mc μ ν (P ∗ Q) ⊣⊢ rename_mc μ ν P ∗ rename_mc μ ν Q.
  Proof.
    split; unseal; intros ???; split; intros (?&?& Heq &?&?).
    - destruct (rename_mc_iResUR_op_inv _ _ _ _ _ _ Heq) as
        (z & w & Hzw & Hz & Hw).
      eexists; eexists; split; first done.
      rewrite -Hz -Hw; auto.
    - eexists (rename_mc_iResUR μ ν _);
        eexists (rename_mc_iResUR μ ν _);
        rewrite -rename_mc_iResUR_op Heq; eauto.
  Qed.

  Lemma rename_mc_wand μ ν P Q :
    rename_mc μ ν (P -∗ Q) ⊢ (rename_mc μ ν P -∗ rename_mc μ ν Q).
  Proof.
    split; unseal; intros ??? Hant; intros.
    rewrite rename_mc_iResUR_op.
    apply Hant; [done| |done].
    rewrite -rename_mc_iResUR_op. by apply rename_mc_iResUR_validN.
  Qed.

  Lemma rename_mc_except_0 μ ν P : rename_mc μ ν (◇ P) ⊣⊢ ◇ (rename_mc μ ν P).
  Proof. rewrite /bi_except_0 rename_mc_or rename_mc_later rename_mc_pure //. Qed.

  Lemma remove_mc_pure μ φ : remove_mc μ ⌜φ⌝ ⊣⊢@{iPropI Σ} ⌜φ⌝.
  Proof. split; unseal; done. Qed.

  Lemma remove_mc_emp μ P : remove_mc μ emp ⊣⊢@{iPropI Σ} emp.
  Proof. split; unseal; done. Qed.

  Lemma remove_mc_plainly μ P : remove_mc μ (■ P) ⊣⊢ ■ P.
  Proof. split; unseal; done. Qed.
  
  Lemma plainly_remove_mc μ P : ■ (remove_mc μ P) ⊣⊢ ■ P.
  Proof. split; unseal; done. Qed.

  Lemma remove_mc_persistently μ P :
    remove_mc μ (<pers> P) ⊣⊢ <pers> (remove_mc μ P).
  Proof. split; unseal; intros; rewrite remove_mc_iResUR_core //. Qed.

  Lemma remove_mc_later μ P :
    remove_mc μ (▷ P) ⊣⊢ ▷ (remove_mc μ P).
  Proof. split; unseal; done. Qed.

  Lemma remove_mc_forall {A} μ (Φ : A → iProp Σ) :
    remove_mc μ (∀ x, Φ x) ⊣⊢ ∀ x, remove_mc μ (Φ x).
  Proof. split; unseal; done. Qed.

  Lemma remove_mc_exist {A} μ (Φ : A → iProp Σ) :
    remove_mc μ (∃ x, Φ x) ⊣⊢ ∃ x, remove_mc μ (Φ x).
  Proof. split; unseal; done. Qed.

  Lemma remove_mc_or μ P Q :
    remove_mc μ (P ∨ Q) ⊣⊢ remove_mc μ P ∨ remove_mc μ Q.
  Proof. split; unseal; done. Qed.

  Lemma remove_mc_and μ P Q :
    remove_mc μ (P ∧ Q) ⊣⊢ remove_mc μ P ∧ remove_mc μ Q.
  Proof. split; unseal; done. Qed.

  Lemma remove_mc_impl μ P Q :
    remove_mc μ (P → Q) ⊢ (remove_mc μ P → remove_mc μ Q).
  Proof.
    split; unseal; simpl; intros ??? Hant; intros.
    apply Hant; [|done| |done].
    - by apply remove_mc_iResUR_mono.
    - by apply remove_mc_iResUR_validN.
  Qed.

  Lemma remove_mc_sep μ P Q :
    remove_mc μ (P ∗ Q) ⊣⊢ remove_mc μ P ∗ remove_mc μ Q.
  Proof.
    split; unseal; intros ???; split; intros (?&?& Heq &?&?).
    - destruct (remove_mc_iResUR_op_inv _ _ _ _ _ Heq) as
        (z & w & Hzw & Hz & Hw).
      eexists; eexists; split; first done.
      rewrite -Hz -Hw; auto.
    - eexists (remove_mc_iResUR μ _);
        eexists (remove_mc_iResUR μ _);
        rewrite -remove_mc_iResUR_op Heq; eauto.
  Qed.

  Lemma remove_mc_wand μ P Q :
    remove_mc μ (P -∗ Q) ⊢ (remove_mc μ P -∗ remove_mc μ Q).
  Proof.
    split; unseal; intros ??? Hant; intros.
    rewrite remove_mc_iResUR_op.
    apply Hant; [done| |done].
    rewrite -remove_mc_iResUR_op. by apply remove_mc_iResUR_validN.
  Qed.

  Lemma remove_mc_except_0 μ P : remove_mc μ (◇ P) ⊣⊢ ◇ (remove_mc μ P).
  Proof. rewrite /bi_except_0 remove_mc_or remove_mc_later remove_mc_pure //. Qed.

End modalities.
  
(* type classes for ownership inside and outside a microcosm. *)
Class InsideMC {Σ} (μ : mcname) (P : iProp Σ) := inside_mc : P ⊢ rename_mc μ μ P.
Global Arguments inside_mc {Σ} μ P%_I.
Global Hint Mode InsideMC + + ! : typeclass_instances.
Global Instance: Params (@inside_mc) 4 := {}.
Global Typeclasses Opaque inside_mc.

Class OutsideMC {Σ} (μ : mcname) (P : iProp Σ) := outside_mc : P ⊢ remove_mc μ P.
Global Arguments outside_mc {Σ} μ P%_I.
Global Hint Mode OutsideMC + + ! : typeclass_instances.
Global Instance: Params (@outside_mc) 4 := {}.
Global Typeclasses Opaque outside_mc.

Section inside_outside_rules_instances.
  Context {Σ : gFunctors}.

  Implicit Types P Q : iProp Σ.
  Implicit Types μ ν ρ : mcname.

  Global Instance rename_inside P μ ν : InsideMC μ (rename_mc μ ν P).
  Proof. rewrite /InsideMC rename_mc_compose //. Qed.

  Global Instance rename_outside P μ ν : μ ≠ ν → OutsideMC ν (rename_mc μ ν P).
  Proof. intros; rewrite /OutsideMC remove_mc_rename_mc_just_rename //. Qed.

  Global Instance remove_outside P μ : OutsideMC μ (remove_mc μ P).
  Proof. rewrite /OutsideMC remove_mc_idemp //. Qed.

  Lemma inside_mc_eq_rename μ P `{!InsideMC μ P} : P ⊣⊢ rename_mc μ μ P.
  Proof. iSplit; first by iApply inside_mc. iApply rename_mc_intro. Qed.

  Lemma inside_mc_eq_remove μ P `{!OutsideMC μ P} : P ⊣⊢ remove_mc μ P.
  Proof. iSplit; first by iApply outside_mc. iApply remove_mc_intro. Qed.

  Global Instance plain_inside `{!Plain P} μ : InsideMC μ P.
  Proof. rewrite /InsideMC -(plain_plainly P) rename_mc_plainly //. Qed.
  Global Instance plain_outside `{!Plain P} μ : OutsideMC μ P.
  Proof. rewrite /OutsideMC -(plain_plainly P) remove_mc_plainly //. Qed.

  Global Instance persistently_inside `{!InsideMC μ P} : InsideMC μ (<pers> P).
  Proof.
    rewrite /InsideMC rename_mc_persistently; apply persistently_mono; done.
  Qed.
  Global Instance persistently_outside `{!OutsideMC μ P} : OutsideMC μ (<pers> P).
  Proof.
    rewrite /OutsideMC remove_mc_persistently; apply persistently_mono; done.
  Qed.

  Global Instance except_0_inside `{!InsideMC μ P} : InsideMC μ (◇ P).
  Proof.
    rewrite /InsideMC rename_mc_except_0; apply except_0_mono; done.
  Qed.
  Global Instance except_0_outside `{!OutsideMC μ P} : OutsideMC μ (◇ P).
  Proof.
    rewrite /OutsideMC remove_mc_except_0; apply except_0_mono; done.
  Qed.

  Global Instance later_inside `{!InsideMC μ P} : InsideMC μ (▷ P).
  Proof.
    rewrite /InsideMC rename_mc_later; apply later_mono; done.
  Qed.
  Global Instance later_outside `{!OutsideMC μ P} : OutsideMC μ (▷ P).
  Proof.
    rewrite /OutsideMC remove_mc_later; apply later_mono; done.
  Qed.

  Global Instance sep_inside `{!InsideMC μ P, !InsideMC μ Q} : InsideMC μ (P ∗ Q).
  Proof.
    rewrite /InsideMC rename_mc_sep; apply sep_mono; done.
  Qed.
  Global Instance sep_outside `{!OutsideMC μ P, !OutsideMC μ Q} : OutsideMC μ (P ∗ Q).
  Proof.
    rewrite /OutsideMC remove_mc_sep; apply sep_mono; done.
  Qed.

  Global Instance and_inside `{!InsideMC μ P, !InsideMC μ Q} : InsideMC μ (P ∧ Q).
  Proof.
    rewrite /InsideMC rename_mc_and; apply and_mono; done.
  Qed.
  Global Instance and_outside `{!OutsideMC μ P, !OutsideMC μ Q} : OutsideMC μ (P ∧ Q).
  Proof.
    rewrite /OutsideMC remove_mc_and; apply and_mono; done.
  Qed.

  Global Instance or_inside `{!InsideMC μ P, !InsideMC μ Q} : InsideMC μ (P ∨ Q).
  Proof.
    rewrite /InsideMC rename_mc_or; apply or_mono; done.
  Qed.
  Global Instance or_outside `{!OutsideMC μ P, !OutsideMC μ Q} : OutsideMC μ (P ∨ Q).
  Proof.
    rewrite /OutsideMC remove_mc_or; apply or_mono; done.
  Qed.

  Global Instance forall_inside {A} (Φ : A → iProp Σ)
    `{!∀ x : A, InsideMC μ (Φ x)} : InsideMC μ (∀ x, Φ x).
  Proof.
    rewrite /InsideMC rename_mc_forall; apply forall_mono; done.
  Qed.
  Global Instance forall_outside {A} (Φ : A → iProp Σ)
    `{!∀ x : A, OutsideMC μ (Φ x)} : OutsideMC μ (∀ x, Φ x).
  Proof.
    rewrite /OutsideMC remove_mc_forall; apply forall_mono; done.
  Qed.

  Global Instance exist_inside {A} (Φ : A → iProp Σ)
    `{!∀ x : A, InsideMC μ (Φ x)} : InsideMC μ (∃ x, Φ x).
  Proof.
    rewrite /InsideMC rename_mc_exist; apply exist_mono; done.
  Qed.
  Global Instance exist_outside {A} (Φ : A → iProp Σ)
    `{!∀ x : A, OutsideMC μ (Φ x)} : OutsideMC μ (∃ x, Φ x).
  Proof.
    rewrite /OutsideMC remove_mc_exist; apply exist_mono; done.
  Qed.

End inside_outside_rules_instances.

(* creating a new microcosm *)

Lemma rename_mc_iResUR_in_fresh_mcname {Σ} μ ν n (x y : iResUR Σ) :
  ν ∉ (mcnames_of_iResUR y) → ✓{n} x → ✓{n} y → ✓{n} (rename_mc_iResUR μ ν x ⋅ y).
Proof.
  intros Hfresh Hvlx Hvlf i γ.
  rewrite discrete_fun_lookup_op.
  destruct ((mcrename_keys μ ν (x i) ⋅ y i) !! γ) as [m|] eqn:Heqm;
    rewrite Heqm; last done.
  rewrite lookup_op in Heqm.
  destruct (mcrename_keys μ ν (x i) !! γ) as [w|] eqn:Heqw; last first.
  { rewrite left_id in Heqm.
    specialize (Hvlf i γ).
    rewrite -Heqm; done. }
  apply in_mcrename_keys in Heqw as (δ & Hγ & Hδ).
  assert (y i !! γ = None) as Hfiγ.
  { apply (not_elem_of_dom (y i)).
    pose proof (mcnames_of_iResUR_include_dom y i) as Hdom.
    assert (ν ∉ mcnames_of (dom (y i))) as Hν by set_solver.
    intros ?; apply Hν.
    apply elem_of_mcnames_of.
    exists γ; split; last done.
    apply mcrename_spec in Hγ as (?&?&?&->).
    apply mcname_of_push_mcname. }
    rewrite Hfiγ right_id in Heqm; simplify_eq.
    specialize (Hvlx i δ).
    rewrite Hδ in Hvlx; done.
Qed.

Section new_microcosm.
  Local Arguments uPred_holds {_} !_.

  Lemma new_microcosm {Σ} (P : iProp Σ) μ `{!InsideMC μ P} :
  P ⊢ ■ ∀ (M : gset mcname), |==> ∃ ν, ⌜ν ∉ M⌝ ∗ rename_mc ν μ P.
  Proof.
    rewrite {1}(inside_mc_eq_rename μ P).
    rewrite /rename_mc; unseal.
    split; intros n x Hvl HP M k f Hkn Hvl'; simpl in *.
    rewrite left_id in Hvl'.
    exists (rename_mc_iResUR μ (fresh_mcname f M) x).
    pose proof (fresh_mcname_is_fresh f M).
    split.
    { apply rename_mc_iResUR_in_fresh_mcname;
      [set_solver|by eapply cmra_validN_le|done]. }
    eexists (fresh_mcname f M), ε, _; split; first by rewrite left_id.
    split; first set_solver.
    rewrite rename_mc_iResUR_comp.
    eapply uPred_holds_ne; [done|done| |by eauto].
    eapply rename_mc_iResUR_validN, cmra_validN_le; eauto.
  Qed.
End new_microcosm.

(* ownership;
   most of what's below is taken and adapted from Iris development's own.v file. *)

Local Definition mcown_def `{!inG Σ A} (μ : mcname) (γ : gname) (a : A) : iProp Σ :=
  own (push_mcname μ γ) a.
Local Definition mcown_aux : seal (@mcown_def). Proof. by eexists. Qed.
Definition mcown := mcown_aux.(unseal).
Global Arguments mcown {Σ A _} μ γ a.
Local Definition mcown_eq : @mcown = @mcown_def := mcown_aux.(seal_eq).
Local Instance: Params (@mcown) 5 := {}.

Lemma iRes_singleton_included `{i : !inG Σ A} γ (a : A) n x :
  own.iRes_singleton γ a ≼{n} x ↔
  ∃ b, x (inG_id i) !! γ ≡{n}≡ Some b ∧ ∃ c, b ≡{n}≡ (own.inG_unfold (cmra_transport inG_prf a)) ⋅? c.
Proof.
  split; intros Hincl.
  - destruct Hincl as [z Hincl].
    specialize (Hincl (inG_id i) γ).
    rewrite discrete_fun_lookup_op lookup_op in Hincl.
    rewrite /own.iRes_singleton discrete_fun_lookup_singleton /= in Hincl.
    rewrite lookup_singleton_eq in Hincl.
    destruct (z (inG_id i) !! γ) eqn:Hzlu.
    + rewrite Hzlu -Some_op in Hincl.
      eexists _; split; first done.
      eexists (Some _); simpl; eauto.
    + rewrite Hzlu right_id in Hincl.
      eexists _; split; first done.
      exists None; done.
  - destruct Hincl as (b & Hx & [c|] & Hc); simpl in *.
    + exists (discrete_fun_insert (inG_id i) (<[γ := c]> (x (inG_id i))) x).
      intros j δ.
      rewrite discrete_fun_lookup_op lookup_op.
      destruct (decide ((inG_id i) = j)) as [<-|].
      * destruct (decide (γ = δ)) as [<-|].
        -- rewrite discrete_fun_lookup_insert lookup_insert_eq.
           rewrite /own.iRes_singleton discrete_fun_lookup_singleton lookup_insert_eq.
           rewrite -Some_op Hx Hc //.
        -- rewrite discrete_fun_lookup_insert lookup_insert_ne; last done.
           rewrite /own.iRes_singleton discrete_fun_lookup_singleton lookup_insert_ne; last done.
           rewrite lookup_empty left_id //.
      * rewrite discrete_fun_lookup_insert_ne; last done.
        rewrite /own.iRes_singleton discrete_fun_lookup_singleton_ne; last done.
        rewrite lookup_empty left_id //.
    + exists (discrete_fun_insert (inG_id i) (delete γ (x (inG_id i))) x).
      intros j δ.
      rewrite discrete_fun_lookup_op lookup_op.
      destruct (decide ((inG_id i) = j)) as [<-|].
      * destruct (decide (γ = δ)) as [<-|].
        -- rewrite discrete_fun_lookup_insert lookup_delete_eq right_id.
           rewrite /own.iRes_singleton discrete_fun_lookup_singleton lookup_insert_eq.
           rewrite Hx Hc //.
        -- rewrite discrete_fun_lookup_insert lookup_delete_ne; last done.
          rewrite /own.iRes_singleton discrete_fun_lookup_singleton lookup_insert_ne; last done.
          rewrite lookup_empty left_id //.
      * rewrite discrete_fun_lookup_insert_ne; last done.
        rewrite /own.iRes_singleton discrete_fun_lookup_singleton_ne; last done.
        rewrite lookup_empty left_id //.
Qed.

(** * Properties about ghost ownership *)
Section global.
Context `{i : !inG Σ A}.
Implicit Types a : A.

(** ** Properties of [own] *)
Global Instance mcown_ne μ γ : NonExpansive (@mcown Σ A _ μ γ).
Proof. rewrite !mcown_eq. solve_proper. Qed.
Global Instance mcown_proper μ γ :
  Proper ((≡) ==> (⊣⊢)) (@mcown Σ A _ μ γ) := ne_proper _.

Section rename_remove_mcown.
  Local Arguments uPred_holds {_} !_.
  
  Lemma rename_mcown μ ν γ a :
    rename_mc ν μ (mcown μ γ a) ⊣⊢ mcown ν γ a.
  Proof.
    rewrite /rename_mc !mcown_eq /mcown_def own.own_eq /own.own_def.
    unseal; rewrite /upred.uPred_ownM_def.
    split; intros n x Hvl; simpl.
    rewrite !iRes_singleton_included.
    split.
    - intros (b & Hlu & c & Hc).
      rewrite /rename_mc_iResUR in Hlu.
      destruct (mcrename_keys ν μ (x (inG_id i)) !! push_mcname μ γ) as [b'|] eqn:Hb'; last first.
      {rewrite Hb' in Hlu; inversion Hlu. }
      assert (b ≡{n}≡ b') as Hbb'.
      { apply Some_dist_inj; rewrite Hb' in Hlu; done. }
      apply in_mcrename_keys in Hb' as (δ & Hren & Hlu').
      exists b'; split.
      { erewrite <- mcrename_to_push; last done. rewrite Hlu' //. }
      exists c; rewrite -Hbb'; done.
    - intros (b & Hlu & c & Hc).
      rewrite /rename_mc_iResUR.
      pose proof (mcrename_of_push ν μ γ) as Hγ.
      destruct (mcrename_keys ν μ (x (inG_id i)) !! push_mcname μ γ) as [b'|] eqn:Hb'; last first.
      { eapply not_in_mcrename_keys' in Hb'; last done.
        rewrite Hb' in Hlu; inversion Hlu. }
      pose proof Hb' as (δ & Hren & Hlu')%in_mcrename_keys.
      apply mcrename_to_push in Hren; subst.
      assert (b ≡{n}≡ b') as Hbb'.
      { apply Some_dist_inj; rewrite Hlu' in Hlu; done. }
      exists b'; split.
      { rewrite Hb'; done. }
      exists c; rewrite -Hbb'; done.
  Qed.

  Lemma remove_mcown_1 μ γ a :
    remove_mc μ (mcown μ γ a) ⊣⊢ False.
  Proof.
    split; rewrite /remove_mc mcown_eq /mcown_def /= own.own_eq /own.own_def /=; unseal.
    intros ? x; split; last done.
    intros (?& Heq &?&?)%iRes_singleton_included.
    destruct (remove_mc_iResUR μ x (inG_id i) !! push_mcname μ γ) eqn:Heqm;
      last by inversion Heq.
    apply in_remove_keys_in_mc in Heqm as [Heqm _].
    apply Heqm; rewrite mcname_of_push_mcname //.
  Qed.

  Lemma remove_mcown_2 μ ν γ a :
    μ ≠ ν → remove_mc μ (mcown ν γ a) ⊣⊢ mcown ν γ a.
  Proof.
    split; rewrite /remove_mc mcown_eq /mcown_def /= own.own_eq /own.own_def /=; unseal.
    intros ? x; split.
    - intros (?& Heq &?&?)%iRes_singleton_included.
      rewrite iRes_singleton_included.
      destruct (remove_mc_iResUR μ x (inG_id i) !! push_mcname ν γ) eqn:Heqm;
        last by inversion Heq.
        apply in_remove_keys_in_mc in Heqm as [Heqm1 Heqm2].
        eexists; split; last by eauto. by rewrite Heqm2.
    - intros (?& Heq &?&?)%iRes_singleton_included.
      rewrite iRes_singleton_included.
      destruct (x (inG_id i) !! push_mcname ν γ) eqn:Heqm;
        last by inversion Heq.
      apply Some_dist_inj in Heq.
      destruct (remove_mc_iResUR μ x (inG_id i) !! push_mcname ν γ) eqn:Heqm'.
      + apply in_remove_keys_in_mc in Heqm' as [? Heqm'].
        rewrite Heqm in Heqm'; simplify_eq.
        eexists; split; first done. by eexists; rewrite Heq.
      + apply not_in_remove_keys_in_mc in Heqm' as [Heqm'|Heqm'].
        { rewrite mcname_of_push_mcname in Heqm'; simplify_eq. }
        rewrite Heqm in Heqm'; done.
  Qed.
  
End rename_remove_mcown.

Global Instance mcown_inside μ γ a : InsideMC μ (mcown μ γ a).
Proof. rewrite /InsideMC rename_mcown //. Qed.

Global Instance mcown_outside μ ν γ a : μ ≠ ν → OutsideMC μ (mcown ν γ a).
Proof. intros; rewrite /OutsideMC remove_mcown_2 //. Qed.


Lemma mcown_op μ γ a1 a2 : mcown μ γ (a1 ⋅ a2) ⊣⊢ mcown μ γ a1 ∗ mcown μ γ a2.
Proof. by rewrite !mcown_eq /mcown_def own_op. Qed.
Lemma mcown_mono μ γ a1 a2 : a2 ≼ a1 → mcown μ γ a1 ⊢ mcown μ γ a2.
Proof. move=> [c ->]. by rewrite mcown_op sep_elim_l. Qed.

Global Instance mcown_mono' μ γ : Proper (flip (≼) ==> (⊢)) (@mcown Σ A _ μ γ).
Proof. intros a1 a2. apply mcown_mono. Qed.

Lemma mcown_valid μ γ a : mcown μ γ a ⊢ ✓ a.
Proof. by rewrite !mcown_eq /mcown_def; apply own_valid. Qed.
Lemma mcown_valid_2 μ γ a1 a2 : mcown μ γ a1 -∗ mcown μ γ a2 -∗ ✓ (a1 ⋅ a2).
Proof. apply entails_wand, wand_intro_r. by rewrite -mcown_op mcown_valid. Qed.
Lemma mcown_valid_3 μ γ a1 a2 a3 : mcown μ γ a1 -∗ mcown μ γ a2 -∗ mcown μ γ a3 -∗ ✓ (a1 ⋅ a2 ⋅ a3).
Proof. apply entails_wand. do 2 apply wand_intro_r. by rewrite -!mcown_op mcown_valid. Qed.
Lemma mcown_valid_r μ γ a : mcown μ γ a ⊢ mcown μ γ a ∗ ✓ a.
Proof. apply: bi.persistent_entails_r. apply mcown_valid. Qed.
Lemma mcown_valid_l μ γ a : mcown μ γ a ⊢ ✓ a ∗ mcown μ γ a.
Proof. by rewrite comm -mcown_valid_r. Qed.

Global Instance mcown_timeless μ γ a : Discrete a → Timeless (mcown μ γ a).
Proof. rewrite !mcown_eq /mcown_def. apply _. Qed.
Global Instance mcown_core_persistent μ γ a : CoreId a → Persistent (mcown μ γ a).
Proof. rewrite !mcown_eq /mcown_def; apply _. Qed.

Lemma later_mcown μ γ a : ▷ mcown μ γ a ⊢ ◇ ∃ b, mcown μ γ b ∧ ▷ (a ≡ b).
Proof. rewrite mcown_eq /mcown_def; apply later_own. Qed.

Lemma mcown_alloc_strong_dep
  (f : mcname → gname → A) (M : gset mcname) (P : gname → Prop) :
  pred_infinite P →
  (∀ μ γ, μ ∈ M → P γ → ✓ (f μ γ)) →
  ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ [∗ set] μ ∈ M, mcown μ γ (f μ γ).
Proof.
  intros HPinf Hf.
  set (w γ := foldr (λ μ (m : gmap gname A),
    <[push_mcname μ γ := (f μ γ)]>m) ε (elements M)).
  set (r γ := (λ x, own.inG_unfold (cmra_transport inG_prf x)) <$> w γ).
  rewrite -(bupd_mono (∃ m, ⌜∃ γ, P γ ∧
    m = discrete_fun_singleton (inG_id i) (r γ)⌝ ∧ uPred_ownM m)%I).
  - rewrite /bi_emp_valid (ownM_unit emp).
    apply bupd_ownM_updateP, (discrete_fun_singleton_updateP_empty _ (λ m, ∃ γ,
      m = (λ x, own.inG_unfold (cmra_transport inG_prf x)) <$> w γ ∧ P γ));
      last first.
    { intros ? (?& -> &?); eexists; split; done. }
    apply (alloc_updateP_strong_dep pop_mcname push_mcname (elements M)
      _ P _ (λ μ γ, own.inG_unfold (cmra_transport inG_prf (f μ γ)))).
    { apply NoDup_elements. }
    { done. }
    { intros ??? []%push_mcname_inj; done. }
    { intros; apply pop_push_mcname. }
    { intros;
        by apply (cmra_morphism_valid own.inG_unfold), cmra_transport_valid, Hf;
        [apply elem_of_elements|]. }
    intros; eexists; split; last done.
    rewrite /w; clear; induction (elements M) as [|μ L IHL];
      simpl in *; first done.
    rewrite fmap_insert IHL //.
  - apply exist_elim=>m; apply pure_elim_l=>-[γ [Hfresh ->]].
    rewrite !mcown_eq /mcown_def -(exist_intro γ) pure_True // left_id.
    rewrite big_sepS_elements.
    pose proof (NoDup_elements M) as HM.
    rewrite /r /w; clear -HM;
      induction (elements M) as [|μ L IHL]; simpl in *; first by auto.
    rewrite fmap_insert insert_singleton_op.
    + rewrite -discrete_fun_singleton_op ownM_op.
      apply sep_mono; first by rewrite !own.own_eq /own.own_def.
      apply IHL; by inversion HM.
    + assert (μ ∉ L) as HμL by by inversion HM.
      clear -HμL; induction L as [|ν L IHL]; simpl; first done.
      rewrite lookup_fmap lookup_insert_ne -?lookup_fmap; first by apply IHL; set_solver.
      intros []%push_mcname_inj; simplify_eq; set_solver.
Qed.

Lemma mcown_alloc_cofinite_dep (f : mcname → gname → A)
  (M : gset mcname) (G : gset gname) :
  (∀ μ γ, μ ∈ M → γ ∉ G → ✓ (f μ γ)) →
  ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ [∗ set] μ ∈ M, mcown μ γ (f μ γ).
Proof.
  intros Ha.
  apply (mcown_alloc_strong_dep f M (λ γ, γ ∉ G))=> //.
  apply (pred_infinite_set (C:=gset gname)).
  intros E. set (γ := fresh (G ∪ E)).
  exists γ. apply not_elem_of_union, is_fresh.
Qed.
Lemma mcown_alloc_dep (f : mcname → gname → A) (M : gset mcname) :
  (∀ μ γ, μ ∈ M → ✓ (f μ γ)) → ⊢ |==> ∃ γ, [∗ set] μ ∈ M, mcown μ γ (f μ γ).
Proof.
  intros Ha. rewrite /bi_emp_valid (mcown_alloc_cofinite_dep f M ∅); last by auto.
  apply bupd_mono, exist_mono=>?. apply: sep_elim_r.
Qed.

Lemma mcown_alloc_strong a (M : gset mcname) (P : gname → Prop) :
  pred_infinite P →
  ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ [∗ set] μ ∈ M, mcown μ γ a.
Proof. intros HP Ha. eapply (mcown_alloc_strong_dep (λ _ _, a)); eauto. Qed.
Lemma mcown_alloc_cofinite a (M : gset mcname) (G : gset gname) :
  ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ [∗ set] μ ∈ M, mcown μ γ a.
Proof. intros Ha. eapply (mcown_alloc_cofinite_dep (λ _ _, a)); eauto. Qed.
Lemma mcown_alloc a (M : gset mcname) : ✓ a → ⊢ |==> ∃ γ, [∗ set] μ ∈ M, mcown μ γ a.
Proof. intros Ha. eapply (mcown_alloc_dep (λ _ _, a)); eauto. Qed.

Lemma mcown_alloc_strong' a μ (P : gname → Prop) :
  pred_infinite P →
  ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ mcown μ γ a.
Proof.
  intros HP Ha.
  iPoseProof (mcown_alloc_strong a {[μ]}) as "H"; eauto; [].
  iMod "H" as (?) "[? ?]"; rewrite big_sepS_singleton; iFrame; done.
Qed.
Lemma mcown_alloc_cofinite' a μ (G : gset gname) :
  ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ mcown μ γ a.
Proof.
  intros Ha.
  iPoseProof (mcown_alloc_cofinite a {[μ]}) as "H"; eauto; [].
  iMod "H" as (?) "[? ?]"; rewrite big_sepS_singleton; iFrame; done.
Qed.
Lemma mcown_alloc' a μ : ✓ a → ⊢ |==> ∃ γ, mcown μ γ a.
Proof.
  intros Ha.
  iPoseProof (mcown_alloc a {[μ]}) as "H"; eauto; [].
  iMod "H" as (?) "?"; rewrite big_sepS_singleton; iFrame; done.
Qed.

(** ** Frame preserving updates *)
Lemma mcown_updateP P μ γ a : a ~~>: P → mcown μ γ a ⊢ |==> ∃ a', ⌜P a'⌝ ∗ mcown μ γ a'.
Proof. by intros; rewrite !mcown_eq /mcown_def; apply own_updateP. Qed.

Lemma mcown_update μ γ a a' : a ~~> a' → mcown μ γ a ⊢ |==> mcown μ γ a'.
Proof. by intros; rewrite !mcown_eq /mcown_def; apply own_update. Qed.
Lemma mcown_update_2 μ γ a1 a2 a' :
  a1 ⋅ a2 ~~> a' → mcown μ γ a1 -∗ mcown μ γ a2 ==∗ mcown μ γ a'.
Proof. by intros; rewrite !mcown_eq /mcown_def; apply own_update_2. Qed.
Lemma mcown_update_3 μ γ a1 a2 a3 a' :
  a1 ⋅ a2 ⋅ a3 ~~> a' → mcown μ γ a1 -∗ mcown μ γ a2 -∗ mcown μ γ a3 ==∗ mcown μ γ a'.
Proof. by intros; rewrite !mcown_eq /mcown_def; apply own_update_3. Qed.
End global.

Global Arguments mcown_valid {_ _} [_] _ _ _.
Global Arguments mcown_valid_2 {_ _} [_] _ _ _ _.
Global Arguments mcown_valid_3 {_ _} [_] _ _ _ _ _.
Global Arguments mcown_valid_l {_ _} [_] _ _ _.
Global Arguments mcown_valid_r {_ _} [_] _ _ _.
Global Arguments mcown_updateP {_ _} [_] _ _ _ _ _.
Global Arguments mcown_update {_ _} [_] _ _ _ _ _.
Global Arguments mcown_update_2 {_ _} [_] _ _ _ _ _ _.
Global Arguments mcown_update_3 {_ _} [_] _ _ _ _ _ _ _.

Lemma mcown_unit A `{i : !inG Σ (A:ucmra)} μ γ : ⊢ |==> mcown μ γ (ε:A).
Proof. rewrite mcown_eq /mcown_def; apply own_unit. Qed.

(** Big op class instances *)
Section big_op_instances.
  Context `{!inG Σ (A:ucmra)}.

  Global Instance own_cmra_sep_homomorphism μ γ :
    WeakMonoidHomomorphism op uPred_sep (≡) (mcown μ γ).
  Proof. split; try apply _. apply mcown_op. Qed.

  Lemma big_opL_mcown {B} μ γ (f : nat → B → A) (l : list B) :
    l ≠ [] →
    mcown μ γ ([^op list] k↦x ∈ l, f k x) ⊣⊢ [∗ list] k↦x ∈ l, mcown μ γ (f k x).
  Proof. apply (big_opL_commute1 _). Qed.
  Lemma big_opM_mcown `{Countable K} {B} μ γ (g : K → B → A) (m : gmap K B) :
    m ≠ ∅ →
    mcown μ γ ([^op map] k↦x ∈ m, g k x) ⊣⊢ [∗ map] k↦x ∈ m, mcown μ γ (g k x).
  Proof. apply (big_opM_commute1 _). Qed.
  Lemma big_opS_mcown `{Countable B} μ γ (g : B → A) (X : gset B) :
    X ≠ ∅ →
    mcown μ γ ([^op set] x ∈ X, g x) ⊣⊢ [∗ set] x ∈ X, mcown μ γ (g x).
  Proof. apply (big_opS_commute1 _). Qed.
  Lemma big_opMS_mcown `{Countable B} μ γ (g : B → A) (X : gmultiset B) :
    X ≠ ∅ →
    mcown μ γ ([^op mset] x ∈ X, g x) ⊣⊢ [∗ mset] x ∈ X, mcown μ γ (g x).
  Proof. apply (big_opMS_commute1 _). Qed.

  Global Instance own_cmra_sep_entails_homomorphism μ γ :
    MonoidHomomorphism op uPred_sep (⊢) (mcown μ γ).
  Proof.
    split; [split|]; try apply _.
    - intros. by rewrite mcown_op.
    - apply (affine _).
  Qed.

  Lemma big_opL_mcown_1 {B} μ γ (f : nat → B → A) (l : list B) :
    mcown μ γ ([^op list] k↦x ∈ l, f k x) ⊢ [∗ list] k↦x ∈ l, mcown μ γ (f k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_mcown_1 `{Countable K} {B} μ γ (g : K → B → A) (m : gmap K B) :
    mcown μ γ ([^op map] k↦x ∈ m, g k x) ⊢ [∗ map] k↦x ∈ m, mcown μ γ (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_mcown_1 `{Countable B} μ γ (g : B → A) (X : gset B) :
    mcown μ γ ([^op set] x ∈ X, g x) ⊢ [∗ set] x ∈ X, mcown μ γ (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_mcown_1 `{Countable B} μ γ (g : B → A) (X : gmultiset B) :
    mcown μ γ ([^op mset] x ∈ X, g x) ⊢ [∗ mset] x ∈ X, mcown μ γ (g x).
  Proof. apply (big_opMS_commute _). Qed.
End big_op_instances.

(** Proofmode class instances *)
Section proofmode_instances.
  Context `{!inG Σ A}.
  Implicit Types a b : A.

  Global Instance into_sep_mcown μ γ a b1 b2 :
    IsOp a b1 b2 → IntoSep (mcown μ γ a) (mcown μ γ b1) (mcown μ γ b2).
  Proof. intros. by rewrite /IntoSep (is_op a) mcown_op. Qed.
  Global Instance into_and_mcown p μ γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (mcown μ γ a) (mcown μ γ b1) (mcown μ γ b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) mcown_op sep_and. Qed.

  Global Instance from_sep_mcown μ γ a b1 b2 :
    IsOp a b1 b2 → FromSep (mcown μ γ a) (mcown μ γ b1) (mcown μ γ b2).
  Proof. intros. by rewrite /FromSep -mcown_op -is_op. Qed.
  (* TODO: Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_mcown μ γ a b1 b2 :
    IsOp a b1 b2 → CombineSepAs (mcown μ γ b1) (mcown μ γ b2) (mcown μ γ a) | 60.
  Proof. intros. by rewrite /CombineSepAs -mcown_op -is_op. Qed.
  (* TODO: Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_mcown μ γ b1 b2 :
    CombineSepGives (mcown μ γ b1) (mcown μ γ b2) (✓ (b1 ⋅ b2)).
  Proof.
    intros. rewrite /CombineSepGives -mcown_op mcown_valid.
    by apply: bi.persistently_intro.
  Qed.
  Global Instance from_and_mcown_persistent μ γ a b1 b2 :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (mcown μ γ a) (mcown μ γ b1) (mcown μ γ b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) mcown_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed.
End proofmode_instances.

Section mcown_forall.
  Context `{i : !inG Σ A}.
  Implicit Types a c : A.
  Implicit Types x z : iResUR Σ.

  (** Our main goal in this section is to prove [mcown_forall]:

    (∀ b, mcown μ γ (f b)) ⊢ ∃ c : A, mcown μ γ c ∗ (∀ b, Some (f b) ≼ Some c)
    
    We have the analogue for own: in the global ucmra, from [ownM_forall]:
    
    (∀ b, own γ (f b)) ⊢ ∃ c : A, own γ c ∗ (∀ b, Some (f b) ≼ Some c)
  *)

  Lemma mcown_forall `{!Inhabited B} μ γ (f : B → A) :
    (∀ b, mcown μ γ (f b)) ⊢ ∃ c, mcown μ γ c ∗ (∀ b, Some (f b) ≼ Some c).
  Proof. rewrite mcown_eq /mcown_def; iIntros "Hown"; by iApply @own_forall. Qed.

  (** Now some corollaries. *)
  Lemma mcown_forall_total `{!CmraTotal A, !Inhabited B} μ γ (f : B → A) :
    (∀ b, mcown μ γ (f b)) ⊢ ∃ c, mcown μ γ c ∗ (∀ b, f b ≼ c).
  Proof. setoid_rewrite <-Some_included_totalI. apply mcown_forall. Qed.

  Lemma mcown_and μ γ a1 a2 :
    mcown μ γ a1 ∧ mcown μ γ a2 ⊢ ∃ c, mcown μ γ c ∗ Some a1 ≼ Some c ∗ Some a2 ≼ Some c.
  Proof.
    iIntros "Hown". iDestruct (mcown_forall μ γ (λ b, if b : bool then a1 else a2)
      with "[Hown]") as (c) "[$ Hincl]".
    { rewrite and_alt.
      iIntros ([]); [iApply ("Hown" $! true)|iApply ("Hown" $! false)]. }
    iSplit; [iApply ("Hincl" $! true)|iApply ("Hincl" $! false)].
  Qed.
  Lemma mcown_and_total `{!CmraTotal A} μ γ a1 a2 :
    mcown μ γ a1 ∧ mcown μ γ a2 ⊢ ∃ c, mcown μ γ c ∗ a1 ≼ c ∗ a2 ≼ c.
  Proof. setoid_rewrite <-Some_included_totalI. apply mcown_and. Qed.

  (** A version of [own_forall] for bounded quantification. Here [φ : B → Prop]
  is a pure predicate that restricts the elements of [B]. *)
  Lemma mcown_forall_pred {B} μ γ (φ : B → Prop) (f : B → A) :
    (∃ b, φ b) → (* [φ] is non-empty *)
    (∀ b, ⌜ φ b ⌝ -∗ mcown μ γ (f b)) ⊢
    ∃ c, mcown μ γ c ∗ (∀ b, ⌜ φ b ⌝ -∗ Some (f b) ≼ Some c).
  Proof.
    iIntros ([b0 pb0]) "Hown".
    iAssert (∀ b : { b | φ b }, mcown μ γ (f (`b)))%I with "[Hown]" as "Hown".
    { iIntros ([b pb]). by iApply ("Hown" $! b). }
    iDestruct (@mcown_forall _ with "Hown") as (c) "[$ Hincl]".
    { split. apply (b0 ↾ pb0). }
    iIntros (b pb). iApply ("Hincl" $! (b ↾ pb)).
  Qed.
  Lemma mcown_forall_pred_total `{!CmraTotal A} {B} μ γ (φ : B → Prop) (f : B → A) :
    (∃ b, φ b) →
    (∀ b, ⌜ φ b ⌝ -∗ mcown μ γ (f b)) ⊢ ∃ c, mcown μ γ c ∗ (∀ b, ⌜ φ b ⌝ -∗ f b ≼ c).
  Proof. setoid_rewrite <-Some_included_totalI. apply mcown_forall_pred. Qed.

  Lemma mcown_and_discrete_total `{!CmraDiscrete A, !CmraTotal A} μ γ a1 a2 c :
    (∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → c ≼ c') →
    mcown μ γ a1 ∧ mcown μ γ a2 ⊢ mcown μ γ c.
  Proof.
    iIntros (Hvalid) "Hown".
    iDestruct (mcown_and_total with "Hown") as (c') "[Hown [%Ha1 %Ha2]]".
    iDestruct (mcown_valid with "Hown") as %?.
    iApply (mcown_mono with "Hown"); eauto.
  Qed.
  Lemma own_and_discrete_total_False `{!CmraDiscrete A, !CmraTotal A} μ γ a1 a2 :
    (∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → False) →
    mcown μ γ a1 ∧ mcown μ γ a2 ⊢ False.
  Proof.
    iIntros (Hvalid) "Hown".
    iDestruct (mcown_and_total with "Hown") as (c) "[Hown [%Ha1 %Ha2]]".
    iDestruct (mcown_valid with "Hown") as %?; eauto.
  Qed.
End mcown_forall.
