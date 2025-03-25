From microcosms Require Import prelude.
From stdpp Require Import countable gmap finite.
From iris.algebra Require Import functions gmap proofmode_classes.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export iprop own.
Import uPred.

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
    (l&l'&->)%(elem_of_list_fmap_1 (λ i, dom (x i)))%elem_of_list_split.
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

Lemma fresh_mcname_is_fresh' `(x : !iResUR Σ) M i γ :
  x i !! push_mcname (fresh_mcname x M) γ = None.
Proof.
  apply (not_elem_of_dom (x i)).
  pose proof (fresh_mcname_is_fresh x M).
  pose proof (mcnames_of_iResUR_include_dom x i).
  assert (fresh_mcname x M ∉ mcnames_of (dom (x i))) as Hnin by set_solver.
  intros (γ' & Heq & Hin)%elem_of_push_mcname.
  apply Hnin, elem_of_mcnames_of; eauto.
Qed.

Definition mcrename_keys {A} (μ μ' : mcname) (g : gmap gname A) : gmap gname A :=
  list_to_map (omap (λ γa, option_map (λ δ, (δ, γa.2)) (mcrename μ μ' γa.1)) (map_to_list g)).

(*TODO: move lemma *)
Lemma NoDup_omap {A B} (f : A → option B) (l : list A) :
  (∀ a a' b, f a = Some b → f a' = Some b → a = a') →
  NoDup l →
  NoDup (omap f l).
Proof.
  intros Hf Hl.
  induction l as [|a l IHl]; simpl; first by constructor.
  destruct f as [b|] eqn:Heqb; last first.
  { apply IHl. by inversion Hl. }
  constructor; last first.
  { apply IHl. by inversion Hl. }
  intros Hbl.
  apply elem_of_list_omap in Hbl as (a' & Ha' & Hb').
  assert (a = a'); subst.
  { eapply Hf; eauto. }
  inversion Hl; done.
Qed.

Lemma in_mcrename_keys {A} μ μ' (g : gmap gname A) δ a :
  mcrename_keys μ μ' g !! δ = Some a ↔ ∃ γ, mcrename μ μ' γ = Some δ ∧ g !! γ = Some a.
Proof.
  rewrite /mcrename_keys.
  rewrite -elem_of_list_to_map; last first.
  { apply NoDup_fmap_fst.
    - intros ???.
      rewrite !elem_of_list_omap.
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
  rewrite elem_of_list_omap.
  split.
  - intros ([γ b]& Hγ &?); simpl in *.
    destruct (mcrename μ μ' γ) as [ξ|] eqn:Heqξ; last done.
    apply elem_of_map_to_list in Hγ.
    simplify_eq/=; eauto.
  - intros (γ & Hγ &?); simpl in *.
    exists (γ, a); split; first by apply elem_of_map_to_list.
    rewrite Hγ //=.
Qed.

Lemma not_in_mcrename_keys {A} μ μ' (g : gmap gname A) δ γ :
  mcrename_keys μ μ' g !! δ = None → mcrename μ μ' γ = Some δ → g !! γ = None.
Proof.
  rewrite /mcrename_keys.
  intros Hδ%not_elem_of_list_to_map_2 Hγδ.
  rewrite list_fmap_omap elem_of_list_omap in Hδ.
  destruct (g !! γ) eqn:Hgγ; last done.
  exfalso; apply Hδ.
  exists (γ, a).
  split; first by apply elem_of_map_to_list.
  rewrite Hγδ //=.
Qed.

Definition mcrename_iResUR {Σ} μ μ' (x : iResUR Σ) : iResUR Σ := λ i, mcrename_keys μ μ' (x i).

Local Instance mcrename_ne {Σ} n μ μ' : Proper ((dist n) ==> (dist n)) (@mcrename_iResUR Σ μ μ').
Proof.
  intros x y Heq i γ.
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
    eapply not_in_mcrename_keys in Heqm'; last by eauto.
    specialize (Heq i δ).
    rewrite Hδ Heqm' in Heq; done.
  - apply in_mcrename_keys in Heqm' as (δ' & ? & Hδ').
    eapply not_in_mcrename_keys in Heqm; last by eauto.
    specialize (Heq i δ').
    rewrite Heqm Hδ' in Heq; done.
Qed.

Lemma mcrename_iResUR_mul {Σ} μ μ' n (x x' : iResUR Σ) :
  mcrename_iResUR μ μ' (x ⋅ x') ≡{n}≡ mcrename_iResUR μ μ' x ⋅ mcrename_iResUR μ μ' x'.
Proof.
  intros i γ; rewrite /mcrename_iResUR.
  rewrite !discrete_fun_lookup_op !lookup_op.
  destruct (mcrename_keys μ μ' (x i) !! γ) as [m|] eqn:Heqm;
    destruct (mcrename_keys μ μ' (x' i) !! γ) as [m'|] eqn:Heqm';
    rewrite Heqm Heqm' /=.
  - apply in_mcrename_keys in Heqm as (δ & ? & Hδ).
    apply in_mcrename_keys in Heqm' as (δ' & ? & Hδ').
    assert (δ = δ'); subst.
    { eapply mcrename_inj; eauto. }
    destruct (mcrename_keys μ μ' (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw; last first.
    { eapply not_in_mcrename_keys in Heqw; last by eauto.
      rewrite lookup_op Hδ Hδ' in Heqw; done. }
    apply in_mcrename_keys in Heqw as (ξ & ? & Hξ).
    assert (ξ = δ'); subst.
    { eapply mcrename_inj; eauto. }
    rewrite lookup_op Hδ Hδ' -Some_op in Hξ; simplify_eq/=.
    rewrite Some_op //.
  - apply in_mcrename_keys in Heqm as (δ & ? & Hδ).
    eapply not_in_mcrename_keys in Heqm'; last by eauto.
    destruct (mcrename_keys μ μ' (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw; last first.
    { eapply not_in_mcrename_keys in Heqw; last by eauto.
      rewrite lookup_op Hδ Heqm' in Heqw; done. }
    apply in_mcrename_keys in Heqw as (ξ & ? & Hξ).
    assert (ξ = δ); subst.
    { eapply mcrename_inj; eauto. }
    rewrite lookup_op Hδ Heqm' right_id in Hξ; simplify_eq/=.
    rewrite right_id //.
  - apply in_mcrename_keys in Heqm' as (δ' & ? & Hδ').
    eapply not_in_mcrename_keys in Heqm; last by eauto.
    destruct (mcrename_keys μ μ' (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw; last first.
    { eapply not_in_mcrename_keys in Heqw; last by eauto.
      rewrite lookup_op Hδ' Heqm in Heqw; done. }
    apply in_mcrename_keys in Heqw as (ξ & ? & Hξ).
    assert (ξ = δ'); subst.
    { eapply mcrename_inj; eauto. }
    rewrite lookup_op Hδ' Heqm left_id in Hξ; simplify_eq/=.
    rewrite left_id //.
  - rewrite left_id.
    destruct (mcrename_keys μ μ' (x i ⋅ x' i) !! γ) as [w|] eqn:Heqw; last done.
    apply in_mcrename_keys in Heqw as (ξ & ? & Hξ).
    eapply not_in_mcrename_keys in Heqm; last done.
    eapply not_in_mcrename_keys in Heqm'; last done.
    rewrite lookup_op Heqm Heqm' in Hξ; done.
Qed.

Lemma mcrename_iResUR_mono {Σ} μ μ' n (x x' : iResUR Σ) :
  x ≼{n} x' → mcrename_iResUR μ μ' x ≼{n} mcrename_iResUR μ μ' x'.
Proof.
  intros [z Hincl].
  exists (mcrename_iResUR μ μ' z).
  rewrite -mcrename_iResUR_mul Hincl //.
Qed.

Program Definition rename_mc {Σ} μ μ' (P : iProp Σ) : iProp Σ :=
  UPred _ (λ n x, uPred_holds P n (mcrename_iResUR μ μ' x)) _.
Next Obligation.
Proof.
  intros Σ μ μ' P n1 n2 x1 x2 HP Hxs Hns; simpl in *.
  eapply uPred_mono; [eassumption| |done].
  apply mcrename_iResUR_mono; done.
Qed.
Fail Next Obligation.

Lemma mcrename_iResUR_valid {Σ} μ ν n (x : iResUR Σ) :
  ✓{n} x → ✓{n} mcrename_iResUR μ ν x.
Proof.
  intros Hvl i γ.
  destruct (mcrename_keys μ ν (x i) !! γ) as [m|] eqn:Heqm;
    rewrite Heqm; last done.
  apply in_mcrename_keys in Heqm as (δ & ? & Hδ).
  specialize (Hvl i δ); rewrite Hδ in Hvl; done.
Qed.

Lemma mcrename_iResUR_in_fresh_mcname {Σ} μ ν n (x : iResUR Σ) f :
  ν ∉ (mcnames_of_iResUR (x ⋅? f)) →
  ✓{n} (x ⋅? f) →
  ✓{n} (mcrename_iResUR μ ν x ⋅? f).
Proof.
  intros Hfresh Hvl i γ.
  destruct f as [f|]; last by apply mcrename_iResUR_valid.
  simpl in *.
  rewrite discrete_fun_lookup_op.
  destruct ((mcrename_keys μ ν (x i) ⋅ f i) !! γ) as [m|] eqn:Heqm;
    rewrite Heqm; last done.
  rewrite lookup_op in Heqm.
  destruct (mcrename_keys μ ν (x i) !! γ) as [w|] eqn:Heqw;
    rewrite Heqw in Heqm; last first.
  { rewrite left_id in Heqm.
    specialize (Hvl i γ).
    rewrite discrete_fun_lookup_op lookup_op Heqm in Hvl.
    apply cmra_validN_op_r in Hvl; done. }
  apply in_mcrename_keys in Heqw as (δ & Hγ & Hδ).
  assert (f i !! γ = None) as Hfiγ.
  { apply (not_elem_of_dom (f i)).
    pose proof (mcnames_of_iResUR_include_dom (x ⋅ f) i) as Hdom.
    rewrite discrete_fun_lookup_op dom_op mcnames_of_union in Hdom.
    assert (ν ∉ mcnames_of (dom (f i))) as Hν by set_solver.
    intros ?; apply Hν.
    apply elem_of_mcnames_of.
    exists γ; split; last done.
    apply mcrename_spec in Hγ as (?&?&?&->).
    apply mcname_of_push_mcname. }
    rewrite Hfiγ right_id in Heqm; simplify_eq.
    apply cmra_validN_op_l in Hvl.
    specialize (Hvl i δ).
    rewrite Hδ in Hvl; done.
Qed.

(*  ownership *)

Local Definition mcown_def `{!inG Σ A} (μ : mcname) (γ : gname) (a : A) : iProp Σ :=
  own (push_mcname μ γ) a.
Local Definition mcown_aux : seal (@mcown_def). Proof. by eexists. Qed.
Definition mcown := mcown_aux.(unseal).
Global Arguments mcown {Σ A _} μ γ a.
Local Definition mcown_eq : @mcown = @mcown_def := mcown_aux.(seal_eq).
Local Instance: Params (@mcown) 5 := {}.

(** * Properties about ghost ownership *)
Section global.
Context `{i : !inG Σ A}.
Implicit Types a : A.

(** ** Properties of [own] *)
Global Instance mcown_ne μ γ : NonExpansive (@mcown Σ A _ μ γ).
Proof. rewrite !mcown_eq. solve_proper. Qed.
Global Instance mcown_proper μ γ :
  Proper ((≡) ==> (⊣⊢)) (@mcown Σ A _ μ γ) := ne_proper _.

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

(** ** Allocation *)
(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
  assertion. However, the map_updateP_alloc does not suffice to show this. *)
  Lemma own_alloc_strong_dep (f : gname → A) (P : gname → Prop) :
  pred_infinite P →
  (∀ γ, P γ → ✓ (f γ)) →
  ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ (f γ).
Proof.
  intros HPinf Hf.
  rewrite -(bupd_mono (∃ m, ⌜∃ γ, P γ ∧ m = own.iRes_singleton γ (f γ)⌝ ∧ uPred_ownM m)%I).
  - rewrite /bi_emp_valid (ownM_unit emp).
    apply bupd_ownM_updateP, (discrete_fun_singleton_updateP_empty _ (λ m, ∃ γ,
      m = {[ γ := own.inG_unfold (cmra_transport inG_prf (f γ)) ]} ∧ P γ));
      [|naive_solver].
    apply (alloc_updateP_strong_dep _ P _ (λ γ,
      own.inG_unfold (cmra_transport inG_prf (f γ)))); [done| |naive_solver].
    intros γ _ ?.
    by apply (cmra_morphism_valid own.inG_unfold), cmra_transport_valid, Hf.
  - apply exist_elim=>m; apply pure_elim_l=>-[γ [Hfresh ->]].
    by rewrite !own.own_eq /own.own_def -(exist_intro γ) pure_True // left_id.
Qed.

End global.

Definition cmra_omniscient_updateP {A : cmra} (x : A) mz P := ∀ n,
  ✓{n} (x ⋅? mz) → ∃ y, P y ∧ ✓{n} (y ⋅? mz).
Global Instance: Params (@cmra_omniscient_updateP) 1 := {}.
Notation "x '~~>o{' mz }: P" := (cmra_omniscient_updateP x mz P)
  (at level 70, format "x  '~~>o{' mz }:  P").

Lemma cmra_omniscient_updateP_updateP {A : cmra} (x : A) (P : A → Prop) :
  (∀ mz, x ~~>o{ mz }: P) → x ~~>: P.
Proof. rewrite /cmra_updateP /cmra_omniscient_updateP; firstorder. Qed.

Lemma cmra_omniscient_updateP_exists {A : cmra} {B} (x : A) (b : B) (P : B → A → Prop) mz :
  (x ~~>o{ mz }: (P b)) → x ~~>o{ mz }: (λ a, ∃ c : B, P c a).
Proof. rewrite /cmra_updateP /cmra_omniscient_updateP; firstorder. Qed.

Section ofe.
  Context {A : Type} `{Heqdec : !EqDecision A} {B : A → ucmra}.
  Implicit Types x : A.
  Implicit Types f g : discrete_fun B.
  
  Lemma discrete_fun_omniscient_updateP `{!Finite A} f h P Q :
    (∀ a, f a ~~>o{option_map (λ g, g a) h}: P a) →
    (∀ f', (∀ a, P a (f' a)) → Q f') →
    f ~~>o{h}: Q.
  Proof.
    intros F HP n Hv.
    destruct h as [h|].
    - destruct (finite_choice
        (λ a y, P a y ∧ ✓{n} (y ⋅ (h a)))) as [f' Hf']; first naive_solver.
      naive_solver.
    - destruct (finite_choice
      (λ a y, P a y ∧ ✓{n} y)) as [f' Hf']; first naive_solver.
      naive_solver.
  Qed.

End ofe.

Lemma new_microcosm `{!EqDecision A, !Countable A} (B : A → cmra)
  `{I : !∀ a, inG Σ (B a)} (f : ∀ a, B a) (gnames : gmap A gname) :
  (∀ a, ✓ (f a)) → ⊢ |==> ∃ μ, [∗ map] a ↦ γ ∈ gnames, mcown μ γ (f a).
Proof.

Solution: template microcosms ...

Lemma new_microcosm `{!EqDecision A, !Countable A} (B : A → cmra)
  `{I : !∀ a, inG Σ (B a)} (f : ∀ a, B a) (gnames : gmap A gname) :
  (∀ a, ✓ (f a)) → ⊢ |==> ∃ μ, [∗ map] a ↦ γ ∈ gnames, mcown μ γ (f a).
Proof.
  intros Hvld.
  rewrite -(bupd_mono (∃ m, ⌜∃ μ, m ≡ [^ (⋅) map] a ↦ γ ∈ gnames,
    own.iRes_singleton (push_mcname μ γ) (f a)⌝ ∧ uPred_ownM m)%I).
  - rewrite /bi_emp_valid (ownM_unit emp).
    apply bupd_ownM_updateP, cmra_omniscient_updateP_updateP; intros Fr.
    set (μ := from_option fresh_mcname 1%positive Fr).
    apply (cmra_omniscient_updateP_exists _ μ).
    apply (discrete_fun_omniscient_updateP _ _
      (λ i m,
        (∃ a γ (Heq : inG_id (I a) = i),
          gnames !! a = Some γ ∧
          m ≡ {[ push_mcname μ γ :=
          cmra_transport (f_equal (λ i, rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)) Heq)
          (own.inG_unfold (cmra_transport inG_prf (f a))) ]}) ∨
        (∀ a, a ∈ dom gnames → inG_id (I a) ≠ i))).
    + intros i ? Hvl.
      destruct (decide (∃ a γ, gnames !! a = Some γ ∧ inG_id (I a) = i)) as
        [(a & γ & Haγ & Heq)|Hnin].
      * eexists _; split.
        { left; eexists _, _, Heq; eauto. }
        intros γ'.
        destruct Fr; simpl in *.
        -- rewrite lookup_op.
            rewrite left_id in Hvl.
            destruct (decide (push_mcname μ γ = γ')) as [<-|].
            ++ rewrite lookup_singleton fresh_mcname_fresh right_id.
              apply cmra_transport_validN, own.inG_unfold_validN,
                cmra_transport_validN, cmra_valid_validN; done.
            ++ rewrite lookup_singleton_ne ?left_id; done.
        -- destruct (decide (push_mcname μ γ = γ')) as [<-|].
            ++ rewrite lookup_singleton.
              apply cmra_transport_validN, own.inG_unfold_validN,
                cmra_transport_validN, cmra_valid_validN; done.
            ++ rewrite lookup_singleton_ne ?left_id; done.
      * exists ε; split; last done.
        right. intros ?[? ?]%elem_of_dom ?; apply Hnin; eauto.
    + intros g Hg i.
      destruct (Hg i) as [(a & γ & Heq & Ha & Hgi)|Hg'].
      * Search "big_opM".
          
            
            
          cmra_transport_validN

        
    

    Locate cmra_updateP.
    eapply discrete_fun_updateP.
    




Lemma own_alloc_cofinite_dep (f : gname → A) (G : gset gname) :
  (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ (f γ).
Proof.
  intros Ha.
  apply (own_alloc_strong_dep f (λ γ, γ ∉ G))=> //.
  apply (pred_infinite_set (C:=gset gname)).
  intros E. set (γ := fresh (G ∪ E)).
  exists γ. apply not_elem_of_union, is_fresh.
Qed.
Lemma own_alloc_dep (f : gname → A) :
  (∀ γ, ✓ (f γ)) → ⊢ |==> ∃ γ, own γ (f γ).
Proof.
  intros Ha. rewrite /bi_emp_valid (own_alloc_cofinite_dep f ∅) //; [].
  apply bupd_mono, exist_mono=>?. apply: sep_elim_r.
Qed.

Lemma own_alloc_strong a (P : gname → Prop) :
  pred_infinite P →
  ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ a.
Proof. intros HP Ha. eapply (own_alloc_strong_dep (λ _, a)); eauto. Qed.
Lemma own_alloc_cofinite a (G : gset gname) :
  ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ a.
Proof. intros Ha. eapply (own_alloc_cofinite_dep (λ _, a)); eauto. Qed.
Lemma own_alloc a : ✓ a → ⊢ |==> ∃ γ, own γ a.
Proof. intros Ha. eapply (own_alloc_dep (λ _, a)); eauto. Qed.

(** ** Frame preserving updates *)
Lemma own_updateP P γ a : a ~~>: P → own γ a ⊢ |==> ∃ a', ⌜P a'⌝ ∗ own γ a'.
Proof.
  intros Hupd. rewrite !own_eq.
  rewrite -(bupd_mono (∃ m,
    ⌜ ∃ a', m = iRes_singleton γ a' ∧ P a' ⌝ ∧ uPred_ownM m)%I).
  - apply bupd_ownM_updateP, (discrete_fun_singleton_updateP _ (λ m, ∃ x,
      m = {[ γ := x ]} ∧ ∃ x',
      x = inG_unfold x' ∧ ∃ a',
      x' = cmra_transport inG_prf a' ∧ P a')); [|naive_solver].
    apply singleton_updateP', (iso_cmra_updateP' inG_fold).
    { apply inG_unfold_fold. }
    { apply (cmra_morphism_op _). }
    { apply inG_unfold_validN. }
    by apply cmra_transport_updateP'.
  - apply exist_elim=> m; apply pure_elim_l=> -[a' [-> HP]].
    rewrite -(exist_intro a'). rewrite -persistent_and_sep.
    by apply and_intro; [apply pure_intro|].
Qed.

Lemma own_update γ a a' : a ~~> a' → own γ a ⊢ |==> own γ a'.
Proof.
  intros. iIntros "?".
  iMod (own_updateP (a' =.) with "[$]") as (a'') "[-> $]".
  { by apply cmra_update_updateP. }
  done.
Qed.
Lemma own_update_2 γ a1 a2 a' :
  a1 ⋅ a2 ~~> a' → own γ a1 -∗ own γ a2 ==∗ own γ a'.
Proof. intros. apply entails_wand, wand_intro_r. rewrite -own_op. by iApply own_update. Qed.
Lemma own_update_3 γ a1 a2 a3 a' :
  a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 -∗ own γ a2 -∗ own γ a3 ==∗ own γ a'.
Proof. intros. apply entails_wand. do 2 apply wand_intro_r. rewrite -!own_op. by iApply own_update. Qed.
End global.

Global Arguments own_valid {_ _} [_] _ _.
Global Arguments own_valid_2 {_ _} [_] _ _ _.
Global Arguments own_valid_3 {_ _} [_] _ _ _ _.
Global Arguments own_valid_l {_ _} [_] _ _.
Global Arguments own_valid_r {_ _} [_] _ _.
Global Arguments own_updateP {_ _} [_] _ _ _ _.
Global Arguments own_update {_ _} [_] _ _ _ _.
Global Arguments own_update_2 {_ _} [_] _ _ _ _ _.
Global Arguments own_update_3 {_ _} [_] _ _ _ _ _ _.

Lemma own_unit A `{i : !inG Σ (A:ucmra)} γ : ⊢ |==> own γ (ε:A).
Proof.
  rewrite /bi_emp_valid (ownM_unit emp) !own_eq /own_def.
  apply bupd_ownM_update, discrete_fun_singleton_update_empty.
  apply (alloc_unit_singleton_update (inG_unfold (cmra_transport inG_prf ε))).
  - apply (cmra_morphism_valid _), cmra_transport_valid, ucmra_unit_valid.
  - intros x. rewrite -(inG_unfold_fold x) -(cmra_morphism_op inG_unfold).
    f_equiv. generalize (inG_fold x)=> x'.
    destruct inG_prf=> /=. by rewrite left_id.
  - done.
Qed.

(** Big op class instances *)
Section big_op_instances.
  Context `{!inG Σ (A:ucmra)}.

  Global Instance own_cmra_sep_homomorphism γ :
    WeakMonoidHomomorphism op uPred_sep (≡) (own γ).
  Proof. split; try apply _. apply own_op. Qed.

  Lemma big_opL_own {B} γ (f : nat → B → A) (l : list B) :
    l ≠ [] →
    own γ ([^op list] k↦x ∈ l, f k x) ⊣⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof. apply (big_opL_commute1 _). Qed.
  Lemma big_opM_own `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    m ≠ ∅ →
    own γ ([^op map] k↦x ∈ m, g k x) ⊣⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof. apply (big_opM_commute1 _). Qed.
  Lemma big_opS_own `{Countable B} γ (g : B → A) (X : gset B) :
    X ≠ ∅ →
    own γ ([^op set] x ∈ X, g x) ⊣⊢ [∗ set] x ∈ X, own γ (g x).
  Proof. apply (big_opS_commute1 _). Qed.
  Lemma big_opMS_own `{Countable B} γ (g : B → A) (X : gmultiset B) :
    X ≠ ∅ →
    own γ ([^op mset] x ∈ X, g x) ⊣⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof. apply (big_opMS_commute1 _). Qed.

  Global Instance own_cmra_sep_entails_homomorphism γ :
    MonoidHomomorphism op uPred_sep (⊢) (own γ).
  Proof.
    split; [split|]; try apply _.
    - intros. by rewrite own_op.
    - apply (affine _).
  Qed.

  Lemma big_opL_own_1 {B} γ (f : nat → B → A) (l : list B) :
    own γ ([^op list] k↦x ∈ l, f k x) ⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_own_1 `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    own γ ([^op map] k↦x ∈ m, g k x) ⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_own_1 `{Countable B} γ (g : B → A) (X : gset B) :
    own γ ([^op set] x ∈ X, g x) ⊢ [∗ set] x ∈ X, own γ (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_own_1 `{Countable B} γ (g : B → A) (X : gmultiset B) :
    own γ ([^op mset] x ∈ X, g x) ⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof. apply (big_opMS_commute _). Qed.
End big_op_instances.

(** Proofmode class instances *)
Section proofmode_instances.
  Context `{!inG Σ A}.
  Implicit Types a b : A.

  Global Instance into_sep_own γ a b1 b2 :
    IsOp a b1 b2 → IntoSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoSep (is_op a) own_op. Qed.
  Global Instance into_and_own p γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) own_op sep_and. Qed.

  Global Instance from_sep_own γ a b1 b2 :
    IsOp a b1 b2 → FromSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /FromSep -own_op -is_op. Qed.
  (* TODO: Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_own γ a b1 b2 :
    IsOp a b1 b2 → CombineSepAs (own γ b1) (own γ b2) (own γ a) | 60.
  Proof. intros. by rewrite /CombineSepAs -own_op -is_op. Qed.
  (* TODO: Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_own γ b1 b2 :
    CombineSepGives (own γ b1) (own γ b2) (✓ (b1 ⋅ b2)).
  Proof.
    intros. rewrite /CombineSepGives -own_op own_valid.
    by apply: bi.persistently_intro.
  Qed.
  Global Instance from_and_own_persistent γ a b1 b2 :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (own γ a) (own γ b1) (own γ b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) own_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed.
End proofmode_instances.

Section own_forall.
  Context `{i : !inG Σ A}.
  Implicit Types a c : A.
  Implicit Types x z : iResUR Σ.

  (** Our main goal in this section is to prove [own_forall]:

    (∀ b, own γ (f b)) ⊢ ∃ c : A, own γ c ∗ (∀ b, Some (f b) ≼ Some c)

  We have the analogue in the global ucmra, from [ownM_forall]:

    (∀ a, uPred_ownM (f a)) ⊢ ∃ z : iRes Σ, uPred_ownM z ∧ (∀ a, f a ≼ z)

  We need to relate [uPred_ownM (iRes_singleton γ _)] to [own γ _] so that we
  can bring this theorem from the global ucmra world to the [A] world.
  In particular, [ownM_forall] gives us some [z] in the ucmra world, but to prove
  the theorem in the end, we need to supply a witness [z'] in the [A] world.
  We start by defining the [iRes_project] function to map from the ucmra world
  to the [A] world, basically an inverse of [iRes_singleton]: *)

  Local Definition iRes_project (γ : gname) (x : iResUR Σ) : option A :=
    cmra_transport (eq_sym inG_prf) ∘ inG_fold <$> x (inG_id i) !! γ.

  (* Now we prove some properties about [iRes_project] *)
  Local Lemma iRes_project_op γ x y :
    iRes_project γ (x ⋅ y) ≡@{option A} iRes_project γ x ⋅ iRes_project γ y.
  Proof.
    rewrite /iRes_project lookup_op.
    case: (x (inG_id i) !! γ)=> [x1|]; case: (y (inG_id i) !! γ)=> [y1|] //=.
    rewrite -Some_op -cmra_transport_op. do 2 f_equiv. apply: cmra_morphism_op.
  Qed.

  Local Instance iRes_project_ne γ : NonExpansive (iRes_project γ).
  Proof. intros n x1 x2 Hx. rewrite /iRes_project. do 2 f_equiv. apply Hx. Qed.

  Local Lemma iRes_project_singleton γ a :
    iRes_project γ (iRes_singleton γ a) ≡ Some a.
  Proof.
    rewrite /iRes_project /iRes_singleton discrete_fun_lookup_singleton.
    rewrite lookup_singleton /= inG_fold_unfold.
    by rewrite cmra_transport_trans eq_trans_sym_inv_r.
  Qed.

  (** The singleton result [c] of [iRes_project γ z] is below [z] *)
  Local Lemma iRes_project_below γ z c :
    iRes_project γ z = Some c → iRes_singleton γ c ≼ z.
  Proof.
    rewrite /iRes_project /iRes_singleton fmap_Some.
    intros (a' & Hγ & ->). rewrite cmra_transport_trans eq_trans_sym_inv_l /=.
    exists (discrete_fun_insert (inG_id i) (delete γ (z (inG_id i))) z).
    intros j. rewrite discrete_fun_lookup_op.
    destruct (decide (j = inG_id i)) as [->|]; last first.
    { rewrite discrete_fun_lookup_singleton_ne //.
      rewrite discrete_fun_lookup_insert_ne //. by rewrite left_id. }
    rewrite discrete_fun_lookup_singleton discrete_fun_lookup_insert.
    intros γ'. rewrite lookup_op. destruct (decide (γ' = γ)) as [->|].
    - by rewrite lookup_singleton lookup_delete Hγ inG_unfold_fold.
    - by rewrite lookup_singleton_ne // lookup_delete_ne // left_id.
  Qed.

  (** If another singleton [c] is below [z], [iRes_project] is above [c]. *)
  Local Lemma iRes_project_above γ z c :
    iRes_singleton γ c ≼ z ⊢@{iProp Σ} Some c ≼ iRes_project γ z.
  Proof.
    iIntros "#[%x Hincl]". iExists (iRes_project γ x).
    rewrite -(iRes_project_singleton γ) -iRes_project_op.
    by iRewrite "Hincl".
  Qed.

  (** Finally we tie it all together.
  As usual, we use [Some a ≼ Some c] for the reflexive closure of [a ≼ c]. *)
  Lemma own_forall `{!Inhabited B} γ (f : B → A) :
    (∀ b, own γ (f b)) ⊢ ∃ c, own γ c ∗ (∀ b, Some (f b) ≼ Some c).
  Proof.
    rewrite own_eq /own_def. iIntros "Hown".
    iDestruct (ownM_forall with "Hown") as (z) "[Hown Hincl]".
    destruct (iRes_project γ z) as [c|] eqn:Hc.
    - iExists c. iSplitL "Hown".
      { iApply (ownM_mono with "Hown"). by apply iRes_project_below. }
      iIntros (b). rewrite -Hc. by iApply iRes_project_above.
    - iDestruct ("Hincl" $! inhabitant) as "Hincl".
      iDestruct (iRes_project_above with "Hincl") as "Hincl".
      rewrite Hc. iDestruct "Hincl" as (mx) "H".
      rewrite option_equivI. by destruct mx.
  Qed.

  (** Now some corollaries. *)
  Lemma own_forall_total `{!CmraTotal A, !Inhabited B} γ (f : B → A) :
    (∀ b, own γ (f b)) ⊢ ∃ c, own γ c ∗ (∀ b, f b ≼ c).
  Proof. setoid_rewrite <-Some_included_totalI. apply own_forall. Qed.

  Lemma own_and γ a1 a2 :
    own γ a1 ∧ own γ a2 ⊢ ∃ c, own γ c ∗ Some a1 ≼ Some c ∗ Some a2 ≼ Some c.
  Proof.
    iIntros "Hown". iDestruct (own_forall γ (λ b, if b : bool then a1 else a2)
      with "[Hown]") as (c) "[$ Hincl]".
    { rewrite and_alt.
      iIntros ([]); [iApply ("Hown" $! true)|iApply ("Hown" $! false)]. }
    iSplit; [iApply ("Hincl" $! true)|iApply ("Hincl" $! false)].
  Qed.
  Lemma own_and_total `{!CmraTotal A} γ a1 a2 :
    own γ a1 ∧ own γ a2 ⊢ ∃ c, own γ c ∗ a1 ≼ c ∗ a2 ≼ c.
  Proof. setoid_rewrite <-Some_included_totalI. apply own_and. Qed.

  (** A version of [own_forall] for bounded quantification. Here [φ : B → Prop]
  is a pure predicate that restricts the elements of [B]. *)
  Lemma own_forall_pred {B} γ (φ : B → Prop) (f : B → A) :
    (∃ b, φ b) → (* [φ] is non-empty *)
    (∀ b, ⌜ φ b ⌝ -∗ own γ (f b)) ⊢
    ∃ c, own γ c ∗ (∀ b, ⌜ φ b ⌝ -∗ Some (f b) ≼ Some c).
  Proof.
    iIntros ([b0 pb0]) "Hown".
    iAssert (∀ b : { b | φ b }, own γ (f (`b)))%I with "[Hown]" as "Hown".
    { iIntros ([b pb]). by iApply ("Hown" $! b). }
    iDestruct (@own_forall _ with "Hown") as (c) "[$ Hincl]".
    { split. apply (b0 ↾ pb0). }
    iIntros (b pb). iApply ("Hincl" $! (b ↾ pb)).
  Qed.
  Lemma own_forall_pred_total `{!CmraTotal A} {B} γ (φ : B → Prop) (f : B → A) :
    (∃ b, φ b) →
    (∀ b, ⌜ φ b ⌝ -∗ own γ (f b)) ⊢ ∃ c, own γ c ∗ (∀ b, ⌜ φ b ⌝ -∗ f b ≼ c).
  Proof. setoid_rewrite <-Some_included_totalI. apply own_forall_pred. Qed.

  Lemma own_and_discrete_total `{!CmraDiscrete A, !CmraTotal A} γ a1 a2 c :
    (∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → c ≼ c') →
    own γ a1 ∧ own γ a2 ⊢ own γ c.
  Proof.
    iIntros (Hvalid) "Hown".
    iDestruct (own_and_total with "Hown") as (c') "[Hown [%Ha1 %Ha2]]".
    iDestruct (own_valid with "Hown") as %?.
    iApply (own_mono with "Hown"); eauto.
  Qed.
  Lemma own_and_discrete_total_False `{!CmraDiscrete A, !CmraTotal A} γ a1 a2 :
    (∀ c', ✓ c' → a1 ≼ c' → a2 ≼ c' → False) →
    own γ a1 ∧ own γ a2 ⊢ False.
  Proof.
    iIntros (Hvalid) "Hown".
    iDestruct (own_and_total with "Hown") as (c) "[Hown [%Ha1 %Ha2]]".
    iDestruct (own_valid with "Hown") as %?; eauto.
  Qed.
End own_forall.
  