From microcosms Require Import prelude.

Lemma div_lt (n k : nat) : k > 1 → n ≠ 0 → n `div` k < n.
Proof.
  rewrite /Nat.div. destruct k; simpl; first lia.
  intros Hk Hn.
  pose proof (Nat.divmod_spec n k 0 k) as Hs.
  destruct Nat.divmod as [l w]; simpl in *.
  destruct Hs; first lia.
  destruct l; lia.
Qed.

Lemma div_in_div n k l : k > 0 → l > 0 → n `mod` (l * k) = 0 → l * n `div` (l * k) = n `div` k.
Proof.
  intros Hk Hl Hmod.
  pose proof (Nat.div_mod n (l * k)) as Hrml.
  rewrite Hmod Nat.add_0_r in Hrml.
  pose proof (Nat.div_mod n k) as Hrm.
  assert (n `mod` k = 0) as Hrm0.
  { rewrite {2}Hrml in Hrm; last lia.
    replace (l * k * n `div` (l * k)) with ((l * n `div` (l * k)) * k) in Hrm by lia.
    rewrite Nat.div_mul in Hrm; lia. }
  rewrite Hrm0 Nat.add_0_r in Hrm.
  rewrite {1}Hrml in Hrm; last lia.
  assert (k * (l * n `div` (l * k)) = k * n `div` k) as Hrm' by lia.
  rewrite Nat.mul_cancel_l in Hrm'; lia.
Qed.

Lemma mod_by_mul_zero a b c : b * c ≠ 0 → a `mod` (b * c) = 0 → a `mod` b = 0.
Proof.
  intros Hbc Hmod.
  pose proof (Nat.div_mod a (b * c)) as Hrs.
  rewrite Hmod Nat.add_0_r in Hrs.
  pose proof (Nat.div_mod a b) as Hrs'.
  rewrite -Nat.mul_assoc (Nat.mul_comm b c) in Hrs.
  rewrite div_in_div in Hrs; solve [lia||rewrite -(Nat.mul_comm b c); done].
Qed.

Fixpoint log_aux (n : nat) (k : nat) (Hk : k > 1) (wf : Acc lt n) : nat :=
  match decide (n = 0) with
  | left _ => 0
  | right nz =>
    if bool_decide (n `mod` k = 0) then
      S (log_aux (n `div` k) k Hk (Acc_inv wf (div_lt n k Hk nz)))
    else
      0
  end.

Lemma log_aux_irrel (n : nat) (k : nat) (Hk : k > 1) (wf wf' : Acc lt n) :
  log_aux n k Hk wf = log_aux n k Hk wf'.
Proof.
  induction (lt_wf n) as [n _ IHn].
  destruct wf as [ac]; destruct wf' as [ac']; simpl.
  destruct decide; first done.
  erewrite (λ H, IHn _ H (ac _ _)); first eauto.
  apply div_lt; done.
Qed.

Definition log (n : nat) (k : nat) (Hk : k > 1) := log_aux n k Hk (lt_wf n).

Lemma log_unfold n k Hk :
  log n k Hk =
  match n with
  | 0 => 0
  | _ => if bool_decide (n `mod` k = 0) then S (log (n `div` k) k Hk) else 0
  end.
Proof.
  induction (lt_wf n) as [n _ IHn].
  destruct n as [|n].
  - rewrite {1}/log.
    destruct lt_wf; simpl; done.
  - rewrite {1}/log.
    destruct lt_wf as [ac]; simpl.
    destruct bool_decide; last done.
    f_equal.
    rewrite (log_aux_irrel _ k Hk (ac _ _) (lt_wf _)); done.
Qed.

Lemma log_spec n k Hk l :
  n > 0 → log n k Hk = l → n `mod` (k ^ l) = 0 ∧ n `mod` (k ^ (S l)) ≠ 0.
Proof.
  revert l.
  induction (lt_wf n) as [n _ IHn]; intros l Hn Hl.
  rewrite log_unfold in Hl.
  destruct n as [|n]; first lia.
  rewrite -decide_bool_decide in Hl.
  destruct decide as [Heq|]; last first.
  { simplify_eq/=.
    replace (k * 1) with k by lia.
    split; last done.
    pose proof (Nat.div_mod (S n) 1) as Hrm.
    rewrite Nat.div_1_r in Hrm. lia. }
  destruct l; first done.
  simplify_eq/=.
  pose proof (Nat.div_mod (S n) k) as Hrm.
  rewrite Heq in Hrm.
  rewrite Nat.add_0_r in Hrm.
  rewrite {1 3}Hrm; last lia.
  assert (k ^ log (S n `div` k) k Hk > 0).
  { pose proof (Nat.pow_nonzero k (log (S n `div` k) k Hk)). lia. }
  rewrite !Nat.Div0.mul_mod_distr_l.
  destruct (λ H, IHn (S n `div` k) H (log (S n `div` k) k Hk)); [|lia..].
  apply div_lt; done.
Qed.

Lemma log_spec_alt n k Hk l : n > 0 → n `mod` (k ^ l) = 0 ↔ l ≤ log n k Hk.
Proof.
  intros Hn.
  pose proof (log_spec _ _ Hk _ Hn eq_refl) as [Hp1 Hp2].
  split.
  - intros Hkl.
    pose proof (Nat.div_mod n (k ^ log n k Hk)) as Hmod.
    rewrite Hp1 Nat.add_0_r in Hmod.
    destruct (decide (l ≤ log n k Hk)); first done.
    replace l with (log n k Hk + (l - log n k Hk)) in Hkl by lia.
    rewrite Nat.pow_add_r in Hkl.
    assert (k ^ log n k Hk ≠ 0).
    { pose proof (Nat.pow_nonzero k (log n k Hk)). lia. }
    rewrite {1}Hmod //= (Nat.mul_comm k) in Hp2.
    rewrite {1}Hmod // in Hkl.
    rewrite Nat.Div0.mul_mod_distr_l in Hkl.
    rewrite Nat.Div0.mul_mod_distr_l in Hp2.
    destruct (l - log n k Hk) as [|z] eqn:Hz; first lia.
    simpl in Hkl.
    assert ((n `div` k ^ log n k Hk) `mod` k = 0); last lia.
    assert (k ^ z > 0).
    { pose proof (Nat.pow_nonzero k z). lia. }
    apply (mod_by_mul_zero _ _ (k ^ z)); lia.
  - intros Hl.
    replace (log n k Hk) with (l + (log n k Hk - l)) in Hp1 by lia.
    rewrite Nat.pow_add_r in Hp1.
    assert (k ^ l > 0).
    { pose proof (Nat.pow_nonzero k l). lia. }
    assert (k ^ (log n k Hk - l) > 0).
    { pose proof (Nat.pow_nonzero k (log n k Hk -l)). lia. }
    apply mod_by_mul_zero in Hp1; lia.
Qed.

Definition inject_nat_pair (n m : nat) : nat := (2 ^ n) * (3 ^ m).

Lemma inject_nat_pair_positive n m : inject_nat_pair n m > 0.
Proof.
  rewrite /inject_nat_pair.
  pose proof (Nat.pow_nonzero 2 n).
  pose proof (Nat.pow_nonzero 3 m).
  lia.
Qed.

Lemma inject_nat_pair_mod_left n m : (inject_nat_pair n m) `mod` (2 ^ n) = 0.
Proof.
  rewrite /inject_nat_pair.
  replace (2 ^ n) with (2 ^ n * 1) at 2 by lia.
  rewrite Nat.Div0.mul_mod_distr_l.
  rewrite Nat.mod_1_r; lia.
Qed.

Lemma inject_nat_pair_mod_right n m : (inject_nat_pair n m) `mod` (3 ^ m) = 0.
Proof.
  rewrite /inject_nat_pair.
  rewrite Nat.mul_comm.
  replace (3 ^ m) with (3 ^ m * 1) at 2 by lia.
  rewrite Nat.Div0.mul_mod_distr_l.
  rewrite Nat.mod_1_r; lia.
Qed.

Lemma pow3_mod2 n : (3 ^ n) `mod` 2 ≠ 0.
Proof.
  assert (3 ^ n `mod` 2 = 1); last lia.
  induction n as [|n IHn]; first done.
  replace (3 ^ (S n)) with (3 ^ n * 3) by by simpl; lia.
  rewrite Nat.Div0.mul_mod IHn //.
Qed.

Lemma pow2_mod3 n : (2 ^ n) `mod` 3 ≠ 0.
Proof.
  assert (2 ^ n `mod` 3 = 1 ∨ 2 ^ n `mod` 3 = 2); last lia.
  induction n as [|n IHn]; first by auto.
  replace (2 ^ (S n)) with (2 ^ n * 2) by by simpl; lia.
  rewrite Nat.Div0.mul_mod.
  destruct IHn as [->| ->]; simpl; auto.
Qed.

Lemma pnp_2g1 : 2 > 1. Proof. lia. Qed.
Lemma pnp_3g1 : 3 > 1. Proof. lia. Qed.

Lemma log2_inject_nat_pair n m : log (inject_nat_pair n m) 2 pnp_2g1 = n.
Proof.
  assert (n ≤ log (inject_nat_pair n m) 2 pnp_2g1) as Hle.
  { apply log_spec_alt; first apply inject_nat_pair_positive.
    apply inject_nat_pair_mod_left. }
  assert (¬ S n ≤ log (inject_nat_pair n m) 2 pnp_2g1); last lia.
  intros Hlt.
  apply log_spec_alt in Hlt; last by apply inject_nat_pair_positive.
  replace (2 ^ S n) with ((2 ^ n) * 2) in Hlt by by simpl; lia.
  rewrite /inject_nat_pair in Hlt.
  rewrite Nat.Div0.mul_mod_distr_l in Hlt.
  pose proof (Nat.pow_nonzero 2 n).
  pose proof (pow3_mod2 m).
  lia.
Qed.

Lemma log3_inject_nat_pair n m : log (inject_nat_pair n m) 3 pnp_3g1 = m.
Proof.
  assert (m ≤ log (inject_nat_pair n m) 3 pnp_3g1) as Hle.
  { apply log_spec_alt; first apply inject_nat_pair_positive.
    apply inject_nat_pair_mod_right. }
  assert (¬ S m ≤ log (inject_nat_pair n m) 3 pnp_3g1); last lia.
  intros Hlt.
  apply log_spec_alt in Hlt; last by apply inject_nat_pair_positive.
  replace (3 ^ S m) with ((3 ^ m) * 3) in Hlt by by simpl; lia.
  rewrite /inject_nat_pair in Hlt.
  rewrite (Nat.mul_comm (2 ^ n)) in Hlt.
  rewrite Nat.Div0.mul_mod_distr_l in Hlt.
  pose proof (Nat.pow_nonzero 3 m).
  pose proof (pow2_mod3 n).
  lia.
Qed.

Lemma inject_nat_pair_inj n m n' m' : inject_nat_pair n m = inject_nat_pair n' m' → n = n' ∧ m = m'.
Proof.
  intros Hnm.
  pose proof (log2_inject_nat_pair n m) as Hn.
  pose proof (log3_inject_nat_pair n m) as Hm.
  pose proof (log2_inject_nat_pair n' m') as Hn'.
  pose proof (log3_inject_nat_pair n' m') as Hm'.
  rewrite -Hnm in Hn'; rewrite -Hnm in Hm'; simplify_eq; auto.
Qed.

Definition project_nat_pair (k : nat) : option (nat * nat) :=
  let n := log k 2 pnp_2g1 in
  let m := log k 3 pnp_3g1 in
  if bool_decide (k = 2 ^ n * 3 ^ m) then Some (n, m) else None.

Lemma project_nat_pair_spec k n m :
  project_nat_pair k = Some (n, m) ↔ k = inject_nat_pair n m.
Proof.
  rewrite /project_nat_pair /inject_nat_pair.
  remember (log k 2 pnp_2g1) as n'.
  remember (log k 3 pnp_3g1) as m'.
  rewrite -decide_bool_decide.
  destruct decide as [Hn'm'|Hnot].
  - split; first by intros; simplify_eq.
    intros ->.
    apply inject_nat_pair_inj in Hn'm' as []; simplify_eq; done.
  - split; first done.
    intros Hk.
    replace k with (inject_nat_pair n m) in Heqn'.
    rewrite log2_inject_nat_pair in Heqn'.
    replace k with (inject_nat_pair n m) in Heqm'.
    rewrite log3_inject_nat_pair in Heqm'.
    subst; done.
Qed.

Lemma project_nat_pair_inj k k' n m :
  project_nat_pair k = Some (n, m) →
  project_nat_pair k' = Some (n, m) →
  k = k'.
Proof. intros ?%project_nat_pair_spec ?%project_nat_pair_spec; subst; done. Qed.

Lemma project_inject_nat_pair (n m : nat) :
  project_nat_pair (inject_nat_pair n m) = Some (n, m).
Proof. apply project_nat_pair_spec; done. Qed.


Definition inject_positive_pair (p q : positive) : positive :=
  Pos.of_nat (inject_nat_pair (Pos.to_nat p - 1) (Pos.to_nat q - 1)).

Definition project_positive_pair (k : positive) : option (positive * positive) :=
  option_map
    (λ nm : nat * nat, (Pos.of_nat (nm.1 + 1), Pos.of_nat (nm.2 + 1)))
    (project_nat_pair (Pos.to_nat k)).

Lemma project_inject_positive_pair p q : project_positive_pair (inject_positive_pair p q) = Some (p, q).
Proof.
  rewrite /inject_positive_pair /project_positive_pair.
  rewrite Nat2Pos.id; last first.
  { pose proof (inject_nat_pair_positive (Pos.to_nat p - 1) (Pos.to_nat q - 1)); lia. }
  rewrite project_inject_nat_pair /=.
  replace (Pos.to_nat p - 1 + 1) with (Pos.to_nat p) by lia.
  replace (Pos.to_nat q - 1 + 1) with (Pos.to_nat q) by lia.
  rewrite !Pos2Nat.id //.
Qed.

Lemma inject_positive_pair_inj p q p' q' :
  inject_positive_pair p q = inject_positive_pair p' q' → p = p' ∧ q = q'.
Proof.
  intros Heq.
  pose proof (f_equal project_positive_pair Heq) as Heq'.
  rewrite !project_inject_positive_pair in Heq'.
  simplify_eq; done.
Qed.

Lemma project_positive_pair_inj r r' p q :
  project_positive_pair r = Some (p, q) →
  project_positive_pair r' = Some (p, q) →
  r = r'.
Proof.
  rewrite /project_positive_pair; intros Hr Hr'.
  apply Pos2Nat.inj.
  destruct (project_nat_pair (Pos.to_nat r)) as [[s1 s2]|] eqn:Hs; last done.
  destruct (project_nat_pair (Pos.to_nat r')) as [[s1' s2']|] eqn:Hs'; last done.
  simplify_eq/=.
  repeat match goal with
  | Heq : _ |- _ => apply Nat2Pos.inj in Heq; [|lia|lia]
  end.
  assert (s1 = s1') by lia.
  assert (s2 = s2') by lia.
  subst.
  eapply project_nat_pair_inj; eauto.
Qed.