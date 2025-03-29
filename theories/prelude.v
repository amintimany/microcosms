From stdpp Require Export options prelude numbers.
From Stdlib.ssr Require Export ssreflect.

(* Some helper lemmas; consider up-streaming some of them. *)

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