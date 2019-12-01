Require Import Reals.
Open Scope R_scope.

(** 加入前提的*)

Lemma  not_exist : forall (p1 p2:R->Prop), (~ exists x, p1 x /\ p2 x) -> (forall x, p1 x -> ~ p2 x).
Proof.
  intros.
  unfold not; intro.
  destruct H; exists x; auto.
Qed.


Lemma total_eq_or_neq : forall r1 r2:R, r1=r2 \/ r1<>r2.
Proof.
  intros.
  generalize (total_order_T r1 r2); intros.
  destruct H. destruct s; auto.
  apply Rlt_not_eq in r; auto.
  apply Rgt_not_eq in r; auto.
Qed.

Lemma Rmult_par_inv_eq :
  forall r r1:R, r<>0 -> r * (r1 /r) = r*r1/r.
Proof.
  intros; unfold Rdiv.
  rewrite Rmult_assoc; auto.
Qed.

 
Lemma Rmult_eq_r :
  forall r r1:R, r<>0 -> r * r1 /r = r1.
Proof.
  intros.
  unfold Rdiv.
  rewrite Rinv_r_simpl_m; auto.
Qed.

Lemma Rmult_0_lt_reg : forall r1 r2:R, 0<r2 -> 0<r1*r2 -> 0<r1.
Proof.
  intros.
  apply Rmult_lt_reg_r with (r:=r2); auto; rewrite Rmult_0_l; auto.
Qed.


Lemma Rmult_le_r :
  forall r r1 r2 r3:R, 0 < r -> r1 * r <= r2 * r <= r3 * r -> r1 <= r2 <= r3.
Proof.
  intros.
  destruct H0.
  split; apply Rmult_le_reg_r with (r:=r); auto.
Qed.

Lemma Rinv_le_r :
  forall r r1 r2 r3:R, 0 < r -> r1 <= r2 <= r3 <-> r1/r <= r2/r <= r3/r.
Proof. 
  intros; unfold Rdiv.
  split; intro.
  assert(/r>=0). { apply Rgt_ge. apply Rinv_0_lt_compat; auto. }
  - destruct H0.
    split; apply Rmult_le_compat_r; auto; apply Rge_le; auto.
  - apply Rmult_le_r with (r:=/r); auto.
    apply Rinv_0_lt_compat; auto.
Qed.

Lemma Rminus_plus_r : forall r r1:R, r1-r+r=r1.
Proof.
  intros.
  unfold Rminus; rewrite Rplus_assoc.
  rewrite Rplus_opp_l; rewrite Rplus_0_r; auto.
Qed.

Lemma Rplus_le_3_r:
  forall r r1 r2 r3 : R, r1 <= r2 + r <= r3 <-> r1 - r <= r2 <= r3 - r.
Proof.
  intros.
  split; intros.
  - destruct H; split.  
    apply Rplus_le_reg_r with (r:=r).
    rewrite Rminus_plus_r; auto.
    apply Rplus_le_reg_r with (r:=r).
    rewrite Rminus_plus_r; auto.
  - destruct H; split.
    apply Rplus_le_compat_r with (r:=r) in H.
    rewrite Rminus_plus_r in H; auto.
    apply Rplus_le_compat_r with (r:=r) in H0.
    rewrite Rminus_plus_r in H0; auto.
Qed.

Lemma Rlt_x_le :
  forall r r1 r2:R, r>0 -> 0<r1/r<=r2/r -> 0<r1<=r2.
Proof.
  unfold Rdiv; intros.
  assert(/r>0). { apply Rinv_0_lt_compat; auto. }
  destruct H0; split.
  apply Rmult_lt_reg_r with (r:= /r); auto.
  rewrite Rmult_0_l; auto.
  eapply Rmult_le_reg_r. apply H1. apply H2.
Qed.

Lemma Rmult_minus_distr_1_3:
  forall r r1 r2 r3 : R, r * (r1 - r2 - r3) = r * r1 - r * r2 -r * r3.
Proof.
  intros.
  unfold Rminus.
  repeat rewrite Ropp_mult_distr_r.
  rewrite <- Rmult_plus_distr_l with (r1:=r)(r2:=r1)(r3:=- r2).
  rewrite <- Rmult_plus_distr_l with (r1:=r)(r2:=(r1 + - r2))(r3:=- r3); auto.
Qed.

Lemma Rle_abcd : forall a b c d:R, a<=b -> c<=d -> b<=c -> a<=d.
Proof.
  intros.
  assert(a<=c). { eapply Rle_trans. apply H. auto. }
  eapply Rle_trans. apply H2. auto.
Qed.

Lemma Rinv_minus_distr_r:
  forall r1 r2 r3 : R, r3 <> 0 -> (r1 - r2)/r3 = r1/r3 - r2/r3.
Proof.
  intros.
  unfold Rdiv. unfold Rminus.
  rewrite <- Ropp_mult_distr_l_reverse.
  rewrite Rmult_plus_distr_r. auto.
Qed.

Lemma plus_ab_minus_cd : forall a b c d e f:R, (a+b)-(c+d)-(e+f) = (a-c-e)+(b-d-f).
Proof.
 intros; ring.
Qed.

Lemma Rlt_x_le_reg :
  forall r r1 r2:R, r>0 -> 0<r1<=r2 -> 0<r1/r<=r2/r .
Proof.
  unfold Rdiv; intros.
  destruct H0; split.
  apply Rmult_lt_0_compat; auto.
  apply Rinv_0_lt_compat; auto.
  apply Rmult_le_compat_r; auto.
  apply Rlt_le; apply Rinv_0_lt_compat; auto.
Qed.

Lemma Rminus_distr : forall r1 r2 r3:R, r1-(r2-r3) = r1-r2+r3.
Proof.
  intros; ring.
Qed.
Lemma R_distr : forall r1 r2 r3:R, r1-r2+r3=r1+r3-r2.
Proof.
  intros; ring.
Qed.

Lemma Rgt_mult : forall r r1 r2, r>0 -> r1*r>r2->r1>r2/r.
Proof.
  intros.
  apply Rmult_gt_compat_r with (r:=/r)(r1:=r1*r) in H0. 
  rewrite Rinv_r_simpl_l with (r1:=r)in H0; unfold Rdiv; auto.
  apply Rgt_not_eq in H; auto.
  apply Rinv_0_lt_compat; auto.
Qed.


Lemma Rlt_mult : forall r r1 r2, r>0 -> r1*r<r2->r1<r2/r.
Proof.
  intros.
  apply Rmult_lt_compat_r with (r:=/r)(r1:=r1*r) in H0. 
  rewrite Rinv_r_simpl_l with (r1:=r)in H0; unfold Rdiv; auto.
  apply Rgt_not_eq in H; auto.
  apply Rinv_0_lt_compat; auto.
Qed.

Lemma Rinv_mult_rgt0 :forall r r1, r>0 -> r1*/r*r=r1.
Proof.
  intros.
  rewrite Rmult_assoc; rewrite Rinv_l. 
  rewrite Rmult_1_r; auto.
  apply Rgt_not_eq in H; auto.
Qed.

Lemma Rlt_inv : forall r1 r2, r1>0 -> r2>0 -> r1</r2-> r2</r1.
Proof.
  intros.
  apply Rmult_lt_reg_r with (r:=/r2); try apply Rinv_0_lt_compat; auto.
  apply Rmult_lt_reg_l with (r:=r1); try apply Rinv_0_lt_compat; auto.
  rewrite Rinv_r; try rewrite Rmult_1_r.
  rewrite <- Rmult_assoc; rewrite Rinv_r; try rewrite Rmult_1_l; auto.
  apply Rgt_not_eq; auto.
  apply Rgt_not_eq; auto.
Qed.

Lemma Rinv_le : forall r1 r2, r1>0 -> r2>0 -> /r1<=r2-> r1>=/r2.
Proof.
  intros.
  apply Rle_ge.
  apply Rmult_le_reg_r with (r:=/r1); try apply Rinv_0_lt_compat; auto.
  apply Rmult_le_reg_l with (r:=r2); try apply Rinv_0_lt_compat; auto.
  rewrite Rinv_r; try rewrite Rmult_1_r.
  rewrite <- Rmult_assoc; rewrite Rinv_r; try rewrite Rmult_1_l; auto.
  apply Rgt_not_eq; auto.
  apply Rgt_not_eq; auto.
Qed.

Lemma Rminus_Rabs : forall a b c d r1 r2,
  a<=r1<=b -> c<=r2<=d -> Rabs(r2 - r1) <= Rabs(d - a) \/ Rabs(r2 - r1) <= Rabs(c - b).
Proof.
  intros.
  destruct H, H0.
  assert(r2-r1<=d-a).
   { unfold Rminus.
     apply Ropp_le_contravar in H.
     apply Rplus_le_compat; auto. }
  assert(c-b<=r2-r1).
    { unfold Rminus.
     apply Ropp_le_contravar in H1.
     apply Rplus_le_compat; auto. }
  generalize (total_order_T (r2-r1) 0); intro.
  destruct H5.
  - destruct s.
    + generalize Rle_lt_trans; intro.
      generalize H4; intro.
      apply H5 with (r3:=0) in H4; auto. clear H5.
      right; repeat rewrite Rabs_left; auto.
      apply Ropp_le_contravar; auto.
    + left; repeat rewrite e.
      rewrite Rabs_R0; apply Rabs_pos.
  - generalize Rge_gt_trans; intro.
    generalize r;intro.
    apply H5 with(r1:=d-a) in r.
    left; repeat rewrite Rabs_right; auto.
    apply Rgt_ge; auto.
    apply Rgt_ge; auto.
    apply Rle_ge; auto.
Qed.