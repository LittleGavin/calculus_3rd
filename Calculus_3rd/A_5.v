Require Import A_4.
Require Import Classical.


(*微积分系统的基本定理*)


(* 定理4.1: 设F(x)在[a,b]上一致可导，其导数为f(x).
   若在[a,b]上恒有f(x)>=0, 则F(x)单调增；
   若在[a,b]上恒有f(x)<=0, 则F(x)单调减；
   不等式中等号不成立时，则F(x)严格单调增或严格单调减 *)

Theorem th5_1 : forall F f a b, derivative F f a b -> 
  ((forall x, x ∈ [a,b] -> f(x)>=0) -> mon_increasing F [a,b]) /\
  ((forall x, x ∈ [a,b] -> f(x)<=0) -> mon_decreasing F [a,b]) /\
  ((forall x, x ∈ [a,b] -> f(x)>0) -> strict_mon_increasing F [a,b]) /\
  ((forall x, x ∈ [a,b] -> f(x)<0) -> strict_mon_decreasing F [a,b]).
Proof.
  intros.
  apply th4_4 in H.
  destruct H.
  unfold diff_quo_median in H.
  repeat split; intros.
  - unfold mon_increasing; intros.
    generalize H2 as H3; intro.
    apply H in H2.
    destruct H3, H4.
    destruct H2, H2, H2, H6, H7.
    assert(x0 ∈ [a,b]).
     { unfold In; unfold cc.
       unfold In in H2, H3, H4; unfold cc in H2, H3, H4.
       destruct H2, H3, H4. split; auto.
       split.
       apply Rle_trans with (r2:=x); tauto.
       apply Rle_trans with (r2:=y); tauto. }
    apply H1 in H9.
    apply Rle_trans with (r1:=0) in H7.
    apply Rmult_le_compat_r with (r:= y-x) in H7.
    rewrite Rmult_0_l in H7.
    unfold Rdiv in H7; rewrite Rinv_mult_rgt0 in H7; auto.
    apply Rplus_le_reg_r with (r:=-F x). rewrite Rplus_opp_r; auto.
    apply Rlt_le; auto.
    apply Rge_le; auto.
  - unfold mon_decreasing; intros.
    generalize H2 as H3; intro.
    apply H in H2.
    destruct H3, H4.
    destruct H2, H2, H2, H6, H7.
    assert(x1 ∈ [a,b]).
     { unfold In; unfold cc.
       unfold In in H6, H3, H4; unfold cc in H6, H3, H4.
       destruct H6, H3, H4. split; auto.
       split.
       apply Rle_trans with (r2:=x); tauto.
       apply Rle_trans with (r2:=y); tauto. }
    apply H1 in H9.
    apply Rle_trans with (r3:=0) in H8; auto.
    apply Rmult_le_compat_r with (r:= y-x) in H8.
    rewrite Rmult_0_l in H8.
    unfold Rdiv in H8; rewrite Rinv_mult_rgt0 in H8; auto.
    apply Rle_ge; apply Rplus_le_reg_r with (r:=-F x).
    rewrite Rplus_opp_r; auto.
    apply Rlt_le; auto.
  - unfold strict_mon_increasing; intros.
    generalize H2 as H3; intro.
    apply H in H2.
    destruct H3, H4.
    destruct H2, H2, H2, H6, H7.
    assert(x0 ∈ [a,b]).
     { unfold In; unfold cc.
       unfold In in H2, H3, H4; unfold cc in H2, H3, H4.
       destruct H2, H3, H4. split; auto.
       split.
       apply Rle_trans with (r2:=x); tauto.
       apply Rle_trans with (r2:=y); tauto. }
    apply H1 in H9.
    apply Rlt_le_trans with (r1:=0) in H7; auto.
    apply Rmult_lt_compat_r with (r:= y-x) in H7; auto.
    rewrite Rmult_0_l in H7.
    unfold Rdiv in H7; rewrite Rinv_mult_rgt0 in H7; auto.
    apply Rplus_lt_reg_r with (r:=-F x). rewrite Rplus_opp_r; auto.
  - unfold strict_mon_decreasing; intros.
    generalize H2 as H3; intro.
    apply H in H2.
    destruct H3, H4.
    destruct H2, H2, H2, H6, H7.
    assert(x1 ∈ [a,b]).
     { unfold In; unfold cc.
       unfold In in H6, H3, H4; unfold cc in H6, H3, H4.
       destruct H6, H3, H4. split; auto.
       split.
       apply Rle_trans with (r2:=x); tauto.
       apply Rle_trans with (r2:=y); tauto. }
    apply H1 in H9.
    apply Rle_lt_trans with (r3:=0) in H8; auto.
    apply Rmult_lt_compat_r with (r:= y-x) in H8; auto.
    rewrite Rmult_0_l in H8.
    unfold Rdiv in H8; rewrite Rinv_mult_rgt0 in H8; auto.
    apply Rplus_lt_reg_r with (r:=-F x).
    rewrite Rplus_opp_r; auto.
Qed.

(* Parameter  definite_integral : (R->R)->R->R->R.

Axiom def_integral : forall F f a b , derivative F f a b ->
  forall u v, u ∈ [a,b] /\ v ∈ [a,b] -> definite_integral f u v = F v - F u.

(*定理4.2*)
Theorem th4_2 : forall F f a b , derivative F f a b ->
  integ_sys (definite_integral f) f a b.
Proof.
  intros.
  generalize H; intro.
  apply th4_4 in H.
  destruct H.
  apply th3_1_2 with(S:=(definite_integral f)) in H; try tauto.
  intros.
  apply def_integral with(a:=a)(b:=b); auto.
Qed.


Definition def_integral' (F: R->R) := fun u v => F v - F u.  *)
Theorem th5_2 : forall F f a b , derivative F f a b ->
  integ_sys (fun a b => F b - F a) f a b.
Proof.
  intros.
  apply th4_4 in H.
  destruct H.
  apply th4_1_2 with(S:=(fun a b => F b - F a)) in H; try tauto.
Qed.

Theorem th5_3 : forall G f a b, uniform_continuous f a b ->
  (exists (S: R->R->R), integ_sys' S f a b /\
  forall x, x ∈ [a,b] -> G(x) = S a x) ->
  derivative G f a b.
Proof.
  intros.
  destruct H0, H0. rename x into S.
  assert(diff_quo_median G f a b).
   { unfold diff_quo_median.
     intros.
     unfold integ_sys' in H0.
     destruct H0.
     unfold additivity' in H0.
     unfold median in H3.
     assert(a ∈ [a, b] /\ u ∈ [a, b] /\ v ∈ [a, b]).
      { split; try tauto.
        unfold In; unfold cc.
        destruct H2.
        unfold In in H2; unfold cc in H2; destruct H2.
        split; auto.
        split. apply Req_le; reflexivity.
        apply Rlt_le; auto. }
     apply H0 in H4.
     generalize (H1 u); intro.
     generalize (H1 v); intro.
     rewrite H5; try tauto. clear H5.
     rewrite H6; try tauto. clear H6.
     assert(v - u > 0) as gt_v_u . { tauto. }
     apply H3 in H2. destruct H2, H2, H2, H5.
     exists x,x0.
     split; auto. split; auto.
     apply Rmult_le_r with(r:=v-u); auto.
     rewrite Rplus_comm in H4; rewrite <- H4.
     unfold Rminus. rewrite Rplus_assoc.
     rewrite Rplus_opp_r; rewrite Rplus_0_r.
     unfold Rdiv. rewrite Rinv_mult_rgt0; auto. }
  apply th4_4.
  split; auto.
Qed.
